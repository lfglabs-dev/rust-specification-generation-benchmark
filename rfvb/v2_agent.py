"""RSGB v2 agent harness: specification design.

The agent sees the target crate (extracted Lean + Rust sources without tests),
an editable `Candidate.lean`, and a briefing that names the public API to
specify — but no property, no docstring of the expected answer, no hidden
gold specification. Tools:

  show_task, read_file, search      exploration (same as v1)
  test_spec   elaborate the candidate and run every `prop_*` on generated
              inputs against the real (executable) implementation; reports
              elaboration errors, untestable properties and counterexamples.
  submit      final submission (ends the run); graded by `rfvb.v2.grade`.
"""
from __future__ import annotations

import json
import re
import shutil
import tempfile
import time
from pathlib import Path

from . import ROOT
from .agent import AgentResult, Budget, Runner, SEARCH_SCOPES, strip_fences, truncate
from .transport import ChatConfig
from .v2 import CACHE, Target, compile_candidate, decl_names, policy, test_properties

AGENT_SEED = 31337
AGENT_N = 400

V2_TOOLS = [
    {"type": "function", "function": {
        "name": "show_task",
        "description": "Show the task briefing (API to specify, grading, rules, format).",
        "parameters": {"type": "object", "properties": {}}}},
    {"type": "function", "function": {
        "name": "read_file",
        "description": "Read a text file of the workspace (extracted Lean implementation, Rust sources under rust/, Candidate.lean, Prelude, or library sources under .lake/packages). Returns numbered lines.",
        "parameters": {"type": "object", "properties": {
            "path": {"type": "string"},
            "start_line": {"type": "integer"},
            "num_lines": {"type": "integer"}},
            "required": ["path"]}}},
    {"type": "function", "function": {
        "name": "search",
        "description": "Regex search (grep -E) in Lean sources. scope: workspace | aeneas | coremodels | mathlib | lean_core.",
        "parameters": {"type": "object", "properties": {
            "pattern": {"type": "string"},
            "scope": {"type": "string", "enum": list(SEARCH_SCOPES)}},
            "required": ["pattern", "scope"]}}},
    {"type": "function", "function": {
        "name": "eval_expr",
        "description": ("Evaluate Lean expressions against the real (executable) implementation, like a REPL. "
                        "`exprs` is a list of Lean terms, e.g. [\"permute.obfuscate 42#u64 7#u64\", \"(255#u8).val\"]; "
                        "the same imports and `open`s as Candidate.lean are in scope. Returns each value."),
        "parameters": {"type": "object", "properties": {"exprs": {"type": "array", "items": {"type": "string"}}},
                       "required": ["exprs"]}}},
    {"type": "function", "function": {
        "name": "test_spec",
        "description": ("Elaborate a complete Candidate.lean and run every `prop_*` property on generated inputs against the "
                        "real implementation. Returns Lean errors, untestable properties, and counterexamples for false "
                        "properties. Does not submit. `spec` must be the complete file content."),
        "parameters": {"type": "object", "properties": {"spec": {"type": "string"}}, "required": ["spec"]}}},
    {"type": "function", "function": {
        "name": "submit",
        "description": ("Submit the complete Candidate.lean as your final specification (ends the run). It is graded by "
                        "truth (every property must hold on thousands of hidden inputs; a single false property scores 0) "
                        "and strength (how many hidden buggy variants of the implementation your properties reject)."),
        "parameters": {"type": "object", "properties": {"spec": {"type": "string"}}, "required": ["spec"]}}},
]

PROMPT = (Path(__file__).resolve().parent / "prompts" / "PROMPT_V2.md")


def strip_tests(rust_dir: Path) -> None:
    """Remove property/unit tests so that the expected properties are not handed to the agent."""
    for p in list(rust_dir.rglob("*")):
        if p.is_dir() and p.name in ("tests", "benches", "fuzz", "proptest-regressions"):
            shutil.rmtree(p, ignore_errors=True)
    for p in rust_dir.rglob("*.rs"):
        text = p.read_text(encoding="utf-8", errors="replace")
        new = _strip_cfg_test(text)
        if new != text:
            p.write_text(new, encoding="utf-8")


def _strip_cfg_test(text: str) -> str:
    out, i = [], 0
    pat = re.compile(r"#\[cfg\(test\)\]\s*(?:#\[[^\]]*\]\s*)*(?:pub\s+)?mod\s+\w+\s*\{")
    while True:
        m = pat.search(text, i)
        if not m:
            out.append(text[i:])
            break
        out.append(text[i:m.start()])
        depth, j = 1, m.end()
        while j < len(text) and depth:
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
            j += 1
        out.append("// (tests removed)\n")
        i = j
    return "".join(out)


def api_listing(t: Target) -> str:
    funs = (ROOT / "extracted" / t.package / "Extraction" / "Funs.lean").read_text(encoding="utf-8")
    from .workspace import _decl_blocks
    blocks = dict(_decl_blocks(funs))
    out = []
    for name in t.api:
        b = blocks.get(name)
        if b is None:
            out.append(f"-- {name} (see extraction)")
            continue
        head = b.split(":=", 1)[0].rstrip()
        out.append(head)
    return "\n\n".join(out)


def template(t: Target) -> str:
    opens = " ".join(t.raw.get("opens", []))
    imports = "\n".join(f"import {m}" for m in t.allowed_imports)
    return f"""import Benchmark.V2.Prelude
{imports}

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM{(' ' + opens) if opens else ''}

namespace {t.cand_ns}

-- Write your specification here: one or more `def prop_<name> (inputs…) : Prop`.

end {t.cand_ns}
"""


def briefing(t: Target) -> str:
    forb = ", ".join(f"`{c}`" for c in t.raw.get("forbidden_constants", [])) or "(none)"
    return f"""# Task `{t.id}` — write a formal specification

{t.intent}

## Public API (Lean signatures of the extracted functions)
```lean
{api_listing(t)}
```

Implementation: `extracted/{t.package}/` (verbatim `hax`/Aeneas extraction of the Rust crate).
Rust sources (documentation, without the crate's tests): `{t.rust_dir}/`.
Editable file: `{t.candidate_file}` (namespace `{t.cand_ns}`).

## What to write
Any number of properties, each a definition

```lean
def prop_<name> (x₁ : T₁) … (xₙ : Tₙ) : Prop := …
```

Every property is read as `∀ x₁ … xₙ, prop_<name> x₁ … xₙ`. Express preconditions
inside the property (`pre → post`). Helper definitions (not starting with
`prop_`) are allowed. Do not use the private implementation functions {forb};
specify the behaviour through the public API.

## How the specification is graded
1. **Truth.** Every property is executed on thousands of generated inputs against
   the real implementation (Rust debug semantics: arithmetic overflow, out-of-bounds
   indexing and failed assertions panic, i.e. return `fail .panic`). If any property
   is false on any input, the whole specification scores **0**.
2. **Strength.** Your properties are run against many hidden *buggy variants* of the
   implementation (small code changes that break the intended behaviour). The score
   is the fraction of buggy variants that at least one property rejects. A strong
   specification pins down the complete intended behaviour of every API function —
   results, ranges, relations between the functions, edge cases, and exactly which
   inputs panic — not just one obvious property.

Use `eval_expr` to run the implementation on inputs of your choice (a REPL), and
`test_spec` to check that your properties elaborate, are executable, and hold on
the real implementation before you `submit` (one submission ends the run).

## Executability rules
- Inputs are sampled at random: Rust scalars (`Std.U8 … Std.U128`, `Std.Usize`,
  `Std.I8 … Std.I128`, `Std.Isize`; biased towards 0, 1, MAX, MIN, powers of two ± 1,
  log-uniform magnitudes), `Bool`, `List`, `Slice`, `alloc.vec.Vec`, `Std.Array`
  of those (short lengths), and tuples{t.raw.get('extra_types_note', '')}.
- The body of a property must be decidable by evaluation: `e ⦃ r => P r ⦄`,
  `e = ok v`, `e = fail .panic`, `=`, `≠`, `<`, `≤`, `∧`, `∨`, `¬`, `→`, `if`,
  bounded quantifiers (`∀ i < n, …`, `∀ x ∈ l, …`), and computable helper functions
  (prefer `Bool`-valued helpers or `Prop` helpers built from the above). Unbounded
  quantifiers inside a property are not executable.
- To restrict an input to a small range, use a smaller type and convert:
  `RSGB.mkU .U32 w.val` builds a `Std.U32` from a natural number (mod 2^32),
  `RSGB.mkI .I64 z` a signed scalar from an integer.
- Inputs that make the implementation loop for a very long time (e.g. a huge loop
  bound) must be excluded by a precondition, otherwise the property times out and
  is ignored.

## Semantics
`e ⦃ r => P r ⦄` holds iff the Rust computation `e` returns `ok r` (no panic, no
divergence) and `P r` holds. `.val` is the mathematical value (`Nat` for unsigned,
`Int` for signed scalars). Checked Rust operators on scalars (`+ - * / % <<< >>>`)
return `RustM`; do pure arithmetic on `.val`.
"""


def build_v2_workspace(t: Target, dst: Path) -> Path:
    if dst.exists():
        shutil.rmtree(dst)
    dst.mkdir(parents=True)
    for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain"):
        shutil.copy2(ROOT / name, dst / name)
    shutil.copytree(ROOT / "extracted" / t.package, dst / "extracted" / t.package)
    (dst / "Benchmark/V2").mkdir(parents=True)
    shutil.copy2(ROOT / "Benchmark/V2/Prelude.lean", dst / "Benchmark/V2/Prelude.lean")
    cand = dst / t.candidate_file
    cand.parent.mkdir(parents=True, exist_ok=True)
    cand.write_text(template(t), encoding="utf-8")
    shutil.copytree(ROOT / t.rust_dir, dst / t.rust_dir)
    strip_tests(dst / t.rust_dir)
    (dst / "TASK.md").write_text(briefing(t), encoding="utf-8")
    pk = dst / ".lake" / "packages"
    pk.parent.mkdir(parents=True, exist_ok=True)
    pk.symlink_to(ROOT / ".lake" / "packages")
    return dst


class V2Runner(Runner):
    def __init__(self, t: Target, ws: Path, cfg: ChatConfig, budget: Budget, art: Path):
        self.target = t
        self.task = t  # used by inherited helpers for names only
        self.ws, self.cfg, self.budget, self.art, self.root = ws, cfg, budget, art, ROOT
        from .transport import chat
        self.chat_fn = chat
        self.original = template(t)
        self.editable = ws / t.candidate_file
        (art / "attempts").mkdir(parents=True, exist_ok=True)
        self.conv = (art / "conversation.jsonl").open("a", encoding="utf-8")
        self.toollog = (art / "tool-calls.jsonl").open("a", encoding="utf-8")
        self.res = AgentResult(status="budget_exhausted")
        self.deadline = None
        self.lean_src = self._lean_src()
        self.tests = 0

    def _safe_path(self, rel: str):
        p = super()._safe_path(rel)
        if p is not None and ("/V2/" in str(p) and p.name == "Gold.lean"):
            return None
        if p is not None and "/Benchmark/Cases/" in str(p):
            return None
        return p

    def _normalize(self, spec: str) -> str:
        spec = strip_fences(spec).strip()
        if f"namespace {self.target.cand_ns}" not in spec:
            # a bare body: wrap it into the template
            return self.original.replace(
                "-- Write your specification here: one or more `def prop_<name> (inputs…) : Prop`.", spec)
        return spec + "\n"

    def _evaluate(self, text: str, n: int, seed: int) -> str:
        fail = policy(self.target, text)
        if fail:
            return f"REJECTED (policy): {fail}"
        props = decl_names(text, "prop_")
        if not props:
            return "REJECTED: no `def prop_<name> … : Prop` found in the file."
        build = Path(tempfile.mkdtemp(prefix=f"v2agent-{self.target.slug}-", dir=CACHE.parent))
        try:
            ok, out, root = compile_candidate(self.target, text, build)
            if not ok:
                out = out.replace(str(build / "src") + "/", "")
                return "LEAN ERROR (the file does not elaborate):\n" + out.strip()[-5000:]
            res = test_properties(self.target, [f"{self.target.cand_ns}.{p}" for p in props], root, n, seed, timeout=600)
            lines = []
            for p in props:
                r = res[f"{self.target.cand_ns}.{p}"]
                if not r.get("ok"):
                    err = r.get("error", "")
                    lines.append(f"- {p}: UNTESTABLE ({err[:600]})")
                elif r["failures"]:
                    lines.append(f"- {p}: FALSE on {len(r['failures'])}+ input(s), e.g. {r['failures'][:2]} (tested {r['tested']})")
                else:
                    lines.append(f"- {p}: held on all {r['tested']} generated inputs")
            if out.strip():
                lines.append("\nLean messages:\n" + out.strip()[-1500:])
            return "\n".join(lines)
        finally:
            shutil.rmtree(build, ignore_errors=True)

    EVAL_FORBIDDEN = re.compile(r"\bIO\b|IO\.|EIO|BaseIO|System|Process|\bFS\b|Lean\.|unsafe|run_tac|run_cmd|(?<![0-9])#|"
                                r"\bmacro\b|\belab\b|\bsyntax\b|implemented_by|extern|\bST\b|initialize|"
                                r"dbg_trace|panic!|unsafeIO|Task|Thread")

    def t_eval_expr(self, args) -> str:
        exprs = args.get("exprs") or []
        if isinstance(exprs, str):
            exprs = [exprs]
        exprs = [str(e) for e in exprs][:20]
        if not exprs:
            return "error: pass a non-empty list `exprs` of Lean terms"
        for e in exprs:
            if self.EVAL_FORBIDDEN.search(e) or "\n" in e.strip():
                return f"error: expression not allowed (single-line pure terms only): {e[:200]}"
        header = template(self.target).split(f"namespace {self.target.cand_ns}")[0]
        text = "import Benchmark.Exec.Runtime\n" + header + "\n".join(f"#eval ({e})" for e in exprs) + "\n"
        from .mutate import run_lean_file
        from .exec import EXEC_ROOT, lean_path
        d = EXEC_ROOT / ".rsgb_drivers"
        d.mkdir(exist_ok=True)
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=d, delete=False) as fh:
            fh.write(text)
            path = Path(fh.name)
        try:
            out = run_lean_file(EXEC_ROOT, lean_path(), path, timeout=120)
        finally:
            path.unlink(missing_ok=True)
        if out == "RSGB_TIMEOUT":
            return "error: evaluation timed out (120 s)"
        out = out.replace(str(path), "<eval>")
        return out.strip() or "(no output)"

    def t_show_task(self, _args) -> str:
        return (self.ws / "TASK.md").read_text(encoding="utf-8")

    def t_test_spec(self, args) -> str:
        text = self._normalize(str(args.get("spec", "")))
        self.tests += 1
        (self.art / "attempts" / f"test-{self.tests:02d}.lean").write_text(text, encoding="utf-8")
        self.editable.write_text(text, encoding="utf-8")
        return self._evaluate(text, AGENT_N, AGENT_SEED + self.tests)

    def t_submit(self, args) -> str:
        text = self._normalize(str(args.get("spec", "")))
        self.res.attempts += 1
        (self.art / "attempts" / f"submit-{self.res.attempts:02d}.lean").write_text(text, encoding="utf-8")
        fail = policy(self.target, text)
        if fail:
            return f"REJECTED (policy): {fail}. Fix it and submit again."
        self.editable.write_text(text, encoding="utf-8")
        self.res.status = "solved"
        self.res.final_candidate = text
        return "SUBMITTED. The run ends; the specification will now be graded."

    # inherited loop expects these names
    def run(self) -> AgentResult:
        import rfvb.agent as A
        saved_tools, saved_prompt = A.TOOLS, A.load_prompt
        A.TOOLS = V2_TOOLS
        prompt_text = PROMPT.read_text(encoding="utf-8")
        A.load_prompt = lambda root=None: prompt_text
        self.intro = ""
        try:
            return self._run_v2()
        finally:
            A.TOOLS, A.load_prompt = saved_tools, saved_prompt

    def _run_v2(self) -> AgentResult:
        # Same loop as Runner.run, with the v2 opening message.
        import rfvb.agent as A
        started = time.time()
        messages = [
            {"role": "system", "content": A.load_prompt()},
            {"role": "user", "content": self.t_show_task({}) + "\n\nCurrent editable file:\n```lean\n" + self.original +
             "```\n\n" + f"Budget: {self.budget.max_tool_calls} tool calls (at most {self.budget.max_exploration_calls} "
             f"read_file/search calls), {self.budget.max_turns} turns. Use test_spec to check your properties against "
             "the implementation, then submit the complete file with submit."},
        ]
        for m in messages:
            self.log(self.conv, m)
        no_tool = 0
        while True:
            if self.res.turns >= self.budget.max_turns or self.res.tool_calls >= self.budget.max_tool_calls:
                break
            if self.res.usage["completion_tokens"] >= self.budget.max_completion_tokens_total:
                break
            self.compact_history(messages)
            try:
                resp = self.chat_fn(self.cfg, messages, V2_TOOLS)
            except A.TransportError as exc:
                msg = str(exc)
                self.res.status = "context_overflow" if ("context" in msg or "too long" in msg) else "provider_error"
                self.res.error = msg[:2000]
                break
            self.res.turns += 1
            for k in ("prompt_tokens", "completion_tokens", "total_tokens"):
                self.res.usage[k] += int((resp.get("usage") or {}).get(k) or 0)
            choice = (resp.get("choices") or [{}])[0]
            msg = choice.get("message") or {}
            assistant = {"role": "assistant", "content": msg.get("content") or ""}
            reasoning = msg.get("reasoning_content") or msg.get("reasoning")
            if reasoning:
                assistant["reasoning_content"] = reasoning
            calls = msg.get("tool_calls") or []
            if calls:
                assistant["tool_calls"] = calls
            messages.append(assistant)
            self.log(self.conv, {**{k: v for k, v in assistant.items() if k != "reasoning_content"},
                                 "reasoning": reasoning, "finish_reason": choice.get("finish_reason"), "usage": resp.get("usage")})
            if not calls:
                no_tool += 1
                if no_tool >= 3:
                    self.res.status = "no_tool_calls"
                    break
                nudge = {"role": "user", "content": "Please continue by calling a tool (test_spec to check, submit to finish)."}
                messages.append(nudge)
                self.log(self.conv, nudge)
                continue
            no_tool = 0
            for call in calls:
                fn = (call.get("function") or {}).get("name", "")
                try:
                    args = json.loads((call.get("function") or {}).get("arguments") or "{}")
                    if not isinstance(args, dict):
                        args = {}
                except json.JSONDecodeError:
                    args = None
                t0 = time.time()
                if args is None:
                    out = "error: tool arguments were not valid JSON"
                elif fn in ("read_file", "search") and self.res.exploration_calls >= self.budget.max_exploration_calls:
                    out = "error: exploration budget exhausted; use test_spec and submit."
                else:
                    handler = getattr(self, f"t_{fn}", None)
                    try:
                        out = handler(args) if handler else f"error: unknown tool {fn}"
                    except Exception as exc:  # tool failure must not kill the run
                        out = f"error: tool failed: {exc!r}"
                    if fn in ("read_file", "search"):
                        self.res.exploration_calls += 1
                self.res.tool_calls += 1
                out = truncate(out, self.budget.tool_result_chars)
                if self.res.status != "solved" and self.res.tool_calls == self.budget.max_tool_calls - 8:
                    out += ("\n\n[harness note] Budget almost used: submit your best complete specification with "
                            "submit soon; only submitted specifications are graded.")
                self.log(self.toollog, {"turn": self.res.turns, "tool": fn, "args": args,
                                        "seconds": round(time.time() - t0, 2), "result": out})
                tool_msg = {"role": "tool", "tool_call_id": call.get("id", ""), "content": out}
                messages.append(tool_msg)
                self.log(self.conv, tool_msg)
                if self.res.status == "solved":
                    break
            if self.res.status == "solved":
                break
        self.res.duration_seconds = round(time.time() - started, 2)
        self.conv.close()
        self.toollog.close()
        return self.res
