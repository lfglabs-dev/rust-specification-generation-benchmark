"""Reference agent: OpenAI-compatible tool loop over one task workspace.

The model sees only the isolated workspace (see workspace.py). Tools:
  show_task, read_file, search, run_lean (exploratory),
  check_spec (metered submission attempt).
The loop stops at the first clean `check_spec` or when a budget is exhausted;
the independent verifier then checks Lean kernel elaboration, axioms, and
Z3 SMT equivalence against the hidden ground-truth specification from scratch.
"""
from __future__ import annotations

import json
import re
import subprocess
import time
from dataclasses import dataclass, field
from pathlib import Path

from .limits import lake_command, run_limited
from .policy import policy_failure
from .tasks import Task, opens_block
from .transport import ChatConfig, TransportError, chat
from .z3_spec import check_spec_equivalence

PLACEHOLDER = "  -- Replace this placeholder with the formal specification.\n  True"
SEARCH_SCOPES = {
    "workspace": ["extracted", "Benchmark", "rust"],
    "aeneas": [".lake/packages/aeneas/backends/lean/Aeneas"],
    "coremodels": [".lake/packages/hax/CoreModels", ".lake/packages/hax/Hax"],
    "mathlib": [".lake/packages/mathlib/Mathlib"],
    "lean_core": [],  # resolved at runtime to the toolchain's src/lean
}


@dataclass
class Budget:
    max_attempts: int = 10
    max_tool_calls: int = 80
    max_exploration_calls: int = 25  # read_file/search/show_task
    max_turns: int = 50
    max_completion_tokens_total: int = 400_000
    tool_result_chars: int = 7000
    lean_timeout: int = 300
    context_char_budget: int = 150_000


BUDGETS = {
    "quick": Budget(max_attempts=4, max_tool_calls=30, max_exploration_calls=10, max_turns=20, max_completion_tokens_total=150_000),
    "normal": Budget(),
    "extended": Budget(max_attempts=40, max_tool_calls=300, max_exploration_calls=80, max_turns=200, max_completion_tokens_total=3_000_000),
    "deep": Budget(max_attempts=24, max_tool_calls=160, max_exploration_calls=50, max_turns=100, max_completion_tokens_total=1_500_000),
}

TOOLS = [
    {"type": "function", "function": {
        "name": "show_task",
        "description": "Show the task briefing: contract, origin (Rust property test), semantics, shared helpers, extracted definitions, target specification signature, and rules.",
        "parameters": {"type": "object", "properties": {}}}},
    {"type": "function", "function": {
        "name": "read_file",
        "description": "Read a text file of the workspace (extracted implementation, Defs.lean, editable file, original Rust sources under rust/, or library sources under .lake/packages). Returns numbered lines.",
        "parameters": {"type": "object", "properties": {
            "path": {"type": "string", "description": "workspace-relative path"},
            "start_line": {"type": "integer", "description": "1-based first line (default 1)"},
            "num_lines": {"type": "integer", "description": "number of lines (default 250, max 400)"}},
            "required": ["path"]}}},
    {"type": "function", "function": {
        "name": "search",
        "description": "Regex search (grep -E) for declarations/types/functions. scope: workspace | aeneas | coremodels | mathlib | lean_core.",
        "parameters": {"type": "object", "properties": {
            "pattern": {"type": "string"},
            "scope": {"type": "string", "enum": list(SEARCH_SCOPES)}},
            "required": ["pattern", "scope"]}}},
    {"type": "function", "function": {
        "name": "run_lean",
        "description": "Exploration: elaborate a candidate specification WITHOUT submitting it. `spec` is either the specification body (the `Prop` expression replacing `True`), a `def <spec_name> ... := ...` snippet, or a complete Lean file. Returns Lean's messages. Does not consume an attempt.",
        "parameters": {"type": "object", "properties": {"spec": {"type": "string"}}, "required": ["spec"]}}},
    {"type": "function", "function": {
        "name": "check_spec",
        "description": "Submit a formal specification attempt (consumes one attempt). `spec` is either the specification body replacing `True`, a `def <spec_name> ... := ...` snippet, or a complete Lean file for the editable specification file (helper definitions allowed above the target `def`; the target signature must be unchanged). Succeeds only if policy, Lean 4 kernel elaboration, and Z3 non-vacuity/non-triviality checks pass; then the run ends and the independent verifier checks full Z3 equivalence against the reference specification.",
        "parameters": {"type": "object", "properties": {"spec": {"type": "string"}}, "required": ["spec"]}}},
]


PROMPT_DIR = Path(__file__).resolve().parent / "prompts"


def load_prompt(root: Path | None = None) -> str:
    p = PROMPT_DIR / "PROMPT.md"
    return p.read_text(encoding="utf-8") if p.is_file() else ""


def dedent_body(body: str) -> str:
    lines = body.replace("\t", "  ").strip("\n").splitlines()
    indents = [len(l) - len(l.lstrip()) for l in lines if l.strip()]
    base = min(indents) if indents else 0
    return "\n".join(("  " + l[base:]) if l.strip() else "" for l in lines)


def strip_fences(text: str) -> str:
    m = re.search(r"```(?:lean4?|)\s*\n(.*?)```", text, re.DOTALL)
    return m.group(1) if m else text


def materialize(task: Task, original: str, spec: str) -> str:
    spec = strip_fences(spec).strip()
    if re.search(r"^\s*import\s", spec, re.M) and f"namespace {task.namespace}" in spec:
        return spec + "\n"
    m_def = re.search(
        rf"^(?:noncomputable\s+)?def\s+(?:{re.escape(task.spec_decl_name)}|{re.escape(task.spec_name)})\b.*?$",
        spec,
        re.M | re.S,
    )
    if m_def and not re.search(r"^\s*import\s", spec, re.M):
        # Extract body after the first top-level `:=` in the def
        decl_text = m_def.group(0)
        prefix_helpers = spec[: m_def.start()].strip()
        depth = 0
        opens, closes = "([{⦃⟨", ")]}⦄⟩"
        split_idx = None
        j = 0
        while j < len(decl_text) - 1:
            ch = decl_text[j]
            if ch in opens:
                depth += 1
            elif ch in closes:
                depth -= 1
            elif depth == 0 and decl_text[j : j + 2] == ":=":
                split_idx = j
                break
            j += 1
        if split_idx is not None:
            body = decl_text[split_idx + 2 :].strip("\n")
            if not body.startswith(" "):
                body = dedent_body(body)
            out = original.replace(PLACEHOLDER, body)
            if prefix_helpers:
                ns_hdr = f"namespace {task.namespace}"
                out = out.replace(ns_hdr, f"{ns_hdr}\n\n{prefix_helpers}", 1)
            return out
    body = spec.strip()
    body = re.sub(r"^:=\s*", "", body).strip("\n")
    return original.replace(PLACEHOLDER, dedent_body(body))


def run_lean_file(ws: Path, rel: str, timeout: int) -> tuple[int, str]:
    cmd, gated = lake_command(["env", "lean", rel])
    code, out = run_limited(cmd, ws, timeout, gated=gated)
    return code, (f"Lean timed out after {timeout}s" if code == 124 else out)


def truncate(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    head = text[: limit // 2]
    tail = text[-limit // 2 :]
    return f"{head}\n... [{len(text) - limit} chars elided] ...\n{tail}"


def classify_lean_output(code: int, out: str) -> str:
    if code == 124:
        return "lean_timeout"
    if code == 75:
        return "lean_unavailable"
    if "out of memory" in out or "std::bad_alloc" in out:
        return "lean_out_of_memory"
    if "unknown identifier" in out or "unknown constant" in out or "Unknown identifier" in out or "Unknown constant" in out:
        return "unknown_name"
    if "unsolved goals" in out:
        return "unsolved_goals"
    if "unexpected token" in out or ("expected" in out and "parse" in out):
        return "parse_error"
    if "type mismatch" in out.lower():
        return "type_mismatch"
    return "lean_error"


@dataclass
class AgentResult:
    status: str  # solved | budget_exhausted | provider_error | context_overflow | no_tool_calls
    attempts: int = 0
    tool_calls: int = 0
    exploration_calls: int = 0
    lean_runs: int = 0
    turns: int = 0
    usage: dict = field(default_factory=lambda: {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0})
    final_candidate: str | None = None
    last_failure_class: str | None = None
    error: str | None = None
    duration_seconds: float = 0.0
    resumed: int = 0


class Runner:
    def __init__(self, task: Task, ws: Path, cfg: ChatConfig, budget: Budget, art: Path, root: Path,
                 chat_fn=chat):
        self.task, self.ws, self.cfg, self.budget, self.art, self.root = task, ws, cfg, budget, art, root
        self.chat_fn = chat_fn
        self.original = (root / task.editable_file).read_text(encoding="utf-8")
        self.editable = ws / task.editable_file
        self.scratch_rel = f".rfvb_scratch/{Path(task.editable_file).name}"
        (ws / ".rfvb_scratch").mkdir(exist_ok=True)
        (art / "attempts").mkdir(parents=True, exist_ok=True)
        self.conv = (art / "conversation.jsonl").open("a", encoding="utf-8")
        self.toollog = (art / "tool-calls.jsonl").open("a", encoding="utf-8")
        self.res = AgentResult(status="budget_exhausted")
        self.deadline: float | None = None
        self.lean_src = self._lean_src()

    def _lean_src(self) -> str:
        try:
            prefix = subprocess.run(["lean", "--print-prefix"], cwd=self.ws, capture_output=True, text=True).stdout.strip()
            return str(Path(prefix) / "src" / "lean")
        except OSError:
            return ""

    # ---- tools -------------------------------------------------------
    def _safe_path(self, rel: str) -> Path | None:
        p = (self.ws / rel).resolve()
        allowed = [self.ws.resolve(), (self.ws / ".lake" / "packages").resolve()]
        if self.lean_src:
            allowed.append(Path(self.lean_src).resolve())
        if not any(str(p).startswith(str(a)) for a in allowed):
            return None
        if ".lake/build" in str(p) or "/References/" in str(p) or "/Proofs/" in str(p) or p.name in (".env", "Specs.lean"):
            return None
        return p

    def t_show_task(self, _args) -> str:
        return (self.ws / "TASK.md").read_text(encoding="utf-8")

    def t_read_file(self, args) -> str:
        p = self._safe_path(str(args.get("path", "")))
        if p is None or not p.is_file():
            return "error: file not found or not readable in this workspace"
        start = max(1, int(args.get("start_line") or 1))
        n = min(400, max(1, int(args.get("num_lines") or 250)))
        lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
        chunk = lines[start - 1 : start - 1 + n]
        out = "\n".join(f"{start + i:5d}  {l}" for i, l in enumerate(chunk))
        return out + f"\n[lines {start}-{start + len(chunk) - 1} of {len(lines)}]"

    def t_search(self, args) -> str:
        scope = args.get("scope", "workspace")
        dirs = SEARCH_SCOPES.get(scope)
        if dirs is None:
            return "error: unknown scope"
        if scope == "lean_core":
            dirs = [self.lean_src + "/Init", self.lean_src + "/Std"] if self.lean_src else []
        paths = [d if d.startswith("/") else str(self.ws / d) for d in dirs]
        cmd = ["grep", "-rnE", "--include=*.lean", "-m", "40", str(args.get("pattern", "")), *paths]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            return "error: search timed out; use a more specific pattern"
        out = proc.stdout.replace(str(self.ws) + "/", "")
        if self.lean_src:
            out = out.replace(self.lean_src + "/", "<lean>/")
        lines = [l if len(l) < 300 else l[:300] + "…" for l in out.splitlines()]
        if not lines:
            return "no matches"
        return "\n".join(lines[:80]) + (f"\n[{len(lines) - 80} more matches]" if len(lines) > 80 else "")

    def t_run_lean(self, args) -> str:
        raw_spec = str(args.get("spec") if "spec" in args else args.get("proof", ""))
        text = materialize(self.task, self.original, raw_spec)
        scratch = self.ws / self.scratch_rel
        scratch.write_text(text, encoding="utf-8")
        code, out = run_lean_file(self.ws, self.scratch_rel, self.budget.lean_timeout)
        out = out.replace(self.scratch_rel, "EditableFile.lean").strip()
        clean = code == 0 and not re.search(r"\berror\b", out) and "declaration uses 'sorry'" not in out
        note = ("\n[harness note] This specification elaborated without errors or sorry. run_lean is not graded: "
                "submit it with check_spec when you are confident it captures the complete property.") if clean else ""
        return (out or "no messages (file elaborated without errors or warnings)") + f"\n[exit {code}]" + note

    def _check_self_vacuity(self) -> tuple[str, str] | None:
        """Run spec_audit on the candidate spec alone (no OracleSpec) to catch vacuous or trivial specs."""
        self_mod = self.task.defs_module.replace(".Defs", ".SelfCheck")
        self_rel = self.task.defs_file.replace("/Defs.lean", "/SelfCheck.lean")
        self_path = self.ws / self_rel
        self_olean = Path(".lake/build/lib/lean") / Path(*self_mod.split(".")).with_suffix(".olean")
        (self.ws / self_olean).parent.mkdir(parents=True, exist_ok=True)
        self_content = (
            f"import {self.task.target_module}\n\n"
            f"{opens_block(self.task)}\n\n"
            f"namespace {self.task.namespace}\n\n"
            f"axiom _rsgb_self_thm {self.task.theorem_statement}\n\n"
            f"end {self.task.namespace}\n"
        )
        self_path.write_text(self_content, encoding="utf-8")
        try:
            cmd_build, gated = lake_command(["env", "lean", "-o", str(self_olean), self_rel])
            b_code, b_out = run_limited(cmd_build, self.ws, self.budget.lean_timeout, gated=gated)
            if b_code != 0 or re.search(r"\berror\b", b_out):
                return "lean_error", b_out.strip()
            cmd_audit, gated_a = lake_command([
                "env", ".lake/build/bin/spec_audit",
                self_mod,
                f"{self.task.namespace}._rsgb_self_thm",
            ])
            a_code, a_out = run_limited(cmd_audit, self.ws, self.budget.lean_timeout, gated=gated_a)
            if a_code != 0:
                return None
            json_line = None
            for line in reversed(a_out.splitlines()):
                sline = line.strip()
                if sline.startswith("{") and sline.endswith("}"):
                    json_line = sline
                    break
            if not json_line:
                return None
            data = json.loads(json_line)
            if "error" in data:
                return None
            z3_res = check_spec_equivalence(data, timeout_ms=5000)
            if z3_res.status in ("vacuous_spec", "trivial_spec"):
                return z3_res.status, z3_res.detail
            return None
        finally:
            self_path.unlink(missing_ok=True)

    def t_check_spec(self, args) -> str:
        self.res.attempts += 1
        raw_spec = str(args.get("spec") if "spec" in args else args.get("proof", ""))
        text = materialize(self.task, self.original, raw_spec)
        (self.art / "attempts" / f"{self.res.attempts:02d}.lean").write_text(text, encoding="utf-8")
        fail = policy_failure(self.task, text, allowed_local_imports=(self.task.defs_module,))
        if fail:
            self.res.last_failure_class = fail[0]
            return f"REJECTED ({fail[0]}): {fail[1]}. Attempts used: {self.res.attempts}/{self.budget.max_attempts}."
        self.editable.write_text(text, encoding="utf-8")
        mod_olean = Path(".lake/build/lib/lean") / Path(*self.task.target_module.split(".")).with_suffix(".olean")
        (self.ws / mod_olean).parent.mkdir(parents=True, exist_ok=True)
        cmd, gated = lake_command(["env", "lean", "-o", str(mod_olean), self.task.editable_file])
        code, out = run_limited(cmd, self.ws, self.budget.lean_timeout, gated=gated)
        errors = code != 0 or re.search(r"\berror\b", out)
        if errors or "declaration uses 'sorry'" in out:
            self.res.last_failure_class = classify_lean_output(code, out)
            return f"FAILED ({self.res.last_failure_class}). Attempts used: {self.res.attempts}/{self.budget.max_attempts}.\n" + out.strip()
        vac_fail = self._check_self_vacuity()
        if vac_fail:
            self.res.last_failure_class = vac_fail[0]
            return f"REJECTED ({vac_fail[0]}): {vac_fail[1]} Attempts used: {self.res.attempts}/{self.budget.max_attempts}."
        self.res.status = "solved"
        self.res.final_candidate = text
        return "ACCEPTED by the local check (well-typed, non-vacuous, non-trivial). The run ends; the independent verifier will now check full Z3 equivalence against the reference specification."

    t_check_proof = t_check_spec

    # ---- loop --------------------------------------------------------
    def log(self, handle, obj) -> None:
        handle.write(json.dumps(obj, ensure_ascii=False) + "\n")
        handle.flush()

    def compact_history(self, messages: list[dict]) -> None:
        total = sum(len(json.dumps(m, ensure_ascii=False)) for m in messages)
        before = total
        i = 2
        while total > self.budget.context_char_budget and i < len(messages) - 6:
            m = messages[i]
            if m.get("role") == "tool" and not m.get("content", "").startswith("[elided"):
                old = len(m["content"])
                m["content"] = "[elided older tool output to fit the context budget]"
                total -= old
            i += 1
        i = 2
        while total > self.budget.context_char_budget and i < len(messages) - 6:
            m = messages[i]
            if m.get("role") == "assistant" and m.get("reasoning_content"):
                total -= len(json.dumps(m["reasoning_content"], ensure_ascii=False))
                del m["reasoning_content"]
            i += 1
        if total != before:
            self.log(self.conv, {"role": "harness", "event": "compacted", "chars_before": before, "chars_after": total})

    def restore(self) -> list[dict] | None:
        conv_path = self.art / "conversation.jsonl"
        if not conv_path.is_file() or conv_path.stat().st_size == 0:
            return None
        messages: list[dict] = []
        for line in conv_path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            m = json.loads(line)
            role = m.get("role")
            if role == "assistant":
                self.res.turns += 1
                for k in ("prompt_tokens", "completion_tokens", "total_tokens"):
                    self.res.usage[k] += int((m.get("usage") or {}).get(k) or 0)
                entry = {"role": "assistant", "content": m.get("content") or ""}
                if m.get("reasoning"):
                    entry["reasoning_content"] = m["reasoning"]
                if m.get("tool_calls"):
                    entry["tool_calls"] = m["tool_calls"]
                messages.append(entry)
            elif role == "tool":
                messages.append({"role": "tool", "tool_call_id": m.get("tool_call_id", ""), "content": m.get("content", "")})
            elif role in ("system", "user"):
                messages.append({"role": role, "content": m.get("content", "")})
        while messages:
            last_asst = max((i for i, m in enumerate(messages) if m["role"] == "assistant"), default=None)
            if last_asst is None:
                break
            calls = messages[last_asst].get("tool_calls") or []
            answered = {m.get("tool_call_id") for m in messages[last_asst + 1:] if m["role"] == "tool"}
            if calls and not all(c.get("id") in answered for c in calls):
                del messages[last_asst:]
                continue
            break
        tool_path = self.art / "tool-calls.jsonl"
        if tool_path.is_file():
            for line in tool_path.read_text(encoding="utf-8").splitlines():
                if not line.strip():
                    continue
                t = json.loads(line)
                self.res.tool_calls += 1
                if t.get("tool") in ("read_file", "search", "show_task"):
                    self.res.exploration_calls += 1
                elif t.get("tool") in ("run_lean", "check_spec", "check_proof"):
                    self.res.lean_runs += 1
                if t.get("tool") in ("check_spec", "check_proof"):
                    self.res.attempts += 1
        attempts = sorted((self.art / "attempts").glob("*.lean"))
        if attempts:
            self.editable.write_text(attempts[-1].read_text(encoding="utf-8"), encoding="utf-8")
        self.res.resumed += 1
        return messages if len(messages) >= 2 else None

    def run(self) -> AgentResult:
        started = time.time()
        system = load_prompt()
        restored = self.restore()
        messages = restored or [
            {"role": "system", "content": system},
            {"role": "user", "content": getattr(self, "intro", "") + self.t_show_task({}) + "\n\nCurrent editable file:\n```lean\n" + self.original + "```\n\n"
             f"Budget: {self.budget.max_attempts} check_spec attempts, {self.budget.max_tool_calls} tool calls "
             f"(at most {self.budget.max_exploration_calls} read_file/search calls), {self.budget.max_turns} turns. "
             "The shared helper definitions and relevant extracted code are included above; use run_lean to test "
             "elaboration of your specification and submit with check_spec."},
        ]
        if restored is None:
            for m in messages:
                self.log(self.conv, m)
        else:
            self.log(self.conv, {"role": "harness", "event": "resumed", "turns": self.res.turns, "tool_calls": self.res.tool_calls})
        no_tool_streak = 0
        while True:
            if self.res.turns >= self.budget.max_turns or self.res.tool_calls >= self.budget.max_tool_calls or self.res.attempts >= self.budget.max_attempts:
                break
            if self.res.usage["completion_tokens"] >= self.budget.max_completion_tokens_total:
                break
            if self.deadline is not None and time.time() >= self.deadline:
                self.res.error = "wall-clock budget reached"
                break
            self.compact_history(messages)
            try:
                resp = self.chat_fn(self.cfg, messages, TOOLS)
            except TransportError as exc:
                msg = str(exc)
                self.res.status = "context_overflow" if ("maximum context" in msg or "context length" in msg or "too long" in msg) else "provider_error"
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
            self.log(self.conv, {**{k: v for k, v in assistant.items() if k != "reasoning_content"}, "reasoning": reasoning, "finish_reason": choice.get("finish_reason"), "usage": resp.get("usage")})
            if not calls:
                no_tool_streak += 1
                if no_tool_streak >= 3:
                    self.res.status = "no_tool_calls"
                    break
                nudge = {"role": "user", "content": "Please continue by calling a tool (run_lean to test elaboration, check_spec to submit)."}
                messages.append(nudge)
                self.log(self.conv, nudge)
                continue
            no_tool_streak = 0
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
                elif fn in ("read_file", "search", "show_task") and self.res.exploration_calls >= self.budget.max_exploration_calls:
                    out = (f"error: exploration budget exhausted ({self.budget.max_exploration_calls} read/search calls). "
                           "Work with what you have: use run_lean to test your specification and check_spec to submit.")
                else:
                    handler = getattr(self, f"t_{fn}", None)
                    out = handler(args) if handler else f"error: unknown tool {fn}"
                    if fn in ("read_file", "search", "show_task"):
                        self.res.exploration_calls += 1
                        if self.res.lean_runs == 0 and self.res.exploration_calls in (8, 16):
                            out += ("\n\n[harness note] You have made several exploration calls without running Lean. "
                                    "Try drafting your candidate specification with run_lean now; read more only if a specific type or function signature is missing.")
                    elif fn in ("run_lean", "check_spec", "check_proof"):
                        self.res.lean_runs += 1
                self.res.tool_calls += 1
                out = truncate(out, self.budget.tool_result_chars)
                if self.res.status != "solved" and (
                        self.res.tool_calls == self.budget.max_tool_calls - 10
                        or (call is calls[-1] and self.res.turns == self.budget.max_turns - 5)):
                    out += (f"\n\n[harness note] Budget almost used: {self.budget.max_tool_calls - self.res.tool_calls} tool calls, "
                            f"{self.budget.max_turns - self.res.turns} turns and {self.budget.max_attempts - self.res.attempts} "
                            "check_spec attempts left. Only specifications submitted with check_spec are graded: "
                            "submit your best specification with check_spec soon.")
                self.log(self.toollog, {"turn": self.res.turns, "tool": fn, "args": args, "seconds": round(time.time() - t0, 2), "result": out})
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
