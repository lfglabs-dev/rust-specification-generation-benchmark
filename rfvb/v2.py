"""RSGB v2: specification *design* tasks graded by truth + mutation strength.

A v2 target names a small public API of one crate (e.g. `obfuscate` /
`deobfuscate` / `feistel_n` / `feistel_n_inv` of `arxid::permute`). The agent
writes any number of properties `def prop_<name> (inputs…) : Prop` in the
editable `Candidate.lean`; nothing about the expected properties is revealed.

Grading (`grade`):
  1. policy: forbidden tokens, imports, no use of the crate's private helpers;
  2. the candidate elaborates (normal build) and compiles (executable build);
  3. truth: every property holds on the real implementation on `TRUTH_N`
     generated inputs per property (hidden seed). Any false property ⇒ score 0;
  4. strength: fraction of the target's *relevant* mutants on which at least one
     property is falsified.

A mutant is relevant iff it compiles, is observably different from the original
on the gold `diff_*` probes, and violates the hidden gold specification
(`Gold.lean`), i.e. it breaks the intended contract (`prepare`).

  python -m rfvb.v2 prepare <target|all> [--mutants 60] [--jobs 6]
  python -m rfvb.v2 grade <target> <Candidate.lean>
  python -m rfvb.v2 baseline <target|all>     # score the upstream property tests
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from pathlib import Path

from . import ROOT
from .exec import EXEC_ROOT, build as exec_build, lean_path as exec_lean_path, sync_v2
from .mutate import Mutant, MutantBuilder, candidates, cone, parse_outputs, parse_results, run_lean_file, sample

TARGETS_DIR = ROOT / "v2" / "targets"
CACHE = ROOT / ".lake" / "v2cache"
DIFF_N = 400
GOLD_N = 1500
TRUTH_N = 3000
KILL_N = 1500
TRUTH_SEED = 104729  # hidden from agents (they get a different seed in `test_spec`)
KILL_SEED = 7919


@dataclass
class Target:
    raw: dict

    def __getattr__(self, k):
        try:
            return self.raw[k]
        except KeyError as exc:
            raise AttributeError(k) from exc

    @property
    def slug(self) -> str:
        return self.id.replace("/", "__")

    @property
    def gold_module(self) -> str:
        return f"{self.module_prefix}.Gold"

    @property
    def candidate_module(self) -> str:
        return f"{self.module_prefix}.Candidate"

    @property
    def candidate_file(self) -> str:
        return self.module_prefix.replace(".", "/") + "/Candidate.lean"

    @property
    def gold_file(self) -> str:
        return self.module_prefix.replace(".", "/") + "/Gold.lean"

    @property
    def cand_ns(self) -> str:
        return f"{self.module_prefix}.Candidate"

    @property
    def gold_ns(self) -> str:
        return f"{self.module_prefix}.Gold"


def load_targets() -> dict[str, Target]:
    out = {}
    for f in sorted(TARGETS_DIR.glob("*.json")):
        t = Target(json.loads(f.read_text(encoding="utf-8")))
        out[t.id] = t
    return out


def select(spec: str) -> list[Target]:
    ts = load_targets()
    if spec == "all":
        return list(ts.values())
    return [ts[s] for s in spec.split(",")]


def decl_names(text: str, prefix: str) -> list[str]:
    return re.findall(rf"^(?:@\[[^\]]*\]\s*)*def\s+({prefix}[\w']*)", text, re.M)


# ---------------------------------------------------------------- drivers

def driver(imports: list[str], tests: list[tuple[str, int, int]], outputs: list[tuple[str, int, int]] = ()) -> str:
    lines = ["import Benchmark.Exec.Driver", *[f"import {m}" for m in imports]]
    lines += [f"#rsgb_test {n} {k} {s}" for n, k, s in tests]
    lines += [f"#rsgb_outputs {n} {k} {s}" for n, k, s in outputs]
    return "\n".join(lines) + "\n"


def run_driver(text: str, lean_path: str, timeout: int = 900) -> str:
    d = EXEC_ROOT / ".rsgb_drivers"
    d.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=d, delete=False) as fh:
        fh.write(text)
        p = Path(fh.name)
    try:
        return run_lean_file(EXEC_ROOT, lean_path, p, timeout)
    finally:
        p.unlink(missing_ok=True)


# ---------------------------------------------------------------- prepare

def prepare(t: Target, n_mutants: int = 60, jobs: int = 6, seed: int = 0, log=print) -> dict:
    lp = exec_lean_path()
    work = CACHE / t.slug
    work.mkdir(parents=True, exist_ok=True)
    funs = (EXEC_ROOT / "extracted" / t.package / "Extraction" / "Funs.lean").read_text(encoding="utf-8")
    targets = cone(funs, t.mutation_roots)
    cands = candidates(funs, targets)
    muts = sample(cands, n_mutants, seed) + manual_mutants(t, funs)
    log(f"[{t.id}] cone={len(targets)} defs, {len(cands)} candidate mutants, sampled {len(muts)} "
        f"(incl. {len(t.raw.get('manual_mutants', []))} hand-written)")

    gold_text = (ROOT / t.gold_file).read_text(encoding="utf-8")
    golds = [f"{t.gold_ns}.{n}" for n in decl_names(gold_text, "gold_")]
    diffs = [f"{t.gold_ns}.{n}" for n in decl_names(gold_text, "diff_")]

    # gold must hold on the original
    out = run_driver(driver([t.gold_module], [(g, GOLD_N, KILL_SEED) for g in golds],
                            [(d, DIFF_N, KILL_SEED) for d in diffs]), lp)
    res = parse_results(out)
    bad = [g for g in golds if not res.get(g, {}).get("ok") or res[g]["failures"]]
    if bad:
        raise RuntimeError(f"gold properties fail on the original implementation: {bad}\n{out[-3000:]}")
    base_out = parse_outputs(out)
    if set(base_out) != set(diffs):
        raise RuntimeError(f"diff probes failed: {out[-3000:]}")

    builder = MutantBuilder(EXEC_ROOT, t.package, work / "mutants", lp)

    def one(m: Mutant) -> Mutant:
        ok, msg = builder.build(m)
        if not ok:
            m.status = "compile_error"
            return m
        mlp = builder.lean_path_for(m)
        o = run_driver(driver([t.gold_module], [], [(d, DIFF_N, KILL_SEED) for d in diffs]), mlp, timeout=300)
        if "RSGB_TIMEOUT" in o:
            m.status = "timeout"
            return m
        mo = parse_outputs(o)
        if set(mo) != set(diffs):
            m.status = "driver_error"
            return m
        m.differing_inputs = sum(a != b for d in diffs for a, b in zip(base_out[d], mo[d]))
        if m.differing_inputs == 0:
            m.status = "equivalent"
            return m
        o = run_driver(driver([t.gold_module], [(g, GOLD_N, KILL_SEED) for g in golds]), mlp, timeout=600)
        r = parse_results(o)
        m.killed_by_gold = [g.split(".")[-1] for g in golds if r.get(g, {}).get("ok") and r[g]["failures"]]
        m.status = "relevant" if m.killed_by_gold else "unspecified"
        return m

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        muts = list(pool.map(one, muts))
    summary = {}
    for m in muts:
        summary[m.status] = summary.get(m.status, 0) + 1
    data = {"target": t.id, "summary": summary, "mutants": [m.to_json() for m in muts]}
    (work / "mutants.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
    log(f"[{t.id}] {summary}")
    return data


def check_gold(t: Target) -> str:
    """Truth-test the gold properties and run the diff probes on the original implementation."""
    gold_text = (ROOT / t.gold_file).read_text(encoding="utf-8")
    golds = [f"{t.gold_ns}.{n}" for n in decl_names(gold_text, "gold_")]
    diffs = [f"{t.gold_ns}.{n}" for n in decl_names(gold_text, "diff_")]
    out = run_driver(driver([t.gold_module], [(g, GOLD_N, KILL_SEED) for g in golds] +
                            [(g, GOLD_N, TRUTH_SEED) for g in golds], [(d, 20, KILL_SEED) for d in diffs]),
                     exec_lean_path())
    lines = [l for l in out.splitlines() if "RSGB_" in l or "error" in l]
    return "\n".join(lines)


def manual_mutants(t: Target, funs: str) -> list[Mutant]:
    """Hand-written plausible bugs: `{"decl", "before", "after", "note"}` single-line edits.

    `before` must occur exactly once inside the body of `decl` (whitespace-insensitive
    at the ends); `after` replaces that line.
    """
    import hashlib
    from .mutate import decl_ranges
    lines = funs.splitlines()
    ranges = {n: (a, b) for n, a, b in decl_ranges(funs)}
    out = []
    for spec in t.raw.get("manual_mutants", []):
        a, b = ranges[spec["decl"]]
        hits = [i for i in range(a, b) if lines[i].strip() == spec["before"].strip()]
        if len(hits) != 1:
            raise ValueError(f"manual mutant {spec}: `before` matches {len(hits)} lines of {spec['decl']}")
        i = hits[0]
        indent = lines[i][: len(lines[i]) - len(lines[i].lstrip())]
        after = indent + spec["after"].strip()
        mid = "man-" + hashlib.sha1(f"{i}:{after}".encode()).hexdigest()[:8]
        out.append(Mutant(mid, spec["decl"], i + 1, "manual", lines[i], after))
    return out


def load_mutants(t: Target) -> list[Mutant]:
    data = json.loads((CACHE / t.slug / "mutants.json").read_text(encoding="utf-8"))
    return [Mutant(**m) for m in data["mutants"]]


# ---------------------------------------------------------------- grading

FORBIDDEN = [r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bnative_decide\b", r"implemented_by", r"\bextern\b",
             r"\bunsafe\b", r"#eval", r"\bmacro\b", r"\bsyntax\b", r"\belab\b", r"\bnotation\b", r"\binfix",
             r"\bprefix\b", r"\bpostfix\b", r"set_option\s+debug", r"\bopaque\b", r"\binitialize\b", r"IO\.",
             r"\bpartial\b", r"@\[\s*csimp", r"#rsgb"]


@dataclass
class Grade:
    target: str
    status: str  # graded | policy | lean_error | no_properties | false_property | harness_error
    score: float = 0.0
    killed: int = 0
    relevant: int = 0
    properties: list[str] = field(default_factory=list)
    untestable: dict = field(default_factory=dict)
    false_properties: dict = field(default_factory=dict)
    per_mutant: dict = field(default_factory=dict)
    class_score: float = 0.0
    classes: int = 0
    detail: str = ""

    def to_json(self) -> dict:
        return self.__dict__.copy()


def policy(t: Target, text: str) -> str | None:
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    for pat in FORBIDDEN:
        if re.search(pat, code):
            return f"forbidden construct: {pat}"
    for imp in re.findall(r"^\s*import\s+(\S+)", code, re.M):
        if not (imp in t.allowed_imports or imp.startswith(("Mathlib", "Aeneas", "CoreModels", "Hax", "Std", "Init"))
                or imp == "Benchmark.V2.Prelude"):
            return f"import not allowed: {imp}"
    if f"namespace {t.cand_ns}" not in code:
        return f"the specification must live in namespace {t.cand_ns}"
    for name in t.raw.get("forbidden_constants", []):
        short = name.split(".")[-1]
        if re.search(rf"(?<![\w]){re.escape(short)}(?![\w'])", code) or name in code:
            return f"use of a private implementation function is not allowed: {name}"
    return None


def compile_candidate(t: Target, text: str, build_root: Path) -> tuple[bool, str, Path]:
    """Compile Candidate.lean into a private olean tree on top of the exec build."""
    rel = Path(t.candidate_file)
    src_root = build_root / "src"
    out_root = build_root / "olean"
    (src_root / rel).parent.mkdir(parents=True, exist_ok=True)
    (src_root / rel).write_text(text, encoding="utf-8")
    # shadow the Benchmark package: symlink-copy the exec build, then add the candidate
    (out_root).mkdir(parents=True, exist_ok=True)
    bench = out_root / "Benchmark"
    if not bench.exists():
        subprocess.run(["cp", "-rs", str(EXEC_ROOT / ".lake/build/lib/lean/Benchmark"), str(out_root)], check=True)
    olean = out_root / rel.with_suffix(".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    for p in (olean, olean.with_suffix(".ilean")):
        if p.is_symlink() or p.exists():
            p.unlink()
    lp = f"{out_root}:{exec_lean_path()}"
    proc = subprocess.run(["lean", f"--root={src_root}", "-o", str(olean), "-i", str(olean.with_suffix('.ilean')),
                           str(src_root / rel)], cwd=EXEC_ROOT, env=_env(lp), capture_output=True, text=True,
                          timeout=900)
    out = proc.stdout + proc.stderr
    ok = proc.returncode == 0 and not re.search(r"\berror\b", out) and olean.is_file()
    return ok, out, out_root


def _env(lp: str) -> dict:
    import os
    env = dict(os.environ)
    env["LEAN_PATH"] = lp
    return env


def test_properties(t: Target, props: list[str], cand_root: Path, n: int, seed: int,
                    mutant_root: Path | None = None, timeout: int = 900) -> dict[str, dict]:
    lp = f"{cand_root}:{exec_lean_path()}"
    if mutant_root is not None:
        lp = f"{mutant_root}:{lp}"
    out = run_driver(driver([t.candidate_module], [(p, n, seed) for p in props]), lp, timeout)
    res = parse_results(out)
    if "RSGB_TIMEOUT" in out:
        for p in props:
            res.setdefault(p, {"ok": False, "error": "timeout", "name": p})
    for p in props:
        res.setdefault(p, {"ok": False, "error": "no result (elaboration error?)\n" + out[-1500:], "name": p})
    return res


def grade(t: Target, text: str, jobs: int = 6, keep: bool = False) -> Grade:
    g = Grade(t.id, "harness_error")
    fail = policy(t, text)
    if fail:
        g.status, g.detail = "policy", fail
        return g
    props_short = decl_names(text, "prop_")
    if not props_short:
        g.status, g.detail = "no_properties", "no `def prop_<name> … : Prop` found"
        return g
    props = [f"{t.cand_ns}.{p}" for p in props_short]
    g.properties = props_short
    build = Path(tempfile.mkdtemp(prefix=f"v2-{t.slug}-", dir=CACHE.parent))
    try:
        ok, out, cand_root = compile_candidate(t, text, build)
        if not ok:
            g.status, g.detail = "lean_error", out[-4000:]
            return g
        res = test_properties(t, props, cand_root, TRUTH_N, TRUTH_SEED)
        testable = []
        for p in props:
            r = res[p]
            short = p.split(".")[-1]
            if not r.get("ok"):
                g.untestable[short] = r.get("error", "")[:500]
            elif r["failures"]:
                g.false_properties[short] = r["failures"]
            else:
                testable.append(p)
        if g.false_properties:
            g.status = "false_property"
            g.detail = "a property is false on the real implementation"
            return g
        if not testable:
            g.status, g.detail = "no_properties", "no executable property (see untestable)"
            return g
        muts = [m for m in load_mutants(t) if m.status == "relevant"]
        g.relevant = len(muts)
        work = CACHE / t.slug / "mutants"

        def kill(m: Mutant) -> tuple[str, list[str]]:
            r = test_properties(t, testable, cand_root, KILL_N, KILL_SEED, mutant_root=work / m.mid / "olean",
                                timeout=600)
            return m.mid, [p.split(".")[-1] for p in testable if r[p].get("ok") and r[p]["failures"]]

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for mid, killers in pool.map(kill, muts):
                g.per_mutant[mid] = killers
        finish(g, muts)
        g.status = "graded"
        return g
    finally:
        if not keep:
            shutil.rmtree(build, ignore_errors=True)


def finish(g: Grade, muts: list[Mutant]) -> None:
    """Raw kill rate and class-weighted score.

    Relevant mutants are grouped by the set of gold properties they violate; the
    class score averages, over these behavioural classes, the fraction of the
    class that the candidate kills. Mutants that break everything (and are caught
    by any reasonable property) then weigh as much as one subtle contract aspect.
    """
    g.killed = sum(1 for k in g.per_mutant.values() if k)
    g.score = g.killed / g.relevant if g.relevant else 0.0
    classes: dict[tuple, list[bool]] = {}
    for m in muts:
        classes.setdefault(tuple(sorted(m.killed_by_gold)), []).append(bool(g.per_mutant.get(m.mid)))
    g.classes = len(classes)
    g.class_score = (sum(sum(v) / len(v) for v in classes.values()) / len(classes)) if classes else 0.0


def baseline(t: Target, jobs: int = 6) -> Grade:
    """Score the crate's own property tests (the v1 oracle specifications, with
    their hypotheses as preconditions) exactly like a candidate."""
    g = Grade(t.id + " [upstream]", "harness_error")
    props = list(t.upstream_props)
    g.properties = [p.split(".")[-1] for p in props]
    lp = exec_lean_path()
    imports = list(t.upstream_imports)
    out = run_driver(driver(imports, [(p, TRUTH_N, TRUTH_SEED) for p in props]), lp)
    res = parse_results(out)
    testable = [p for p in props if res.get(p, {}).get("ok") and not res[p]["failures"]]
    for p in props:
        r = res.get(p, {"ok": False, "error": out[-500:]})
        if not r.get("ok"):
            g.untestable[p.split(".")[-1]] = r.get("error", "")[:300]
        elif r["failures"]:
            g.false_properties[p.split(".")[-1]] = r["failures"]
    muts = [m for m in load_mutants(t) if m.status == "relevant"]
    g.relevant = len(muts)
    work = CACHE / t.slug / "mutants"

    def kill(m: Mutant) -> tuple[str, list[str]]:
        o = run_driver(driver(imports, [(p, KILL_N, KILL_SEED) for p in testable]),
                       f"{work / m.mid / 'olean'}:{lp}", 600)
        r = parse_results(o)
        return m.mid, [p.split(".")[-1] for p in testable if r.get(p, {}).get("ok") and r[p]["failures"]]

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for mid, killers in pool.map(kill, muts):
            g.per_mutant[mid] = killers
    finish(g, muts)
    g.status = "graded" if testable else "no_properties"
    return g


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.v2")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("prepare"); p.add_argument("targets"); p.add_argument("--mutants", type=int, default=60)
    p.add_argument("--jobs", type=int, default=6); p.add_argument("--no-sync", action="store_true")
    c = sub.add_parser("check-gold"); c.add_argument("targets")
    q = sub.add_parser("grade"); q.add_argument("target"); q.add_argument("file"); q.add_argument("--jobs", type=int, default=6)
    b = sub.add_parser("baseline"); b.add_argument("targets"); b.add_argument("--jobs", type=int, default=6)
    args = ap.parse_args(argv)
    if args.cmd in ("prepare", "check-gold"):
        sync_v2()
        for t in select(args.targets):
            ok, out = exec_build(["Benchmark.Exec.Driver", t.gold_module, *t.raw.get("upstream_imports", [])])
            if not ok:
                print(out)
                return 1
            if args.cmd == "check-gold":
                print(check_gold(t))
            else:
                prepare(t, args.mutants, args.jobs)
    elif args.cmd == "grade":
        t = load_targets()[args.target]
        g = grade(t, Path(args.file).read_text(encoding="utf-8"), jobs=args.jobs)
        print(json.dumps(g.to_json(), indent=1))
    elif args.cmd == "baseline":
        for t in select(args.targets):
            g = baseline(t, jobs=args.jobs)
            print(json.dumps({k: v for k, v in g.to_json().items() if k != "per_mutant"}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
