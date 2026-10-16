"""Mutation-based specification strength (RSGB v2).

A *mutant* is a copy of the executable extraction with one small textual change
inside one of the target definitions (functions under test and the crate
functions they call). The grader keeps the mutants that

  1. compile,
  2. are observably different from the original implementation (differential
     testing of the target functions on the shared input generator), and
  3. violate the hidden gold specification of the target (so the change breaks
     the intended contract rather than unspecified behaviour),

and scores a candidate specification by the fraction of those mutants on which
at least one of its properties is falsified.

Mutant builds reuse every compiled module of the executable benchmark copy
(`exec_root`, see `exec.py`) and only recompile the mutated `Funs.lean` into a
private olean tree that shadows the original package on `LEAN_PATH`.
"""
from __future__ import annotations

import hashlib
import json
import random
import re
import shutil
import subprocess
from dataclasses import asdict, dataclass, field
from pathlib import Path

DECL_HDR = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:partial\s+)?def\s+([^\s:(]+)")

# (operator class, regex, replacement). Applied to one occurrence at a time.
OPERATORS: list[tuple[str, str, str]] = [
    ("arith", r" \+ ", " - "),
    ("arith", r" - ", " + "),
    ("arith", r" \* ", " + "),
    ("arith", r" / ", " * "),
    ("arith", r" % ", " / "),
    ("bitwise", r" &&& ", " ||| "),
    ("bitwise", r" \|\|\| ", " &&& "),
    ("bitwise", r" \^\^\^ ", " ||| "),
    ("shift", r" <<< ", " >>> "),
    ("shift", r" >>> ", " <<< "),
    ("compare", r" < ", " <= "),
    ("compare", r" <= ", " < "),
    ("compare", r" > ", " >= "),
    ("compare", r" >= ", " > "),
    ("compare", r" = ", " != "),
    ("compare", r" != ", " = "),
    ("method", r"wrapping_add", "wrapping_sub"),
    ("method", r"wrapping_sub", "wrapping_add"),
    ("method", r"overflowing_add", "overflowing_sub"),
    ("method", r"overflowing_sub", "overflowing_add"),
    ("method", r"to_le_bytes", "to_be_bytes"),
    ("method", r"to_be_bytes", "to_le_bytes"),
    ("method", r"from_le_bytes", "from_be_bytes"),
    ("method", r"from_be_bytes", "from_le_bytes"),
    ("method", r"rotate_left", "rotate_right"),
    ("method", r"rotate_right", "rotate_left"),
    ("method", r"leading_zeros", "trailing_zeros"),
    ("method", r"trailing_zeros", "leading_zeros"),
    ("control", r"\bif (.+) then$", r"if ¬ (\1) then"),
    ("control", r"\bmassert \((.+)\)$", "ok ()"),
]
LITERAL = re.compile(r"\b(\d+)#(u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)\b")


@dataclass
class Mutant:
    mid: str
    decl: str
    line: int  # 1-based line in Funs.lean
    op: str
    before: str
    after: str
    status: str = "new"  # new | compile_error | equivalent | unspecified | relevant
    extra: list = field(default_factory=list)  # further [line, before, after] edits (hand-written bugs)
    note: str = ""
    differing_inputs: int = 0
    killed_by_gold: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        return asdict(self)


def decl_ranges(text: str) -> list[tuple[str, int, int]]:
    """(name, first body line, last line) for every `def` in an Aeneas Funs.lean (1-based)."""
    lines = text.splitlines()
    ns = ""
    m = re.search(r"^namespace\s+(\S+)", text, re.M)
    if m:
        ns = m.group(1) + "."
    starts = []
    for i, l in enumerate(lines):
        mm = DECL_HDR.match(l)
        if mm:
            starts.append((ns + mm.group(1), i))
        elif re.match(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:partial\s+)?def\s*$", l) and i + 1 < len(lines):
            # Aeneas puts long names on the next line: `def\n  name …`
            name = lines[i + 1].strip().split()[0] if lines[i + 1].strip() else ""
            if name:
                starts.append((ns + name, i))
    out = []
    for k, (name, i) in enumerate(starts):
        end = starts[k + 1][1] - 1 if k + 1 < len(starts) else len(lines) - 1
        # stop before the next docstring
        j = i + 1
        while j <= end and not lines[j].startswith("/--"):
            j += 1
        out.append((name, i + 1, j))  # body lines i+1 .. j-1 (0-based) -> 1-based i+2 .. j
    return out


def cone(text: str, roots: list[str]) -> set[str]:
    """Target definitions: `roots` and every definition of the same file they (transitively) mention."""
    lines = text.splitlines()
    ranges = decl_ranges(text)
    body = {n: "\n".join(lines[a - 1 : b]) for n, a, b in ranges}
    ns = ""
    m = re.search(r"^namespace\s+(\S+)", text, re.M)
    if m:
        ns = m.group(1) + "."
    short = {n: n[len(ns):] if n.startswith(ns) else n for n in body}
    seen: set[str] = set()
    todo = [r for r in roots if r in body]
    missing = [r for r in roots if r not in body]
    if missing:
        raise KeyError(f"unknown target definitions: {missing}")
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        for other, sh in short.items():
            if other not in seen and re.search(r"(?<![\w.])" + re.escape(sh) + r"(?![\w])", body[n]):
                todo.append(other)
    return seen


def candidates(text: str, targets: set[str], literal_per_decl: int = 6) -> list[Mutant]:
    lines = text.splitlines()
    out: list[Mutant] = []
    for name, start0, stop0 in decl_ranges(text):
        if name not in targets:
            continue
        lits = 0
        for i in range(start0, stop0):
            line = lines[i]
            code = line.split("--", 1)[0]
            if not code.strip() or code.lstrip().startswith(("/-", "Source:", "Visibility:")):
                continue
            for op, pat, rep in OPERATORS:
                for m in re.finditer(pat, code):
                    new = code[: m.start()] + m.expand(rep) + code[m.end():]
                    if new != code:
                        out.append(Mutant("", name, i + 1, op, line, new + line[len(code):]))
            for m in LITERAL.finditer(code):
                if lits >= literal_per_decl:
                    break
                n = int(m.group(1))
                for v in {n + 1, n - 1} if n > 0 else {1}:
                    new = code[: m.start()] + f"{v}#{m.group(2)}" + code[m.end():]
                    out.append(Mutant("", name, i + 1, "literal", line, new + line[len(code):]))
                lits += 1
    for m in out:
        m.mid = hashlib.sha1(f"{m.line}:{m.after}".encode()).hexdigest()[:10]
    # dedupe
    seen, uniq = set(), []
    for m in out:
        if m.mid not in seen:
            seen.add(m.mid)
            uniq.append(m)
    return uniq


def sample(cands: list[Mutant], k: int, seed: int = 0) -> list[Mutant]:
    """Stratified sample: round-robin over operator classes, deterministic."""
    rng = random.Random(seed)
    by: dict[str, list[Mutant]] = {}
    for m in cands:
        by.setdefault(m.op, []).append(m)
    for v in by.values():
        rng.shuffle(v)
    out: list[Mutant] = []
    keys = sorted(by)
    while len(out) < k and any(by.values()):
        for key in keys:
            if by[key] and len(out) < k:
                out.append(by[key].pop())
    return out


def apply(text: str, m: Mutant) -> str:
    lines = text.splitlines(keepends=True)
    for line, before, after in [(m.line, m.before, m.after), *m.extra]:
        nl = "\n" if lines[line - 1].endswith("\n") else ""
        assert lines[line - 1].rstrip("\n") == before, (m.mid, lines[line - 1], before)
        lines[line - 1] = after + nl
    return "".join(lines)


class MutantBuilder:
    """Builds mutant olean trees under `work/<mid>/olean` for one Lean package."""

    def __init__(self, exec_root: Path, package: str, work: Path, lean_path: str):
        self.exec_root, self.package, self.work, self.lean_path = exec_root, package, work, lean_path
        self.funs_rel = Path(package) / "Extraction" / "Funs.lean"
        self.original = (exec_root / "extracted" / self.funs_rel).read_text(encoding="utf-8")

    def build(self, m: Mutant, timeout: int = 600) -> tuple[bool, str]:
        d = self.work / m.mid
        text = apply(self.original, m)
        key = hashlib.sha256(text.encode()).hexdigest()
        if (d / "ok").is_file() and (d / "ok").read_text() == key:
            return True, ""
        if d.exists():
            shutil.rmtree(d)
        src = d / "src" / self.funs_rel
        src.parent.mkdir(parents=True)
        src.write_text(text, encoding="utf-8")
        olean_pkg = d / "olean" / self.package
        olean_pkg.parent.mkdir(parents=True)
        subprocess.run(["cp", "-rs", str(self.exec_root / ".lake/build/lib/lean" / self.package), str(olean_pkg.parent)], check=True)
        out_olean = olean_pkg / "Extraction" / "Funs.olean"
        for suffix in (".olean", ".ilean", ".ir", ".c", ".hash", ".trace", ".olean.hash", ".ilean.hash"):
            p = olean_pkg / "Extraction" / ("Funs" + suffix)
            if p.is_symlink() or p.exists():
                p.unlink()
        from .slots import slot
        try:
            with slot("lean", LEAN_SLOTS):
                proc = subprocess.run(
                    ["timeout", "-k", "10", str(timeout), "lean", f"--root={d / 'src'}", "-o", str(out_olean), "-i", str(out_olean.with_suffix(".ilean")),
                     str(src)],
                    cwd=self.exec_root, env=_env(self.lean_path), capture_output=True, text=True, timeout=timeout,
                )
        except subprocess.TimeoutExpired:
            return False, "timeout"
        ok = proc.returncode == 0 and out_olean.is_file()
        if ok:
            (d / "ok").write_text(key)
        return ok, (proc.stdout + proc.stderr)[-2000:]

    def lean_path_for(self, m: Mutant | None) -> str:
        if m is None:
            return self.lean_path
        return f"{self.work / m.mid / 'olean'}:{self.lean_path}"


def _env(lean_path: str) -> dict:
    import os
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path
    return env


LEAN_SLOTS = int(__import__("os").environ.get("RSGB_LEAN_SLOTS", "8"))


def run_lean_file(exec_root: Path, lean_path: str, path: Path, timeout: int = 900) -> str:
    from .slots import slot
    with slot("lean", LEAN_SLOTS):
        try:
            proc = subprocess.run(["timeout", "-k", "10", str(timeout), "lean", str(path)], cwd=exec_root, env=_env(lean_path),
                                  capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "RSGB_TIMEOUT"
    if proc.returncode in (124, 137):
        return "RSGB_TIMEOUT"
    return proc.stdout + proc.stderr


def parse_results(out: str) -> dict[str, dict]:
    res: dict[str, dict] = {}
    for line in out.splitlines():
        line = line.strip()
        for tag in ("RSGB_RESULT ", "RSGB_ERROR "):
            i = line.find(tag)
            if i >= 0:
                try:
                    d = json.loads(line[i + len(tag):])
                except json.JSONDecodeError:
                    continue
                d["ok"] = tag == "RSGB_RESULT "
                res[d["name"]] = d
    return res


def parse_outputs(out: str) -> dict[str, list[str]]:
    res: dict[str, list[str]] = {}
    for line in out.splitlines():
        i = line.find("RSGB_OUTPUTS ")
        if i >= 0:
            parts = line[i + len("RSGB_OUTPUTS "):].split()
            res[parts[0]] = parts[1:]
    return res
