"""Executable copy of the benchmark (grader-side only).

The verbatim extraction is wrapped in `noncomputable section`, so the Lean
compiler never generates code for it. The grader keeps a private copy of the
repository (`exec_root`, default `<repo>/.lake/exec`) in which that line is
removed, so the extracted Rust functions can be *run* by the specification
testing runtime (`Benchmark/Exec`). The copy shares `.lake/packages` with the
main checkout and has its own build directory.

Crates whose extraction declares external functions as axioms get grader-side
implementations from `exec_shims/<Package>/...` (overlaid on the copy).

  python -m rfvb.exec sync      # (re)create the copy from the repository
  python -m rfvb.exec build [modules...]
"""
from __future__ import annotations

import argparse
import json
import re
import functools
import os
import shutil
import subprocess
import sys
from pathlib import Path

from . import ROOT

EXEC_ROOT = Path(os.environ.get("RSGB_EXEC_ROOT", str(ROOT / ".lake" / "exec")))
MARK = "-- (rsgb-exec) noncomputable section removed"
# Do not export small function bodies for cross-module inlining: callers (gold
# specs, candidates, drivers) compiled against the original extraction would
# otherwise keep the original body of tiny wrappers and never see a mutant.
NO_INLINE = "set_option compiler.small 0"


# Grader-side implementations of external functions that the extraction declares
# as axioms (keyed by Lean package, then axiom name). Any other axiom gets a body
# that panics, so the module compiles; targets never exercise those.
GOLDILOCKS_P = 18446744069414584321
AXIOM_IMPLS: dict[str, dict[str, str]] = {
    "MemchrTwoway": {
        "arch.all.is_equal":
            "def arch.all.is_equal (x y : Slice Std.U8) : RustM Bool := RustM.ok (decide (x.val = y.val))",
    },
    "GoldilocksField": {
        "utils.branch_hint": "def utils.branch_hint : RustM Unit := RustM.ok ()",
        "field.algo.generic.inv_ebgcd": (
            "def rsgbPowMod (b e m : Nat) : Nat :=\n"
            "  ((List.range 64).foldl (fun (acc : Nat × Nat) i =>\n"
            "    let (r, x) := acc\n"
            "    ((if (e >>> i) % 2 = 1 then r * x % m else r), x * x % m)) (1 % m, b % m)).1\n"
            "def field.algo.generic.inv_ebgcd (a : Std.U64) : RustM Std.U64 :=\n"
            f"  if a.val ≥ {GOLDILOCKS_P} then RustM.fail .panic\n"
            "  else if a.val = 0 then RustM.ok ⟨0#64⟩\n"
            f"  else RustM.ok ⟨BitVec.ofNat 64 (rsgbPowMod a.val ({GOLDILOCKS_P} - 2) {GOLDILOCKS_P})⟩"),
    },
}
for _w, _ty in (("U8", "Std.U8"), ("U16", "Std.U16"), ("U32", "Std.U32"), ("U64", "Std.U64"),
                ("U128", "Std.U128"), ("Usize", "Std.Usize")):
    # Rust's `next_power_of_two` (debug build: panics when the result overflows)
    AXIOM_IMPLS.setdefault("DashuBase", {})[f"{_w}.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two"] = (
        f"def {_w}.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two (x : {_ty}) : RustM {_ty} :=\n"
        f"  let n := (List.range (UScalarTy.{_w}.numBits + 1)).find? (fun k => x.val ≤ 2 ^ k)\n"
        f"  match n with\n"
        f"  | some k => if k < UScalarTy.{_w}.numBits then RustM.ok ⟨BitVec.ofNat _ (2 ^ k)⟩ else RustM.fail .panic\n"
        f"  | none => RustM.fail .panic")


# jiff_core::bounds::*::checkc: inclusive range checks (jiff's documented ranges).
for _k, _ty, _lo, _hi in (("Hour", "Std.I8", 0, 23), ("Minute", "Std.I8", 0, 59), ("Second", "Std.I8", 0, 59),
                          ("SubsecNanosecond", "Std.I32", 0, 999999999), ("Millisecond", "Std.I16", 0, 999),
                          ("Microsecond", "Std.I16", 0, 999), ("Nanosecond", "Std.I16", 0, 999),
                          ("CivilDaySecond", "Std.I32", 0, 86399),
                          ("CivilDayNanosecond", "Std.I64", 0, 86399999999999),
                          ("Year", "Std.I16", -9999, 9999), ("Month", "Std.I8", 1, 12)):
    AXIOM_IMPLS.setdefault("JiffCivil", {})[f"bounds.{_k}.checkc"] = (
        f"def bounds.{_k}.checkc (v : Std.I64) : RustM (core.result.Result {_ty} bounds.BoundsError) :=\n"
        f"  if ({_lo} : Int) ≤ v.val ∧ v.val ≤ ({_hi} : Int) then RustM.ok (core.result.Result.Ok ⟨BitVec.ofInt _ v.val⟩)\n"
        f"  else RustM.ok (core.result.Result.Err {{ kind := bounds.BoundsErrorKind.{_k} () }})")


def implement_axioms(text: str, pkg: str) -> str:
    """Replace `axiom NAME : TYPE` blocks by grader implementations (or a panicking default)."""
    impls = AXIOM_IMPLS.get(pkg, {})
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        m = re.match(r"^axiom\s+(\S+)", lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() and not lines[j].startswith(("/--", "axiom", "def", "end ")):
            j += 1
        block = "\n".join(lines[i:j])
        name = m.group(1)
        if name in impls:
            out.append(impls[name])
        else:
            out.append("def" + block[len("axiom"):] + " := default")
        i = j
    return "\n".join(out)


def add_noinline(text: str) -> str:
    """Mark every top-level `def` `@[noinline]` (merging into an existing attribute list)."""
    lines = text.split("\n")
    out = []
    for i, line in enumerate(lines):
        prev = out[-1] if out else ""
        if line.startswith("@[") and "noinline" not in line and (
                re.match(r"^@\[[^\]]*\]\s*(def\b.*)?$", line)):
            line = "@[noinline, " + line[2:]
        elif re.match(r"^def(\s|$)", line) and not prev.rstrip().endswith("]"):
            line = "@[noinline] " + line
        out.append(line)
    return "\n".join(out)


def transform_tree(tree: Path, extracted_root: Path) -> None:
    """Make an extraction tree executable (in place): implement axioms, drop `noncomputable
    section`, forbid cross-module inlining, raise the recursion limit."""
    for f in tree.rglob("*.lean"):
        text = f.read_text(encoding="utf-8")
        orig = text
        if "/Assumptions/" in str(f) and re.search(r"^axiom\s", text, re.M):
            text = implement_axioms(text, f.relative_to(extracted_root).parts[0])
        text = text.replace("set_option maxRecDepth 2048", "set_option maxRecDepth 100000")
        if "\nnoncomputable section\n" in text:
            text = text.replace("\nnoncomputable section\n", f"\n{MARK}\n{NO_INLINE}\n")
            # Callers (gold specs, candidates, drivers) are compiled once against the original
            # extraction; inlining an extracted body into them would hide mutants of it.
            text = add_noinline(text)
        if text != orig:
            f.write_text(text, encoding="utf-8")


def add_package(pkg: str, exec_root: Path = EXEC_ROOT, source_root: Path = ROOT) -> tuple[bool, str]:
    """Add (or refresh) one extracted package in the executable copy and build it, under the build lock."""
    import fcntl
    lock = exec_root / ".lake" / "build.lock"
    with open(lock, "w") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        shutil.copy2(source_root / "lakefile.lean", exec_root / "lakefile.lean")
        dst = exec_root / "extracted" / pkg
        subprocess.run(["rsync", "-a", "--delete", f"{source_root / 'extracted' / pkg}/", f"{dst}/"], check=True)
        transform_tree(dst, exec_root / "extracted")
        shim = source_root / "exec_shims" / pkg
        if shim.is_dir():
            subprocess.run(["rsync", "-a", f"{shim}/", f"{dst}/"], check=True)
        proc = subprocess.run(["lake", "build", f"{pkg}.Extraction.Funs"], cwd=exec_root, capture_output=True,
                              text=True, timeout=7200)
        if proc.returncode:
            return False, (proc.stdout + proc.stderr)[-6000:]
    # instances (builds under the lock itself, module by module)
    rep = gen_instances(exec_root, source_root, only=pkg)
    if shim.is_dir():
        subprocess.run(["rsync", "-a", f"{shim}/", f"{dst}/"], check=True)
    with open(lock, "w") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        proc = subprocess.run(["lake", "build", f"{pkg}.Extraction"], cwd=exec_root, capture_output=True,
                              text=True, timeout=7200)
    return proc.returncode == 0, json.dumps(rep) + "\n" + (proc.stdout + proc.stderr)[-4000:]


def sync(exec_root: Path = EXEC_ROOT, source_root: Path = ROOT) -> None:
    exec_root.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["rsync", "-a", "--delete", "--exclude", ".lake", "--exclude", "results", "--exclude", ".git",
         "--exclude", ".rsgb_drivers",
         f"{source_root}/", f"{exec_root}/"],
        check=True,
    )
    (exec_root / ".lake").mkdir(exist_ok=True)
    pk = exec_root / ".lake" / "packages"
    if not pk.exists():
        pk.symlink_to(source_root / ".lake" / "packages")
    transform_tree(exec_root / "extracted", exec_root / "extracted")
    shims = source_root / "exec_shims"
    if shims.is_dir():
        subprocess.run(["rsync", "-a", f"{shims}/", f"{exec_root / 'extracted'}/"], check=True)


@functools.lru_cache(maxsize=None)
def lean_path(exec_root: Path = EXEC_ROOT) -> str:
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=exec_root,
                         capture_output=True, text=True, check=True)
    return out.stdout.strip()


def sync_v2(exec_root: Path = EXEC_ROOT, source_root: Path = ROOT) -> None:
    """Copy only the (small) v2 / runtime sources into the executable copy."""
    for rel in ("Benchmark/V2", "Benchmark/Exec"):
        (exec_root / rel).mkdir(parents=True, exist_ok=True)
        subprocess.run(["rsync", "-a", f"{source_root / rel}/", f"{exec_root / rel}/"], check=True)
    shims = source_root / "exec_shims"
    if shims.is_dir():
        subprocess.run(["rsync", "-a", f"{shims}/", f"{exec_root / 'extracted'}/"], check=True)


def build(modules: list[str], exec_root: Path = EXEC_ROOT, timeout: int = 7200) -> tuple[bool, str]:
    """`lake build` in the executable copy, serialized by a lock file (safe for concurrent callers)."""
    lock = exec_root / ".lake" / "build.lock"
    proc = subprocess.run(["flock", str(lock), "lake", "build", *modules], cwd=exec_root, capture_output=True,
                          text=True, timeout=timeout)
    return proc.returncode == 0, proc.stdout[-6000:] + proc.stderr[-3000:]


def type_names(types_lean: Path) -> list[str]:
    text = types_lean.read_text(encoding="utf-8")
    m = re.search(r"^namespace\s+(\S+)", text, re.M)
    ns = (m.group(1) + ".") if m else ""
    return [ns + n for n in re.findall(r"^(?:inductive|structure)\s+([^\s(:]+)", text, re.M)]


def gen_instances(exec_root: Path = EXEC_ROOT, source_root: Path = ROOT, rounds: int = 12,
                  only: str | None = None) -> dict:
    """Generate (and validate by building) `ExecInstances` modules deriving `DecidableEq`, `Repr`
    and `Plausible.Arbitrary` for every crate type, into `exec_shims/<Pkg>/Extraction/`."""
    report = {}
    for pkg_dir in sorted((source_root / "extracted").iterdir()):
        if only and pkg_dir.name != only:
            continue
        types = pkg_dir / "Extraction" / "Types.lean"
        if not types.is_file():
            continue
        names = type_names(types)
        if not names:
            continue
        pkg = pkg_dir.name
        lines = [f"deriving instance {cls} for {n}" for n in names for cls in ("DecidableEq", "Repr", "Plausible.Arbitrary")]
        dropped: list[str] = []
        ok = False
        for _ in range(rounds + 1):
            if _ == rounds:  # give up: no derived instances for this crate
                dropped += lines
                lines = []
            body = "\n".join(lines)
            text = (f"import {pkg}.Extraction.Types\nimport Benchmark.Exec.Runtime\n\n"
                    f"/-! Grader-side instances for the crate types (executable copy only). -/\n\n"
                    f"open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec\n\n{body}\n")
            dst = exec_root / "extracted" / pkg / "Extraction" / "ExecInstances.lean"
            dst.write_text(text, encoding="utf-8")
            ok, out = build([f"{pkg}.Extraction.ExecInstances"], exec_root)
            if ok:
                break
            bad = {int(n) for n in re.findall(r"ExecInstances\.lean:(\d+):\d+", out)}
            if not bad:
                lines = []
                dropped.append("<all: unparsed failure>")
                continue
            first = 8  # line number of the first deriving line
            keep = []
            for i, l in enumerate(lines):
                (dropped if (first + i) in bad else keep).append(l)
            lines = keep
        shim = source_root / "exec_shims" / pkg / "Extraction"
        shim.mkdir(parents=True, exist_ok=True)
        (shim / "ExecInstances.lean").write_text(dst.read_text(encoding="utf-8"), encoding="utf-8")
        umbrella = (source_root / "extracted" / pkg / "Extraction.lean").read_text(encoding="utf-8")
        if f"import {pkg}.Extraction.ExecInstances" not in umbrella:
            umbrella = umbrella.rstrip("\n") + f"\nimport {pkg}.Extraction.ExecInstances\n"
        (source_root / "exec_shims" / pkg / "Extraction.lean").write_text(umbrella, encoding="utf-8")
        report[pkg] = {"types": len(names), "kept": len(lines), "dropped": dropped}
    return report


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.exec")
    ap.add_argument("cmd", choices=["sync", "build", "path", "instances", "add-package"])
    ap.add_argument("modules", nargs="*")
    args = ap.parse_args(argv)
    if args.cmd == "sync":
        sync()
        print(f"synced {EXEC_ROOT}")
    elif args.cmd == "path":
        print(lean_path())
    elif args.cmd == "add-package":
        for pkg in args.modules:
            ok, out = add_package(pkg)
            print(f"{pkg}: {'ok' if ok else 'FAILED'}\n{out}")
            if not ok:
                return 1
    elif args.cmd == "instances":
        import json
        print(json.dumps(gen_instances(), indent=1))
    else:
        ok, out = build(args.modules or ["Extracted", "Benchmark.Exec.Driver"])
        print(out)
        return 0 if ok else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
