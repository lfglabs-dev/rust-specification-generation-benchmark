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
import functools
import os
import shutil
import subprocess
import sys
from pathlib import Path

from . import ROOT

EXEC_ROOT = Path(os.environ.get("RSGB_EXEC_ROOT", str(ROOT / ".lake" / "exec")))
MARK = "-- (rsgb-exec) noncomputable section removed"


def sync(exec_root: Path = EXEC_ROOT, source_root: Path = ROOT) -> None:
    exec_root.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["rsync", "-a", "--delete", "--exclude", ".lake", "--exclude", "results", "--exclude", ".git",
         f"{source_root}/", f"{exec_root}/"],
        check=True,
    )
    (exec_root / ".lake").mkdir(exist_ok=True)
    pk = exec_root / ".lake" / "packages"
    if not pk.exists():
        pk.symlink_to(source_root / ".lake" / "packages")
    for f in (exec_root / "extracted").rglob("*.lean"):
        text = f.read_text(encoding="utf-8")
        if "\nnoncomputable section\n" in text:
            f.write_text(text.replace("\nnoncomputable section\n", f"\n{MARK}\n"), encoding="utf-8")
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


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.exec")
    ap.add_argument("cmd", choices=["sync", "build", "path"])
    ap.add_argument("modules", nargs="*")
    args = ap.parse_args(argv)
    if args.cmd == "sync":
        sync()
        print(f"synced {EXEC_ROOT}")
    elif args.cmd == "path":
        print(lean_path())
    else:
        ok, out = build(args.modules or ["Extracted", "Benchmark.Exec.Driver"])
        print(out)
        return 0 if ok else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
