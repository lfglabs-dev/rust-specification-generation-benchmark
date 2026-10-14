"""Verify one submission: `python -m rfvb.verify <task_id> <spec.lean>`.

Prints a JSON object {task_id, pass, status, detail, axioms, z3, ...}; exit code 0
iff the submission passed.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .tasks import get_task
from .verifier import verify_task


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.verify", description=__doc__)
    ap.add_argument("task_id", help="task id <project>/<case>/<task> (see tasks.jsonl)")
    ap.add_argument("spec", type=Path, help="complete replacement for the task's editable Lean file")
    ap.add_argument("--timeout", type=int, default=900, help="seconds per Lean step (default 900)")
    ap.add_argument("--keep", action="store_true", help="keep the temporary verification directory")
    args = ap.parse_args(argv)
    res = verify_task(get_task(args.task_id), args.spec.resolve(), timeout_seconds=args.timeout, keep=args.keep)
    print(json.dumps(res.to_json(), indent=2, ensure_ascii=False))
    return 0 if res.passed else 1


if __name__ == "__main__":
    sys.exit(main())
