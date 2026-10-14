"""Run every shipped reference specification (or every blank skeleton) through the verifier.

  python -m rfvb.check_references [--tasks SELECTOR] [--jobs 4] [--skeletons] [--json out.json]

Reference specifications must all pass; with --skeletons, every shipped editable file
(the blank task with `True`) must be rejected.
"""
from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor

from . import ROOT
from .tasks import select_tasks
from .verifier import verify_task


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.check_references")
    ap.add_argument("--tasks", default="all")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--skeletons", action="store_true", help="submit the blank editable files instead")
    ap.add_argument("--json")
    args = ap.parse_args(argv)
    tasks = select_tasks(args.tasks)

    def one(task):
        f = task.editable_file if args.skeletons else task.reference_file
        return verify_task(task, ROOT / f, timeout_seconds=args.timeout)

    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for task, res in zip(tasks, pool.map(one, tasks)):
            results.append(res)
            print(f"{res.status:28} {res.duration_seconds:8.1f}s  {task.id}  axioms={res.axioms}", flush=True)
            if res.passed == args.skeletons:
                print("    " + res.detail.replace("\n", "\n    ")[:3000], flush=True)
    passed = sum(r.passed for r in results)
    if args.skeletons:
        print(f"\nblank skeletons rejected: {len(results) - passed}/{len(results)}")
        ok = passed == 0
    else:
        print(f"\nreference specifications passing: {passed}/{len(results)}")
        ok = passed == len(results)
    if args.json:
        with open(args.json, "w") as fh:
            json.dump([r.to_json() for r in results], fh, indent=2)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
