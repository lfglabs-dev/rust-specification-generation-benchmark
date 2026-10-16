"""Summarize v2 runs: per-model and per-target tables.

  python -m rfvb.summarize_v2 results/v2-*.jsonl [--by target]
"""
from __future__ import annotations

import argparse
import collections
import json
import statistics
import sys
from pathlib import Path


def load(paths: list[str]) -> list[dict]:
    rows = []
    for p in paths:
        for line in Path(p).read_text(encoding="utf-8").splitlines():
            if line.strip():
                r = json.loads(line)
                r.setdefault("mode", "whitebox")
                r["_run"] = Path(p).stem
                rows.append(r)
    return rows


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--by", default="model", choices=["model", "target"])
    args = ap.parse_args(argv)
    rows = load(args.files)
    if args.by == "model":
        groups = collections.defaultdict(list)
        for r in rows:
            groups[(r["model"], r["mode"])].append(r)
        print(f"{'model':38} {'mode':9} {'n':>3} {'class':>6} {'kill':>6} {'graded':>6} {'false':>5} {'overspec':>8} {'noprop':>6} {'props':>5}")
        for (m, mode), rs in sorted(groups.items(), key=lambda kv: -statistics.mean(x.get("class_score", 0) for x in kv[1])):
            cls = statistics.mean(r.get("class_score", 0) for r in rs)
            kill = statistics.mean(r.get("kill_rate", 0) for r in rs)
            graded = sum(r["status"] == "graded" for r in rs)
            false = sum(r["status"] == "false_property" for r in rs)
            over = sum(bool(r.get("overspecified")) for r in rs)
            nop = sum(r["status"] in ("no_properties", "lean_error", "policy", "harness_error") for r in rs)
            props = statistics.mean(len(r.get("properties") or []) for r in rs)
            print(f"{m:38} {mode:9} {len(rs):3} {cls:6.3f} {kill:6.3f} {graded:6} {false:5} {over:8} {nop:6} {props:5.1f}")
    else:
        targets = sorted({r["target"] for r in rows})
        models = sorted({(r["model"], r["mode"]) for r in rows})
        idx = {(r["target"], r["model"], r["mode"]): r for r in rows}
        head = "target".ljust(32) + "".join(f"{(m.split('/')[-1][:14] + ('*' if mode == 'blackbox' else '')):>16}" for m, mode in models)
        print(head)
        for t in targets:
            line = t.ljust(32)
            for m, mode in models:
                r = idx.get((t, m, mode))
                if r is None:
                    line += f"{'-':>16}"
                elif r["status"] != "graded":
                    line += f"{r['status'][:14]:>16}"
                else:
                    line += f"{r['class_score']:16.2f}"
            print(line)
        print("(* = black-box mode)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
