"""Summarize v2 runs: per-model table (overall and per task family) and per-task table.

  python -m rfvb.summarize_v2 results/<run>.jsonl ... [--by task] [--crate-weighted]

Task families: base (specify a correct API), bug (audit: the shipped code has a real or
injected bug), clean (audit control: the shipped code is correct). `task_score` is the
per-task score (see rfvb.v2.grade_task); rows from older runs fall back to class_score.
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
                r.setdefault("family", "bug" if "@bug" in r["target"] else "clean" if "@clean" in r["target"] else "base")
                r.setdefault("task_score", r.get("class_score", 0.0) if r.get("status") == "graded" else 0.0)
                r["_run"] = Path(p).stem
                rows.append(r)
    return rows


def crate(task: str) -> str:
    return task.split("@")[0]


def mean(xs: list[float]) -> float:
    return statistics.mean(xs) if xs else float("nan")


def score(rs: list[dict], crate_weighted: bool) -> float:
    if not crate_weighted:
        return mean([r["task_score"] for r in rs])
    by = collections.defaultdict(list)
    for r in rs:
        by[crate(r["target"])].append(r["task_score"])
    return mean([mean(v) for v in by.values()])


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+")
    ap.add_argument("--by", default="model", choices=["model", "task"])
    ap.add_argument("--crate-weighted", action="store_true", help="average per crate first")
    args = ap.parse_args(argv)
    rows = load(args.files)
    if args.by == "model":
        groups = collections.defaultdict(list)
        for r in rows:
            groups[(r["model"], r["mode"])].append(r)
        print(f"{'model':32} {'mode':9} {'n':>4} {'score':>6} {'base':>6} {'bug':>6} {'clean':>6} "
              f"{'detect':>6} {'report':>6} {'falarm':>6} {'false':>5} {'props':>5}")
        for (m, mode), rs in sorted(groups.items(), key=lambda kv: -score(kv[1], args.crate_weighted)):
            fam = {f: [r for r in rs if r["family"] == f] for f in ("base", "bug", "clean")}
            bug = fam["bug"]
            det = mean([float(bool(r.get("detected"))) for r in bug])
            rep = mean([float(bool(r.get("report_valid"))) for r in bug])
            fa = mean([float(bool(r.get("false_alarm"))) for r in fam["clean"]])
            false = sum(r["status"] == "false_property" for r in rs)
            props = mean([len(r.get("properties") or []) for r in rs])
            print(f"{m:32} {mode:9} {len(rs):4} {score(rs, args.crate_weighted):6.3f} "
                  f"{score(fam['base'], args.crate_weighted) if fam['base'] else float('nan'):6.3f} "
                  f"{score(bug, args.crate_weighted) if bug else float('nan'):6.3f} "
                  f"{score(fam['clean'], args.crate_weighted) if fam['clean'] else float('nan'):6.3f} "
                  f"{det:6.2f} {rep:6.2f} {fa:6.2f} {false:5} {props:5.1f}")
    else:
        tasks = sorted({r["target"] for r in rows})
        models = sorted({(r["model"], r["mode"]) for r in rows})
        idx = {(r["target"], r["model"], r["mode"]): r for r in rows}
        print("task".ljust(44) + "".join(f"{(m.split('/')[-1][:13] + ('*' if mode == 'blackbox' else '')):>15}"
                                         for m, mode in models) + "   mean")
        for t in tasks:
            line, vals = t.ljust(44), []
            for m, mode in models:
                r = idx.get((t, m, mode))
                if r is None:
                    line += f"{'-':>15}"
                    continue
                vals.append(r["task_score"])
                cell = f"{r['task_score']:.2f}" if r["status"] == "graded" else r["status"][:10]
                if r["family"] == "bug":
                    cell += ("D" if r.get("detected") else "") + ("R" if r.get("report_valid") else "")
                line += f"{cell:>15}"
            print(line + (f"   {mean(vals):.2f}" if vals else ""))
        print("(* = black-box; D = bug detected by the spec, R = valid bug report)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
