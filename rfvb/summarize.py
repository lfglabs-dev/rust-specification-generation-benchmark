"""Summarise run results into a Markdown table.

  python -m rfvb.summarize results/<run>.jsonl [...]

For each task the last valid row counts. Rows whose agent stopped for an
infrastructure reason (provider_error, harness_error, context_overflow) or
whose verifier reported harness_error are not results; such tasks are
listed as missing.
"""
from __future__ import annotations

import json
import statistics
import sys
from pathlib import Path

from .tasks import load_tasks

INFRA = {"provider_error", "harness_error", "context_overflow"}
LEVELS = ("easy", "medium", "hard")


def summarize(path: Path) -> dict:
    counts = {lvl: sum(1 for t in load_tasks() if t.difficulty == lvl) for lvl in LEVELS}
    rows: dict[str, dict] = {}
    model = budget = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        model, budget = r.get("model", model), r.get("budget", budget)
        agent = r.get("agent") or {}
        if r.get("verifier_status") == "harness_error" or agent.get("status") in INFRA:
            continue
        rows[r["task_id"]] = r
    solved = {lvl: sum(1 for r in rows.values() if r["pass"] and r["difficulty"] == lvl) for lvl in LEVELS}
    usage = [((r.get("agent") or {}).get("usage") or {}) for r in rows.values()]
    walls = [r.get("wall_seconds", 0) for r in rows.values()]
    return {
        "run": path.stem, "model": model, "budget": budget, "valid": len(rows),
        "solved": sum(solved.values()), "solved_by_difficulty": solved, "tasks_by_difficulty": counts,
        "prompt_tokens": sum(u.get("prompt_tokens", 0) for u in usage),
        "completion_tokens": sum(u.get("completion_tokens", 0) for u in usage),
        "median_wall_seconds": statistics.median(walls) if walls else 0,
    }


def main(argv: list[str] | None = None) -> int:
    paths = [Path(p) for p in (argv if argv is not None else sys.argv[1:])]
    if not paths:
        print(__doc__)
        return 2
    print("| model | solved | easy | medium | hard | valid | prompt tok | completion tok | median time |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for p in paths:
        s = summarize(p)
        d, n = s["solved_by_difficulty"], s["tasks_by_difficulty"]
        print(f"| {s['model']} | **{s['solved']}**/100 | {d['easy']}/{n['easy']} | {d['medium']}/{n['medium']} | "
              f"{d['hard']}/{n['hard']} | {s['valid']} | {s['prompt_tokens'] / 1e6:.0f}M | "
              f"{s['completion_tokens'] / 1e6:.1f}M | {s['median_wall_seconds'] / 60:.0f} min |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
