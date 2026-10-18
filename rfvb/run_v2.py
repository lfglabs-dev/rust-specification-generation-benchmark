"""Run the v2 specification-design agent on targets and grade the results.

  python -m rfvb.run_v2 --model M --base-url URL --api-key-env VAR --targets all|id,id [--jobs 2]

Results: one JSON line per target in results/<run>.jsonl, logs under results/<run>/<target>/.
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path

from . import ROOT
from .agent import BUDGETS
from .transport import ChatConfig
from .v2 import Target, grade, grade_task, select
from .v2_agent import V2Runner, build_v2_workspace


def run_one(t: Target, run_dir: Path, cfg: ChatConfig, budget: str, grade_jobs: int, mode: str = "whitebox") -> dict:
    art = run_dir / t.slug
    if art.exists():
        shutil.rmtree(art)
    art.mkdir(parents=True)
    ws = run_dir / "_workspaces" / t.slug
    started = time.time()
    if t.variant:
        mode = "blackbox"  # audit tasks: bodies hidden, the bug must be found from behaviour vs. the docs
    build_v2_workspace(t, ws, mode)
    runner = V2Runner(t, ws, cfg, BUDGETS[budget], art)
    res = runner.run()
    final = (ws / t.candidate_file).read_text(encoding="utf-8")
    (art / "final.lean").write_text(final, encoding="utf-8")
    from .slots import slot
    with slot("grade", int(os.environ.get("RSGB_GRADE_SLOTS", "2"))):
        g = grade_task(t, final, runner.reports, jobs=grade_jobs)
    (art / "grade.json").write_text(json.dumps(g.to_json(), indent=1), encoding="utf-8")
    shutil.rmtree(ws, ignore_errors=True)
    return {
        "target": t.id,
        "model": cfg.model,
        "budget": budget,
        "mode": mode,
        "submitted": res.status == "solved",
        "status": g.status,
        "family": t.family,
        "task_score": round(g.task_score, 4),
        "detected": getattr(g, "detected", None),
        "report_valid": getattr(g, "report_valid", None),
        "false_alarm": getattr(g, "false_alarm", None),
        "reports": len(runner.reports),
        "class_score": round(g.class_score, 4),
        "kill_rate": round(g.score, 4),
        "killed": g.killed,
        "relevant": g.relevant,
        "classes": g.classes,
        "properties": g.properties,
        "false_properties": list(g.false_properties),
        "overspecified": list(g.overspecified),
        "untestable": list(g.untestable),
        "detail": g.detail[:1500],
        "agent": asdict(res) | {"final_candidate": None},
        "wall_seconds": round(time.time() - started, 1),
    }


def regrade(path: Path, grade_jobs: int, only: set[str] | None = None) -> int:
    from .v2 import load_targets
    from .v2 import all_tasks
    targets = all_tasks()
    rows = [json.loads(l) for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]
    run_dir = path.with_suffix("")
    out = []
    for r in rows:
        t = targets.get(r["target"])
        final = run_dir / t.slug / "final.lean" if t else None
        if t is None or not final.is_file() or (only and r["target"] not in only):
            out.append(r)
            continue
        reps = run_dir / t.slug / "bug_reports.json"
        reports = json.loads(reps.read_text()) if reps.is_file() else []
        g = grade_task(t, final.read_text(encoding="utf-8"), reports, jobs=grade_jobs)
        (run_dir / t.slug / "grade.json").write_text(json.dumps(g.to_json(), indent=1), encoding="utf-8")
        r.update({"status": g.status, "family": t.family, "task_score": round(g.task_score, 4),
                  "detected": getattr(g, "detected", None), "report_valid": getattr(g, "report_valid", None),
                  "false_alarm": getattr(g, "false_alarm", None),
                  "class_score": round(g.class_score, 4), "kill_rate": round(g.score, 4),
                  "killed": g.killed, "relevant": g.relevant, "classes": g.classes, "properties": g.properties,
                  "false_properties": list(g.false_properties), "overspecified": list(g.overspecified),
                  "untestable": list(g.untestable), "detail": g.detail[:1500]})
        print(f"{t.id}: {g.status} class={g.class_score:.3f} kill={g.score:.3f}", flush=True)
        out.append(r)
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in out), encoding="utf-8")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.run_v2")
    ap.add_argument("--model", required=True)
    ap.add_argument("--base-url", required=True)
    ap.add_argument("--api-key-env", default="OPENAI_API_KEY")
    ap.add_argument("--targets", default="all")
    ap.add_argument("--budget", default="normal", choices=sorted(BUDGETS))
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--grade-jobs", type=int, default=3)
    ap.add_argument("--run")
    ap.add_argument("--temperature", type=float, default=None)
    ap.add_argument("--max-tokens", type=int, default=16384)
    ap.add_argument("--stream", action="store_true")
    ap.add_argument("--mode", default="whitebox", choices=["whitebox", "blackbox"])
    ap.add_argument("--regrade", metavar="RUN_JSONL", help="re-grade the final.lean files of an existing run "
                    "(after mutants were re-prepared) and rewrite its rows; no model calls")
    args = ap.parse_args(argv)
    if args.regrade:
        only = None if args.targets == "all" else set(args.targets.split(","))
        return regrade(Path(args.regrade), args.grade_jobs, only)
    targets = select(args.targets)
    run = args.run or f"v2-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{args.model.replace('/', '_')}"
    run_dir = ROOT / "results" / run
    run_dir.mkdir(parents=True, exist_ok=True)
    out_path = ROOT / "results" / f"{run}.jsonl"
    cfg = ChatConfig(base_url=args.base_url, model=args.model, api_key=os.environ.get(args.api_key_env),
                     temperature=args.temperature, max_tokens=args.max_tokens, timeout=900, stream=args.stream)
    done = set()
    if out_path.exists():
        done = {json.loads(l)["target"] for l in out_path.read_text().splitlines() if l.strip()}
    todo = [t for t in targets if t.id not in done]
    lock = threading.Lock()

    def work(t: Target) -> None:
        try:
            row = run_one(t, run_dir, cfg, args.budget, args.grade_jobs, args.mode)
        except Exception as exc:
            import traceback
            row = {"target": t.id, "model": args.model, "status": "harness_error", "class_score": 0.0,
                   "kill_rate": 0.0, "detail": traceback.format_exc()[-2000:]}
        with lock:
            with out_path.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(f"{t.id}: {row['status']} task={row.get('task_score')} class={row.get('class_score')} kill={row.get('kill_rate')} "
                  f"props={len(row.get('properties') or [])} false={row.get('false_properties')}", flush=True)

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        list(pool.map(work, todo))
    shutil.rmtree(run_dir / "_workspaces", ignore_errors=True)
    rows = [json.loads(l) for l in out_path.read_text().splitlines() if l.strip()]
    mean = sum(r.get("task_score", r.get("class_score", 0)) for r in rows) / max(1, len(rows))
    print(f"\n{run}: mean task score {mean:.3f} over {len(rows)} tasks -> {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
