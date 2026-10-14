"""Run the reference tool-calling agent on RSGB tasks.

  python -m rfvb.run_agent --model MODEL --base-url URL --tasks SELECTOR [options]

SELECTOR: comma-separated task ids, `all`, `easy`/`medium`/`hard`,
or a file with one task id per line. The API key is read from the environment
variable named by --api-key-env (default OPENAI_API_KEY).

Each task gets an isolated workspace; the agent's final editable specification
file is then checked by the independent verifier (rfvb.verifier) via Lean 4 + Z3.
Results: one JSON line per task in results/<run>.jsonl, logs under results/<run>/<task>/.

`--mock` replaces the model with a scripted client that submits the shipped
reference specification (no network): a smoke test of the whole pipeline.
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
from .agent import BUDGETS, Runner
from .tasks import Task, select_tasks
from .transport import ChatConfig
from .verifier import verify_task
from .workspace import build_workspace


def mock_chat_for(task: Task):
    reference = (ROOT / task.reference_file).read_text(encoding="utf-8")

    def chat(cfg, messages, tools=None):
        call = {
            "id": "mock-1",
            "type": "function",
            "function": {"name": "check_spec", "arguments": json.dumps({"spec": reference})},
        }
        return {
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": "(mock) submitting the reference specification",
                    "tool_calls": [call],
                },
                "finish_reason": "tool_calls",
            }],
            "usage": {"prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0},
        }
    return chat


def slug(task: Task) -> str:
    return task.id.replace("/", "__")


def run_one(task: Task, run_dir: Path, cfg: ChatConfig, budget_name: str, *, mock: bool, keep_ws: bool) -> dict:
    art = run_dir / slug(task)
    if art.exists():
        shutil.rmtree(art)
    art.mkdir(parents=True)
    ws = run_dir / "_workspaces" / slug(task)
    started = time.time()
    build_workspace(task, ws)
    runner = Runner(
        task, ws, cfg, BUDGETS[budget_name], art, ROOT,
        **({"chat_fn": mock_chat_for(task)} if mock else {}),
    )
    result = runner.run()
    shutil.copy2(ws / task.editable_file, art / "final.lean")
    ver = verify_task(task, art / "final.lean")
    (art / "verifier.json").write_text(json.dumps(ver.to_json(), indent=2) + "\n")
    row = {
        "task_id": task.id,
        "difficulty": task.difficulty,
        "property_class": task.property_class,
        "category": task.category,
        "model": "mock" if mock else cfg.model,
        "budget": budget_name,
        "pass": ver.passed,
        "verifier_status": ver.status,
        "verifier_detail": ver.detail[:2000],
        "z3": {
            "soundness": ver.soundness,
            "completeness": ver.completeness,
            "nonvacuity": ver.nonvacuity,
            "nontriviality": ver.nontriviality,
            "counterexample": ver.counterexample,
        },
        "axioms": ver.axioms,
        "agent": asdict(result) | {"final_candidate": None},
        "wall_seconds": round(time.time() - started, 2),
    }
    if not keep_ws:
        shutil.rmtree(ws, ignore_errors=True)
    return row


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="python -m rfvb.run_agent",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--model", help="model name sent to the endpoint")
    ap.add_argument("--base-url", help="OpenAI-compatible base URL (…/v1); /chat/completions is appended")
    ap.add_argument("--api-key-env", default="OPENAI_API_KEY", help="env var holding the API key")
    ap.add_argument("--tasks", required=True, help="task selector (see above)")
    ap.add_argument("--budget", default="normal", choices=sorted(BUDGETS))
    ap.add_argument("--jobs", type=int, default=1, help="tasks in parallel (each runs Lean; mind RAM)")
    ap.add_argument("--run", help="run name (default: <utc time>-<model>)")
    ap.add_argument("--temperature", type=float, default=None)
    ap.add_argument("--max-tokens", type=int, default=16384, help="max completion tokens per request")
    ap.add_argument("--request-timeout", type=int, default=900)
    ap.add_argument("--stream", action="store_true", help="stream responses (avoids proxy idle timeouts on long generations)")
    ap.add_argument("--mock", action="store_true", help="no model: submit the reference specification (pipeline smoke test)")
    ap.add_argument("--keep-workspaces", action="store_true")
    args = ap.parse_args(argv)
    if not args.mock and not (args.model and args.base_url):
        ap.error("--model and --base-url are required unless --mock is given")
    tasks = select_tasks(args.tasks)
    model = "mock" if args.mock else args.model
    run = args.run or f"{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{model.replace('/', '_')}"
    results = ROOT / "results"
    run_dir = results / run
    run_dir.mkdir(parents=True, exist_ok=True)
    out_path = results / f"{run}.jsonl"
    cfg = ChatConfig(
        base_url=args.base_url or "mock://",
        model=model,
        api_key=os.environ.get(args.api_key_env),
        temperature=args.temperature,
        max_tokens=args.max_tokens,
        timeout=args.request_timeout,
        stream=args.stream,
    )
    lock = threading.Lock()
    rows: list[dict] = []

    def work(task: Task) -> None:
        try:
            row = run_one(task, run_dir, cfg, args.budget, mock=args.mock, keep_ws=args.keep_workspaces)
        except Exception as exc:  # harness failure: record and keep going
            row = {
                "task_id": task.id,
                "difficulty": task.difficulty,
                "model": model,
                "pass": False,
                "verifier_status": "harness_error",
                "verifier_detail": repr(exc),
            }
        with lock:
            rows.append(row)
            with out_path.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(row, ensure_ascii=False) + "\n")
            print(
                f"[{len(rows)}/{len(tasks)}] {'PASS' if row['pass'] else 'fail'} {task.id} "
                f"({row['verifier_status']}, {row.get('wall_seconds', 0)}s)",
                flush=True,
            )

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        list(pool.map(work, tasks))
    shutil.rmtree(run_dir / "_workspaces", ignore_errors=True)
    passed = sum(r["pass"] for r in rows)
    print(f"\n{run}: {passed}/{len(rows)} verified -> {out_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
