"""Resource limits for the Lean/Lake processes started by the harness and verifier.

Each command runs in its own process group. The whole group is killed when the
wall-clock timeout expires (so no orphaned `lean` workers survive a timed-out
`lake`), or when the group's total resident memory exceeds
`RFVB_LEAN_MEMORY_BYTES` (default 16 GiB; 0 disables the check). A runaway
elaboration then fails with an explicit out-of-memory message instead of
exhausting the host.

Hosts that gate heavy Lean work behind a `lean-slot` concurrency wrapper (a
shared machine where `lake env lean` waits for one of a few host-wide slots)
are supported without bypassing the gate: the command is run as
`lean-slot sh -c '<marker>; exec <real lake> …'`, and the timeout only starts
once the marker shows the slot was acquired, so queueing time never turns into
a spurious `lean_timeout`. Waiting for a slot is bounded separately
(`RFVB_LEAN_SLOT_WAIT_SECONDS`, default 3600).
"""
from __future__ import annotations

import os
import shutil
import signal
import subprocess
import threading
import time

LEAN_MEMORY_BYTES = int(os.environ.get("RFVB_LEAN_MEMORY_BYTES", str(16 * 2**30)))
SLOT_WAIT_SECONDS = int(os.environ.get("RFVB_LEAN_SLOT_WAIT_SECONDS", "3600"))
SLOT_MARKER = "__RFVB_LEAN_SLOT_ACQUIRED__"
PAGE = os.sysconf("SC_PAGE_SIZE")


def _is_shim(path: str) -> bool:
    try:
        with open(path, "rb") as fh:
            head = fh.read(400)
    except OSError:
        return False
    return head.startswith(b"#!") and b"shim" in head


def _real_lake() -> str | None:
    env = os.environ.get("RFVB_REAL_LAKE")
    if env and os.access(env, os.X_OK):
        return env
    for directory in os.environ.get("PATH", "").split(os.pathsep):
        cand = os.path.join(directory or ".", "lake")
        if os.access(cand, os.X_OK) and not os.path.isdir(cand) and not _is_shim(cand):
            return cand
    return None


def lake_command(args: list[str]) -> tuple[list[str], bool]:
    """Command running `lake <args>`, and whether it first waits for a host Lean slot.

    Only `lake env lean …` is routed through `lean-slot` (mirroring the host's
    own policy); other Lake commands run as usual."""
    gate = shutil.which("lean-slot")
    real = _real_lake()
    if gate and real and args[:2] == ["env", "lean"]:
        script = f'printf "%s\\n" "{SLOT_MARKER}"; exec "$0" "$@"'
        return [gate, "sh", "-c", script, real, *args], True
    return ["lake", *args], False


def group_rss(pgid: int) -> int:
    total = 0
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat") as fh:
                fields = fh.read().rsplit(")", 1)[1].split()
            if int(fields[2]) != pgid:  # fields[2] = pgrp
                continue
            with open(f"/proc/{entry}/statm") as fh:
                total += int(fh.read().split()[1]) * PAGE
        except (OSError, IndexError, ValueError):
            continue
    return total


from . import ROOT

_BASE_LEAN_PATH: str | None = None
_BASE_LOCK = threading.Lock()


def _lean_env_for(cwd) -> dict[str, str] | None:
    global _BASE_LEAN_PATH
    with _BASE_LOCK:
        if _BASE_LEAN_PATH is None:
            try:
                _BASE_LEAN_PATH = subprocess.check_output(
                    ["lake", "env", "printenv", "LEAN_PATH"],
                    cwd=ROOT,
                    text=True,
                    timeout=30,
                ).strip()
            except Exception:
                _BASE_LEAN_PATH = ""
    if not _BASE_LEAN_PATH:
        return None
    env = os.environ.copy()
    root_lib = str((ROOT / ".lake" / "build" / "lib" / "lean").resolve())
    cwd_lib = str((os.path.abspath(cwd) + "/.lake/build/lib/lean"))
    env["LEAN_PATH"] = _BASE_LEAN_PATH.replace(root_lib, cwd_lib)
    return env


def run_limited(cmd: list[str], cwd, timeout: float, mem_bytes: int = LEAN_MEMORY_BYTES,
                gated: bool = False) -> tuple[int, str]:
    """Run `cmd`; return (exit code, stdout+stderr). 124 = timeout, 137 = memory limit, 75 = no slot.

    With `gated=True` the timeout starts when `SLOT_MARKER` appears on the output."""
    env = None
    if not gated and len(cmd) > 2 and cmd[:2] == ["lake", "env"]:
        env = _lean_env_for(cwd)
        if env is not None:
            cmd = cmd[2:]
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    lines: list[str] = []
    started = threading.Event()
    if not gated:
        started.set()

    def reader() -> None:
        assert proc.stdout is not None
        for line in proc.stdout:
            if gated and not started.is_set() and line.strip() == SLOT_MARKER:
                started.set()
                continue
            lines.append(line)

    t = threading.Thread(target=reader, daemon=True)
    t.start()
    begin = time.monotonic()
    run_start = begin if not gated else None
    reason = None
    while True:
        try:
            proc.wait(timeout=1.0)
            break
        except subprocess.TimeoutExpired:
            pass
        now = time.monotonic()
        if run_start is None and started.is_set():
            run_start = now
        if run_start is not None and now - run_start >= timeout:
            reason = "timeout"
        elif run_start is None and now - begin >= SLOT_WAIT_SECONDS:
            reason = "slot"
        elif mem_bytes > 0 and group_rss(proc.pid) > mem_bytes:
            reason = "memory"
        if reason:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
            break
    t.join(timeout=10)
    text = "".join(lines)
    if reason == "timeout":
        return 124, text + f"\nLean timed out after {int(timeout)}s"
    if reason == "slot":
        return 75, text + f"\nno Lean slot became available within {SLOT_WAIT_SECONDS}s (host busy)"
    if reason == "memory":
        return 137, text + f"\nout of memory: the Lean process group exceeded {mem_bytes / 2**30:.0f} GiB and was killed"
    return proc.returncode, text
