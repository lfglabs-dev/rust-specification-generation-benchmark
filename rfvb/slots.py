"""Cross-process concurrency slots (file locks), shared by every harness process.

Grading runs many Lean processes; several agent runs in parallel would otherwise
oversubscribe the machine. `with slot("grade", 3): ...` blocks until one of 3
host-wide slots named "grade" is free.
"""
from __future__ import annotations

import contextlib
import fcntl
import os
import time
from pathlib import Path

SLOT_DIR = Path(os.environ.get("RSGB_SLOT_DIR", str(Path.home() / ".rsgb-slots")))


@contextlib.contextmanager
def slot(name: str, n: int, poll: float = 2.0):
    SLOT_DIR.mkdir(parents=True, exist_ok=True)
    while True:
        for i in range(n):
            fh = open(SLOT_DIR / f"{name}.{i}.lock", "w")
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                fh.close()
                continue
            try:
                yield i
            finally:
                fcntl.flock(fh, fcntl.LOCK_UN)
                fh.close()
            return
        time.sleep(poll)
