"""Per-node observability and memory budget for proof workers.

A worker process proves one node after another. NodeMonitor runs beside one
node: a sampler thread records the process memory (RSS plus swap; start, peak, end) and,
every few seconds, writes a small JSON status file (pid, node, start time,
current / peak RSS) that the parent reads to say which node a worker is on
and how big it is (block_parallel). With a memory budget, the first sample
above it sets a process-wide abort flag and interrupts Z3: the next solver
call (check_abort: solve_query / _solver in block_equivalence) or x86
executor step raises NodeMemoryExceeded, and the worker reports only this
node as inconclusive. If the node does not unwind within a grace period, or RSS
reaches a hard ceiling first, the worker exits with MEMORY_EXIT_CODE; the
parent's pool then fails that one task and respawns the worker.

Soundness: the flag only ever stops work. NodeMemoryExceeded derives from
BaseException, so no `except Exception` handler on the way (summary
fallbacks, "try this rewrite" helpers) can turn it into an answer; nothing
is concluded from an aborted node, which is reported inconclusive.
"""
from __future__ import annotations

import gc
import json
import os
import threading
import time
from pathlib import Path

MEMORY_EXIT_CODE = 86  # a worker that exited because its node ran over the hard memory ceiling


class NodeMemoryExceeded(BaseException):
    """The running node went over its memory budget: stop it, conclude nothing."""


_ABORT = [None]  # message while the running node is over its memory budget
_BUDGET = [None]  # bytes: the running node's memory budget (memory_headroom_mb)
# Automatic cyclic GC is off while a NodeMonitor runs: the sampler thread's own allocations
# would otherwise run collections there, and a Z3 wrapper's __del__ (Z3_dec_ref) on that thread
# races the main thread's Z3 calls on the same context (a SIGSEGV in native AST deletion was
# seen with a profiling thread). check_abort, on the main thread, collects instead.
_GC_DEFERRED = [False]


def collect_deferred_garbage():
    """While automatic GC is deferred, collect on the calling (main) thread once the
    generation-0 count reaches its threshold, choosing the generation from the counters
    and thresholds (a simplification of CPython's own policy; threshold 0 still means off)."""
    if not _GC_DEFERRED[0]:
        return
    (t0, t1, t2), (c0, c1, c2) = gc.get_threshold(), gc.get_count()
    if t0 and c0 >= t0:
        gc.collect(2 if c2 >= t2 else 1 if c1 >= t1 else 0)


def check_abort():
    """Raise NodeMemoryExceeded while the running node is over its budget. Also the
    main thread's safe point for garbage collection (collect_deferred_garbage)."""
    collect_deferred_garbage()
    if _ABORT[0] is not None:
        raise NodeMemoryExceeded(_ABORT[0])


def memory_headroom_mb():
    """MB the running node may still grow before its memory budget, or None
    without a budget: z3_memory_cap never lets one Z3 call take more, so a call
    that would push the node over its budget ends as unknown on its own."""
    if _BUDGET[0] is None:
        return None
    return max(0, (_BUDGET[0] - rss_bytes()) // 2**20)


def rss_bytes():
    """Memory of this process: resident set plus swapped-out pages (Linux /proc;
    0 where unavailable). Swap counts: on the servers a growing node is pushed
    to swap (Aave 7200: 16.8 GB resident + 29.9 GB swap), and a resident-only
    budget would never see it."""
    try:
        total = 0
        with open("/proc/self/status") as f:
            for line in f:
                if line.startswith(("VmRSS:", "VmSwap:")):
                    total += int(line.split()[1]) * 1024
        return total
    except (OSError, ValueError, IndexError):
        return 0


def release_memory():
    """Hand freed heap pages back to the OS (glibc malloc_trim); no-op elsewhere."""
    try:
        import ctypes
        ctypes.CDLL("libc.so.6").malloc_trim(0)
    except (OSError, AttributeError):
        pass


def _interrupt_z3():
    try:
        from z3 import main_ctx
        main_ctx().interrupt()
    except Exception:
        pass


def _mb(value):
    return round(value / 2**20, 1)


class NodeMonitor:
    """Context manager around one node's proof in a worker (see the module docstring).

    budget_bytes: soft budget (None: observe only). hard_bytes: ceiling at
    which the process exits at once (default 1.5x the budget); grace_seconds:
    how long the node may take to unwind after the soft budget tripped.
    status_path: JSON status file rewritten every status_seconds.
    """

    def __init__(self, label, budget_bytes=None, *, hard_bytes=None, grace_seconds=300.0, interval=1.0,
                 status_path=None, status_seconds=10.0):
        self.label, self.budget = label, budget_bytes
        self.hard = hard_bytes if hard_bytes is not None or budget_bytes is None else int(1.5 * budget_bytes)
        self.grace, self.interval = grace_seconds, interval
        self.status_path = None if status_path is None else Path(status_path)
        self.status_seconds = status_seconds
        self.pid = os.getpid()
        self.started_at = self.finished_at = None
        self.start_rss = self.peak_rss = self.end_rss = 0
        self.exceeded = None  # message once the soft budget tripped
        self._tripped = None  # monotonic time it tripped
        self._stop = threading.Event()
        self._thread = None

    def __enter__(self):
        self.started_at = time.time()
        self.start_rss = self.peak_rss = rss_bytes()
        _ABORT[0], _BUDGET[0] = None, self.budget
        self._write_status("running")
        self._gc_was = (gc.isenabled(), _GC_DEFERRED[0])
        gc.disable()  # before the thread starts: see _GC_DEFERRED
        _GC_DEFERRED[0] = True
        self._thread = threading.Thread(target=self._run, name="node-monitor", daemon=True)
        try:
            self._thread.start()
        except BaseException:  # no __exit__ follows: stop a thread that did start, then undo
            if self._thread.is_alive():
                self._stop.set()
                self._thread.join()
            self._restore_gc()
            raise
        return self

    def _restore_gc(self):
        enabled, _GC_DEFERRED[0] = self._gc_was
        if enabled:
            gc.enable()

    def __exit__(self, *exc):
        self._stop.set()
        self._thread.join()
        self._restore_gc()
        gc.collect()  # the node's deferred garbage, here on the owning thread
        self._sample()
        _ABORT[0] = _BUDGET[0] = None
        self.finished_at = time.time()
        self.end_rss = rss_bytes()
        self._write_status("finished")
        return False

    def _sample(self):
        rss = rss_bytes()
        self.peak_rss = max(self.peak_rss, rss)
        if self.budget is not None and self.exceeded is None and rss > self.budget:
            self.exceeded = (f"node memory budget exceeded: RSS {_mb(rss)} MB > budget {_mb(self.budget)} MB "
                             f"(pid {self.pid})")
            self._tripped = time.monotonic()
            _ABORT[0] = self.exceeded
        return rss

    def _run(self):
        last_status = time.monotonic()
        while not self._stop.wait(self.interval):
            rss = self._sample()
            if self.exceeded is not None:
                # Every sample: a solver call that started before the flag (or one that
                # does not go through check_abort) is stopped too.
                _interrupt_z3()
                if (self.hard is not None and rss > self.hard) or time.monotonic() - self._tripped > self.grace:
                    self._write_status("killed")
                    os._exit(MEMORY_EXIT_CODE)
            if time.monotonic() - last_status >= self.status_seconds:
                last_status = time.monotonic()
                self._write_status("running", rss)

    def info(self):
        """Plain data for the node's result: who ran it, when, and how big it got."""
        return dict(pid=self.pid, started_at=self.started_at, finished_at=self.finished_at,
                    start_rss_mb=_mb(self.start_rss), peak_rss_mb=_mb(self.peak_rss), end_rss_mb=_mb(self.end_rss),
                    memory_budget_mb=None if self.budget is None else _mb(self.budget),
                    memory_exceeded=self.exceeded)

    def _write_status(self, state, rss=None):
        if self.status_path is None:
            return
        data = dict(self.info(), node=self.label, state=state, updated_at=time.time(),
                    rss_mb=_mb(rss_bytes() if rss is None else rss))
        try:
            self.status_path.parent.mkdir(parents=True, exist_ok=True)
            tmp = self.status_path.with_suffix(".tmp")
            tmp.write_text(json.dumps(data))
            tmp.replace(self.status_path)
        except OSError:
            pass  # observability only


def read_status(path):
    """A worker status file's data, or None."""
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return None
