"""N4 item 2: per-node observability and memory isolation of proof workers.

NodeMonitor (common/node_monitor) records pid / time / RSS of one node and, over
a memory budget, stops only that node (NodeMemoryExceeded at its next solver
call); NodePool (verification/block_parallel) fails only the task of a worker
that dies and keeps the other workers' tasks running.
"""
import os
import signal
import time

import pytest
from z3 import BitVec, ULT

import common.node_monitor as nm
import verification.block_parallel as bp
from verification.block_equivalence import BlockEquivalenceProver, ProofBudgetExceeded, solve_query
from verification.block_program import BlockProgramResult
from verification.block_specialization import BlockSpecialization


def _wait_for(predicate, seconds=10.0):
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        if predicate():
            return True
        time.sleep(0.02)
    return False


# --- pool tasks (module level: picklable by reference in spawned workers) ----

def _echo(value, seconds=0.0):
    time.sleep(seconds)
    return dict(value=value, pid=os.getpid())


def _exit_now(code):
    os._exit(code)


def _segfault():
    os.kill(os.getpid(), signal.SIGSEGV)
    time.sleep(10)


def _recycled():
    return dict(recycle=True, pid=os.getpid())


def _raise():
    raise ValueError("boom")


# --- NodeMonitor -------------------------------------------------------------

def _fake_rss(monkeypatch, start):
    rss = [start]
    monkeypatch.setattr(nm, "rss_bytes", lambda: rss[0])
    return rss


def test_monitor_records_pid_times_and_peak_rss(monkeypatch, tmp_path):
    rss = _fake_rss(monkeypatch, 500 * 2**20)
    status = tmp_path / "worker.json"
    with nm.NodeMonitor("node-a", status_path=status, interval=0.01, status_seconds=0.01) as monitor:
        rss[0] = 900 * 2**20
        assert _wait_for(lambda: monitor.peak_rss == 900 * 2**20)
        assert _wait_for(lambda: (nm.read_status(status) or {}).get("rss_mb") == 900.0)
        running = nm.read_status(status)
        assert running["node"] == "node-a" and running["pid"] == os.getpid() and running["state"] == "running"
        rss[0] = 600 * 2**20
    info = monitor.info()
    assert info["pid"] == os.getpid() and info["finished_at"] >= info["started_at"]
    assert (info["start_rss_mb"], info["peak_rss_mb"], info["end_rss_mb"]) == (500.0, 900.0, 600.0)
    assert info["memory_exceeded"] is None and nm.read_status(status)["state"] == "finished"


def test_memory_exceeded_is_not_an_ordinary_exception():
    # No `except Exception` on the way (summary fallbacks, rewrite helpers) can absorb it.
    assert not issubclass(nm.NodeMemoryExceeded, Exception)
    assert not issubclass(nm.NodeMemoryExceeded, ProofBudgetExceeded)


def test_over_budget_node_stops_at_its_next_solver_call_and_the_flag_ends_with_it(monkeypatch):
    rss = _fake_rss(monkeypatch, 500 * 2**20)
    x = BitVec("iso_x", 64)
    query = ULT(x, 3)
    with nm.NodeMonitor("node-b", 600 * 2**20, hard_bytes=2**40, grace_seconds=60, interval=0.01) as monitor:
        assert solve_query(query, 1000) == "sat"  # under budget: untouched
        rss[0] = 700 * 2**20
        assert _wait_for(lambda: monitor.exceeded is not None)
        with pytest.raises(nm.NodeMemoryExceeded):
            solve_query(query, 1000)
        rss[0] = 500 * 2**20
    assert "RSS 700.0 MB > budget 600.0 MB" in monitor.info()["memory_exceeded"]
    assert solve_query(query, 1000) == "sat"  # the next node starts clean


def test_interrupted_answer_is_never_cached(monkeypatch, tmp_path):
    from verification import proof_cache
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    query = ULT(BitVec("iso_y", 64), 5)
    nm._ABORT[0] = "test: over budget"
    try:
        with pytest.raises(nm.NodeMemoryExceeded):
            solve_query(query, 1000)
    finally:
        nm._ABORT[0] = None
    key = proof_cache.query_key("check", query)
    assert proof_cache.cached_answer(key, 1000) is None


# --- NodePool ----------------------------------------------------------------

def test_pool_dead_worker_fails_only_its_own_task():
    pool = bp.NodePool(3)
    try:
        slow = pool.submit(_echo, "kept", 1.5)
        dead = pool.submit(_exit_now, nm.MEMORY_EXIT_CODE)
        crashed = pool.submit(_segfault)
        done = set()
        end = time.monotonic() + 60
        while len(done) < 3 and time.monotonic() < end:
            done |= pool.wait(1)
        assert done == {slow, dead, crashed}
        assert slow.result()["value"] == "kept"
        assert isinstance(dead.exception(), bp.WorkerDied) and dead.exception().memory
        assert isinstance(crashed.exception(), bp.WorkerDied) and crashed.exception().exitcode == -signal.SIGSEGV
        assert not crashed.exception().memory
        # Both dead workers were replaced: the pool keeps its width.
        again = [pool.submit(_echo, n) for n in range(3)]
        done = set()
        while len(done) < 3 and time.monotonic() < end:
            done |= pool.wait(1)
        assert sorted(f.result()["value"] for f in again) == [0, 1, 2]
        assert {dead.pid, crashed.pid}.isdisjoint({f.result()["pid"] for f in again})
    finally:
        pool.shutdown()


def test_pool_recycles_a_worker_that_asks_for_it_and_reports_task_errors():
    pool = bp.NodePool(1)
    try:
        first = pool.submit(_recycled)
        assert _wait_for(lambda: bool(pool.wait(0.1)), 60)
        second = pool.submit(_echo, 1)
        assert _wait_for(lambda: bool(pool.wait(0.1)), 60)
        assert second.result()["pid"] != first.result()["pid"]
        failing = pool.submit(_raise)
        assert _wait_for(lambda: bool(pool.wait(0.1)), 60)
        assert "ValueError: boom" in str(failing.exception())
    finally:
        pool.shutdown()


# --- prove_instance / _prove_all ---------------------------------------------

SPEC = BlockSpecialization(10, 1, 64, 128)


class _Setup:
    prover = BlockEquivalenceProver([], [], {})


def test_prove_instance_reports_an_over_budget_node_alone_as_inconclusive(monkeypatch, tmp_path):
    monkeypatch.setattr(bp, "_WORKER", dict(setup=_Setup(), identity="id", memory_budget=nm.rss_bytes() - 2**20,
                                            status_dir=str(tmp_path)))

    def over_budget(*_):
        assert _wait_for(lambda: nm._ABORT[0] is not None)
        solve_query(ULT(BitVec("iso_z", 8), 1), 1000)
        raise AssertionError("the solver call must stop the node")

    monkeypatch.setattr(bp, "_prove_instance", over_budget)
    node = bp.prove_instance(SPEC, 60, time.time() + 60)
    assert node["proved"] is False and node["status"] == "inconclusive" and node["theorem"] is None
    assert "memory budget exceeded" in node["reasons"][0] and node["memory_exceeded"]
    assert node["recycle"] and node["pid"] == os.getpid() and node["peak_rss_mb"] > 0
    assert nm._ABORT[0] is None
    assert nm.read_status(tmp_path / f"worker-{os.getpid()}.json")["state"] == "finished"


def test_memory_killed_worker_is_final_for_its_node_and_not_retried(monkeypatch, tmp_path):
    pools = []

    class Pool:
        """NodePool stand-in: every task dies like a worker the kernel OOM killer took."""

        def __init__(self, *a, **k):
            self.submitted, self.futures = [], set()
            pools.append(self)

        def submit(self, fn, *args):
            from concurrent.futures import Future
            future = Future()
            future.set_exception(bp.WorkerDied(4242, -9, dict(node=repr(args[0]), state="running",
                                                              peak_rss_mb=9000.0)))
            self.submitted.append(args[0])
            self.futures.add(future)
            return future

        def wait(self, timeout):
            done, self.futures = self.futures, set()
            return done

        def running(self):
            return []

        def shutdown(self):
            pass

    monkeypatch.setattr(bp, "NodePool", Pool)
    result = BlockProgramResult()
    result.diagnostics = {SPEC.pc: {"status": "queued", "instances": []}}
    options = dict(node_seconds=300, first_pass_node_seconds=30, status_dir=str(tmp_path))
    done = bp._prove_all("stem", options, (SPEC,), {SPEC: (SPEC,)}, "id", time.time() + 600, 1, 1, None,
                         result, None)
    assert pools[0].submitted == [SPEC]  # no full-budget retry after a memory kill
    assert not done[SPEC]["proved"] and done[SPEC]["memory_exceeded"]
    (instance,) = result.diagnostics[SPEC.pc]["instances"]
    assert instance["status"] == "inconclusive" and instance["pid"] == 4242 and instance["peak_rss_mb"] == 9000.0
    assert "signal 9" in instance["reasons"][0]
