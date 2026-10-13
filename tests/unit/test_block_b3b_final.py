"""b3b-final: the merged _prove_equal cache (review-3b + pair-throughput), the
correspondence wall clock, and the light-premise budget of
_retry_with_uf_unification."""
import gc
from types import SimpleNamespace

import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, BoolVal, Function, If, Lambda, Select, Solver,
                Store, ULE, ULT, UGE)

import verification.block_equivalence as be
from x86_64 import cfg_state
from x86_64.cfg_state import PrefixSolver

BV64, BV8 = BitVecSort(64), BitVecSort(8)


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


# _prove_equal cache ----------------------------------------------------------

def test_every_prove_equal_route_writes_entries_that_keep_their_ids_alive(monkeypatch):
    """One cache filled by every writer: light hit, core hit, case-tree hit, the
    core-SAT skip (pair-throughput) and a case-tree miss. After the terms are
    dropped, each proof entry still holds x, y and every conjunct of its id set;
    failure entries hold nothing."""
    a, b, c, p, q, w = (BitVec(f"bf_{s}", 64) for s in "abcpqw")
    cache = {}
    assert be._prove_equal(And(a == b, p * q == w), a, b, 2000, None, cache) is not None  # light
    assert be._prove_equal(And(a == c, c != 0), a, c, 2000, None, cache) is not None      # unsat_core
    assert be._prove_equal(And(ULT(a, 9), ULT(b, 9)), a, b + 1, 2000, None, cache) is None  # core sat: skip
    real_core = be.unsat_core

    def unknown_core(assertions, goal, timeout, outcome=None):
        if outcome is not None:
            outcome["answer"] = "unknown"
        return None
    monkeypatch.setattr(be, "unsat_core", unknown_core)
    guard = And(ULE(c, 5), a == If(ULE(c, 5), b, b + 1))
    assert be._prove_equal(guard, a, b, 5000, None, cache) is not None                   # case tree
    assert be._prove_equal(And(ULT(c, 3), ULT(w, 3)), c, w, 2000, None, cache) is None  # case tree miss
    monkeypatch.setattr(be, "unsat_core", real_core)
    del a, b, c, p, q, w, guard
    gc.collect()
    proofs_seen = failures_seen = 0
    for key, entries in cache.items():
        for used, proofs, alive in entries:
            if proofs is None:
                failures_seen += 1
                assert alive == ()
                continue
            proofs_seen += 1
            held = {t.get_id() for t in alive}
            assert set(key) <= held and used <= held
    assert proofs_seen == 3 and failures_seen == 2


def test_core_sat_skip_entry_answers_weaker_premises_only():
    # The skip's failure entry is keyed by the full premise: a stronger premise
    # (more conjuncts) is tried again and proved, a weaker one is a cached miss.
    a, b = BitVec("bf_sa", 16), BitVec("bf_sb", 16)
    cache = {}
    assert be._prove_equal(And(ULT(a, 10), ULT(b, 10)), a, b, 2000, None, cache) is None
    assert be._prove_equal(And(ULT(a, 10), ULT(b, 10), a == b), a, b, 2000, None, cache) is not None


# correspondence wall clock ---------------------------------------------------

class _RecordingSolver:
    """A z3 Solver whose set() calls are recorded."""

    def __init__(self):
        self.inner, self.params = Solver(), {}

    def set(self, name, value):
        self.params[name] = value
        self.inner.set(name, value)

    def __getattr__(self, name):
        return getattr(self.inner, name)


def test_bounded_check_wall_clock_defaults_to_the_safety_net_and_can_be_set():
    x = BitVec("bf_x", 8)
    solver = _RecordingSolver()
    PrefixSolver(solver).check([ULT(x, 3)], 40)
    assert solver.params == {"rlimit": 40 * cfg_state.REACHABILITY_RLIMIT_PER_MS,
                             "timeout": 40 * cfg_state.REACHABILITY_WALL_SAFETY_FACTOR}
    PrefixSolver(solver).check([ULT(x, 3)], 40, "correspondence", 40)
    assert solver.params == {"rlimit": 40 * cfg_state.REACHABILITY_RLIMIT_PER_MS, "timeout": 40}


def test_correspondence_rows_get_their_budget_as_wall_clock(monkeypatch):
    x = BitVec("bf_corr", 8)
    calls, real = [], PrefixSolver.check

    def record(self, conjuncts, timeout_ms, tag="incremental", wall_ms=None):
        calls.append((tag, timeout_ms, wall_ms))
        return real(self, conjuncts, timeout_ms, tag, wall_ms)
    monkeypatch.setattr(be.PrefixSolver, "check", record)
    paths = lambda cs: [SimpleNamespace(condition=c) for c in cs]
    evm = paths([ULT(x, 10), UGE(x, 10), BoolVal(False)])
    x86 = paths([ULT(x, 3), And(UGE(x, 3), ULT(x, 10)), And(UGE(x, 10), ULT(x, 20)), UGE(x, 20), x == 255, x == 0])
    corr = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._correspondence(evm, x86, BoolVal(True), [])
    assert corr == (0, 0, 1, 1, 1, 0)
    rows = [c for c in calls if c[0] == "correspondence"]
    assert len(rows) == len(x86)
    assert all(wall == budget and 0 < budget <= be._QUICK_EXACT_MS for _, budget, wall in rows)


# _retry_with_uf_unification light-premise budget -------------------------------

def test_uf_unification_light_query_keeps_the_per_query_budget(monkeypatch):
    """Deliberately not capped at _LIGHT_MS: on the Safe 5377 d30 pairs this query
    is the step that refutes the memory goal, in 3.2-20.0s (pair-throughput
    traces, 32/32 hits, 0 misses); a 2s cap would turn every one into a miss."""
    i, k, n = BitVec("bf_i", 64), BitVec("bf_k", 64), BitVec("bf_n", 64)
    xx, yy, ww = BitVec("bf_px", 64), BitVec("bf_py", 64), BitVec("bf_pw", 64)
    M, v = Array("bf_M", BV64, BV8), BitVec("bf_v", 8)
    sha3 = Function("bf_sha3_slice", ArraySort(BV64, BV8), BV64, BV64)
    L_store = Lambda([i], If(ULT(i, n), Select(Store(M, k, v), i), BitVecVal(0, 8)))
    L_plain = Lambda([i], If(ULT(i, n), Select(M, i), BitVecVal(0, 8)))
    budgets, real = [], be._refute_over_light_premise

    def record(parts, goal, budget_ms):
        budgets.append(budget_ms)
        return real(parts, goal, budget_ms)
    monkeypatch.setattr(be, "_refute_over_light_premise", record)
    F = And(v == Select(M, k), ULT(sha3(L_store, n), 5), ULT(5, sha3(L_plain, n)), xx * yy == ww)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    _, answer, lemmas = prover._retry_with_uf_unification(F, "unknown")
    assert answer == "unsat" and "opaque_array_uf_light" in [l.name for l in lemmas]
    assert budgets and budgets[-1] > be._LIGHT_MS and budgets[-1] <= prover.timeout_ms
