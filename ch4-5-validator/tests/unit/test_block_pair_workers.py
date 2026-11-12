from z3 import And, BitVec, ULT

import verification.block_equivalence as be


def _obligations():
    x = BitVec("pw_x", 64)
    return [
        ("pair_0_0", And(ULT(x, 4), x == 9), ""),          # unsat: proved
        ("pair_0_1", And(ULT(x, 4), x * x == 10), ""),      # unsat, nonlinear
        ("pair_0_2", And(ULT(x, 4), x == 3), ""),           # SAT: must not prove
        ("pair_0_3", And(ULT(x, 4), x == 7), ""),
    ]


def _answers(monkeypatch, workers):
    monkeypatch.setenv("BLOCK_PAIR_WORKERS", str(workers))
    be._reset_pair_pool()
    try:
        records = []
        prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
        oks = list(prover._check_all(_obligations(), records))
        return oks, [(r.name, r.answer) for r in records]
    finally:
        be._reset_pair_pool()


def test_parallel_pairs_match_sequential(monkeypatch):
    sequential = _answers(monkeypatch, 1)
    parallel = _answers(monkeypatch, 2)
    assert sequential == parallel
    assert sequential[0] == [True, True, False, True]
    assert dict(sequential[1])["pair_0_2"] == "sat"


def test_pair_workers_outrunning_deadline_fail_the_node(monkeypatch):
    from concurrent.futures import TimeoutError as FutureTimeout
    from time import monotonic
    import pytest
    resets = []

    class Slow:
        def result(self, timeout=None):
            assert timeout is not None  # the wait is bounded by the node deadline
            raise FutureTimeout()

        def done(self):
            return False

    class Pool:
        def submit(self, *a, **k):
            return Slow()

    monkeypatch.setattr(be, "_pair_pool", lambda: Pool())
    monkeypatch.setattr(be, "_reset_pair_pool", lambda: resets.append(1))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000, deadline=monotonic() + 1)
    with pytest.raises(be.ProofBudgetExceeded):
        list(prover._check_all(_obligations(), []))
    assert resets


def test_deadline_grace_is_absolute_not_per_future(monkeypatch):
    from concurrent.futures import TimeoutError as FutureTimeout
    from time import monotonic
    import pytest
    waits = []

    class Done:
        def __init__(self, ok):
            self.ok = ok

        def result(self, timeout=None):
            waits.append(timeout)
            if not self.ok:
                raise FutureTimeout()
            return be.Obligation("pair", "true", "unsat")

        def done(self):
            return True

    class Pool:
        def __init__(self):
            self.n = 0

        def submit(self, *a, **k):
            self.n += 1
            return Done(self.n < 3)

    monkeypatch.setattr(be, "_pair_pool", lambda: Pool())
    monkeypatch.setattr(be, "_reset_pair_pool", lambda: None)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000, deadline=monotonic() - 100)
    with pytest.raises(be.ProofBudgetExceeded):
        list(prover._check_all(_obligations(), []))
    assert all(w == 0.0 for w in waits)  # deadline+30s already past: no extra waiting


def _alias_formula(high_bytes):
    """mstore(pos, 1) then a 4-byte mload(value): UNSAT for 2 high bytes, SAT for 1."""
    from z3 import Array, BitVecSort, BitVecVal, Concat, Extract, Not, Select, Store, simplify
    M = Array("pa_M", BitVecSort(64), BitVecSort(8))
    pos, value = BitVec("pa_pos", 64), BitVec("pa_value", 64)
    mem = M
    for j in range(4):
        mem = Store(mem, pos + j, BitVecVal(1 if j == 3 else 0, 8))
    word = Concat(*(Select(mem, value + i) for i in range(4)))
    evm = Not(And(*(Select(mem, value + i) == 0 for i in range(2))))
    return simplify(And(evm, Extract(31, 32 - 8 * high_bytes, word) == 0), bv_sort_ac=True)


def test_parallel_alias_cases_match_sequential(monkeypatch):
    sequential = be._alias_split(_alias_formula(2), 5000)
    monkeypatch.setenv("BLOCK_PAIR_WORKERS", "2")
    be._reset_pair_pool()
    monkeypatch.setattr(be, "solve_query", lambda q, t: "unknown")  # every local probe misses: all go to workers
    try:
        prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
        parallel = be._alias_split(_alias_formula(2), 5000, fallback=prover._refute_further, parallel=True)
        assert be._alias_split(_alias_formula(1), 5000, fallback=prover._refute_further, parallel=True) is None
    finally:
        be._reset_pair_pool()
    assert sequential is not None and parallel is not None and all(p.proved for p in parallel)
    assert [p.name for p in parallel] == [p.name for p in sequential]
