"""_prove_equal skips the case tree once the unsat-core probe found a model of
premise ∧ x ≠ y (the case tree refutes exactly that formula), and its cache
entries keep their terms alive (z3 recycles the ids of freed terms). The
light-premise probe's per-conjunct tests (_heavy, _no_binder) are memoized."""
import gc

from z3 import And, BitVec, If, ULE, ULT

import verification.block_equivalence as be

a, b, c = BitVec("pes_a", 16), BitVec("pes_b", 16), BitVec("pes_c", 16)


def _no_cases(monkeypatch):
    calls = []
    real = be._refute_by_cases
    monkeypatch.setattr(be, "_refute_by_cases", lambda *args, **kw: (calls.append(args), real(*args, **kw))[1])
    return calls


def test_satisfiable_difference_skips_the_case_tree(monkeypatch):
    calls = _no_cases(monkeypatch)
    cache = {}
    # a = b is not entailed (a = 1, b = 2 is a model): core probe answers sat.
    assert be._prove_equal(And(ULT(a, 10), ULT(b, 10)), a, b, 2000, None, cache) is None
    assert calls == []
    (used, proofs, _), = cache[tuple(sorted((a.get_id(), b.get_id())))]
    assert proofs is None  # failure recorded under the full premise, as a case-tree failure is


def test_without_cache_the_case_tree_still_runs(monkeypatch):
    # No cache: no core probe, so nothing is known about satisfiability.
    calls = _no_cases(monkeypatch)
    assert be._prove_equal(And(ULT(a, 10), ULT(b, 10)), a, b, 2000, None) is None
    assert len(calls) == 1


def test_unknown_core_probe_still_tries_the_case_tree(monkeypatch):
    # Equal only by cases on the guard: the core probe is forced unknown, so the
    # case tree must run and prove it.
    calls = _no_cases(monkeypatch)

    def unknown_core(assertions, goal, timeout, outcome=None):
        if outcome is not None:
            outcome["answer"] = "unknown"
        return None
    monkeypatch.setattr(be, "unsat_core", unknown_core)
    premise = And(ULE(c, 5), a == If(ULE(c, 5), b, b + 1))
    proofs = be._prove_equal(premise, a, b, 5000, None, {})
    assert proofs is not None and len(calls) == 1


def test_entailed_equality_is_still_proved_with_the_skip(monkeypatch):
    calls = _no_cases(monkeypatch)
    cache = {}
    assert be._prove_equal(And(a == b + c, c == 0), a, b, 2000, None, cache) is not None
    assert calls == []  # the core probe proved it


def test_cache_entries_keep_their_terms_alive():
    cache = {}
    x, y = BitVec("pes_x", 16), BitVec("pes_y", 16)
    key = tuple(sorted((x.get_id(), y.get_id())))
    be._prove_equal(And(x == y + 0, ULT(y, 3)), x, y, 2000, None, cache)
    del x, y
    gc.collect()
    (_, _, keep), = cache[key]
    assert {keep[0].get_id(), keep[1].get_id()} == set(key)
    assert all(t.get_id() for t in keep[2])


def test_memoized_conjunct_tests_agree_with_the_walk():
    from z3 import Array, BitVecSort, Function, Lambda, Select
    f = Function("pes_f", BitVecSort(16), BitVecSort(16))
    m = Array("pes_m", BitVecSort(16), BitVecSort(16))
    i = BitVec("pes_i", 16)
    terms = [a == b, a * b == c, a * 3 == c, f(a) == b, f(BitVec("pes_k", 16)) == 0,
             Select(Lambda([i], Select(m, i + a)), b) == c, ULT(a, b)]
    for _ in range(2):  # the second pass answers from the memo
        assert [be._heavy(t) for t in terms] == [be._heavy_uncached(t) for t in terms] == [
            False, True, False, True, True, False, False]
        assert [be._no_binder(t) for t in terms] == [be._no_binder_uncached(t) for t in terms] == [
            True, True, True, True, True, False, True]
