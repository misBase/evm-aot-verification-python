import pytest
"""E (Safe 5377): Lambda terms are arrays (z3py is_array(Lambda) is False).

_differ compares lambdas pointwise, generalize_array_terms treats lambda UF
arguments as arrays, and _retry_with_uf_unification tries the opaque array-UF
query right after unification.
"""
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Function, If, Lambda, Select, Store, ULT,
                is_quantifier, simplify)

import verification.block_equivalence as be

BV64, BV8 = BitVecSort(64), BitVecSort(8)
M = Array("e_M", BV64, BV8)
i, k, n, n2 = BitVec("e_i", 64), BitVec("e_k", 64), BitVec("e_n", 64), BitVec("e_n2", 64)
v = BitVec("e_v", 8)
sha3 = Function("e_sha3_slice", ArraySort(BV64, BV8), BV64, BV64)

# The same slice built two ways: a byte store of v at k, then the plain array.
L_store = Lambda([i], If(ULT(i, n), Select(Store(M, k, v), i), BitVecVal(0, 8)))
L_plain = Lambda([i], If(ULT(i, n), Select(M, i), BitVecVal(0, 8)))
L_shift = Lambda([i], If(ULT(i, n), Select(M, i + 1), BitVecVal(0, 8)))  # a different slice


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _has_binder(term):
    seen, work = set(), [term]
    while work:
        t = work.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if is_quantifier(t):
            return True
        work.extend(t.children())
    return False


def test_differ_compares_lambdas_pointwise():
    d = be._differ(L_store, L_plain)
    # Select(x, idx) != Select(y, idx): no array-sorted (dis)equality left for the solver.
    assert all(a.sort() == BV8 for a in d.children()), d


def test_prove_equal_merges_equal_lambdas_and_refuses_different_ones():
    premise = v == Select(M, k)
    assert be._prove_equal(premise, L_store, L_plain, 3000, None) is not None
    # Soundness: without the premise (or for a shifted slice) the lambdas differ.
    assert be._prove_equal(BitVecVal(1, 1) == 1, L_store, L_plain, 3000, None) is None
    assert be._prove_equal(premise, L_store, L_shift, 3000, None) is None


def test_generalize_array_terms_abstracts_uf_applications_over_lambdas():
    m = BitVec("e_m", 64)
    F = And(n == m, sha3(L_plain, n) != sha3(L_plain, m))
    G = be.generalize_array_terms(F)
    assert not _has_binder(G), G  # sha3(L, .) became one fresh g(.) per lambda AST
    assert be.solve_query(G, 3000) == "unsat"  # congruence in the other argument survives


def test_generalize_array_terms_soundness_distinct_lambdas_stay_distinct():
    # sha3(L_plain, n) != sha3(L_shift, n) is SAT; the generalisation only adds models.
    F = sha3(L_plain, n) != sha3(L_shift, n)
    assert be.solve_query(be.generalize_array_terms(F), 3000) == "sat"
    assert be.refute_over_bv_abstraction(F, 3000)[1] != "unsat"


def _prover():
    return be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)


def test_opaque_array_uf_query_right_after_unification():
    # Unification merges the lambda arguments (pointwise, under v == M[k]); the two
    # sha3 applications are then one term and the opaque query refutes at once.
    F = And(v == Select(M, k), ULT(sha3(L_store, n), 5), ULT(5, sha3(L_plain, n)))
    proved, answer, lemmas = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer == "unsat"
    names = [l.name for l in lemmas]
    assert "opaque_array_uf" in names, names
    assert all(l.answer == "unsat" for l in lemmas)
    assert be.solve_query(simplify(proved), 3000) == "unsat"


def test_opaque_array_uf_soundness_satisfiable_formula_is_not_refuted():
    # n2 == n merges (a lemma, so the opaque query runs) but the slices differ:
    # sha3 may map them to 0 and 9, so the formula is SAT.
    F = And(n2 == n, ULT(sha3(L_plain, n), 5), ULT(5, sha3(L_shift, n2)))
    _, answer, _ = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer != "unsat"
    records = []
    assert not _prover()._check("e_sat", F, records)
