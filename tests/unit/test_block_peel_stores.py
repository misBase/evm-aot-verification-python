"""Safe 5377 d30 pair_68_58: peel matching stores off a memory disequality.

Select(C_A, i) != Select(C_B, j) over store chains whose outer stores pair up
(same value, addresses b - a = j - i) implies Select(A, i) != Select(B, j) for
the arrays below them; only UNSAT of the peeled formula transfers back.
"""
import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Function, If, Lambda, Not, Select, Store,
                ULT, simplify)

import verification.block_equivalence as be

BV64, BV8 = BitVecSort(64), BitVecSort(8)
A, B, M = (Array(f"ps_{s}", BV64, BV8) for s in "ABM")
f, r, w, k, n, d = (BitVec(f"ps_{s}", 64) for s in "frwknd")
x, y, z = (BitVec(f"ps_p{s}", 64) for s in "xyz")
v1, v2, v = (BitVec(f"ps_v{s}", 8) for s in ("1", "2", ""))
i = BitVec("ps_i", 64)
sha3 = Function("ps_sha3_slice", ArraySort(BV64, BV8), BV64, BV64)


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _chains(base_a, base_b, shift):
    """EVM-style chain at f + c and an x86-style chain at shift + f + c (same values)."""
    ca = Store(Store(base_a, f, v1), f + 1, v2)
    cb = Store(Store(base_b, shift + f, v1), shift + f + 1, v2)
    return ca, cb


def test_peel_store_pair_peels_matching_stores_under_a_shift():
    ca, cb = _chains(A, B, r)
    peeled = be._peel_store_pair(Select(ca, w), Select(cb, r + w))
    assert peeled is not None
    assert peeled[0].eq(Select(A, w)) and peeled[1].eq(Select(B, r + w))
    ca, cb = _chains(A, B, BitVecVal(0, 64))  # no shift: same addresses
    assert be._peel_store_pair(Select(ca, w), Select(cb, w))[1].eq(Select(B, w))


def test_peel_store_pair_stops_at_the_first_mismatch():
    # Outer values differ: nothing peeled.
    ca = Store(Store(A, f, v1), f + 1, v2)
    cb = Store(Store(B, f, v1), f + 1, v1)
    assert be._peel_store_pair(Select(ca, w), Select(cb, w)) is None
    # Address offset r + 1 against a read shift of r: nothing peeled.
    cb = Store(Store(B, r + f, v1), r + f + 2, v2)
    assert be._peel_store_pair(Select(ca, w), Select(cb, r + w)) is None
    # Inner pair mismatches: only the outer store is peeled.
    cb = Store(Store(B, r + f + 5, v1), r + f + 1, v2)
    peeled = be._peel_store_pair(Select(ca, w), Select(cb, r + w))
    assert peeled[0].eq(Select(Store(A, f, v1), w)) and peeled[1].eq(Select(Store(B, r + f + 5, v1), r + w))
    assert be._peel_store_pair(Select(A, w), Select(B, w)) is None  # no stores


def test_mismatched_stores_are_not_peeled_into_a_false_refutation():
    # Same value at f and f + 1 over the same base: SAT (w = f, A[f] != v1). Peeling across the
    # address mismatch would leave A[w] != A[w], which is UNSAT.
    F = Select(Store(A, f, v1), w) != Select(Store(A, f + 1, v1), w)
    assert be.solve_query(F, 5000) == "sat"
    assert be.peel_matching_stores(F) is None
    G = And(_merged_sha3(), x * y == z, F)
    _, answer, _ = _prover()._retry_with_uf_unification(G, "unknown")
    assert answer != "unsat"
    # Same for different values at the same address (w = f, v1 != v2).
    F = Select(Store(A, f, v1), w) != Select(Store(A, f, v2), w)
    assert be.solve_query(F, 5000) == "sat"
    assert be.peel_matching_stores(F) is None


def test_peel_step_is_implied_for_every_value():
    # The lemma behind one peel, with every term free: Store(A, a, u)[i] != Store(B, a + d, u)[i + d]
    # implies A[i] != B[i + d].
    a, u = BitVec("ps_a", 64), BitVec("ps_u", 8)
    q = And(Select(Store(A, a, u), i) != Select(Store(B, a + d, u), i + d), Select(A, i) == Select(B, i + d))
    assert be.solve_query(q, 5000) == "unsat"


def test_peeled_formula_is_implied_by_the_original():
    ca, cb = _chains(A, Lambda([i], Select(A, i - r)), r)
    F = And(ULT(w, n), Select(ca, w) != Select(cb, r + w))
    peeled = be.peel_matching_stores(F)
    assert peeled is not None
    assert be.solve_query(And(F, Not(peeled)), 5000) == "unsat"  # F ⊨ F'
    assert be.peel_matching_stores(And(ULT(w, n), Select(A, w) != Select(B, w))) is None


def test_peeling_can_lose_a_proof_only():
    # The stores cover the one cell where the bases differ: F is UNSAT, F' is SAT.
    base_a = Lambda([i], If(i == f, BitVecVal(1, 8), Select(M, i)))
    ca, cb = _chains(base_a, M, BitVecVal(0, 64))
    F = Select(ca, w) != Select(cb, w)
    assert be.solve_query(F, 5000) == "unsat"
    assert be.solve_query(be.peel_matching_stores(F), 5000) == "sat"


def _prover():
    return be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)


def _merged_sha3():
    # unify_uf_arguments merges the two slices (v = M[k]); the hashes themselves are consistent.
    L_store = Lambda([i], If(ULT(i, n), Select(Store(M, k, v), i), BitVecVal(0, 8)))
    L_plain = Lambda([i], If(ULT(i, n), Select(M, i), BitVecVal(0, 8)))
    return And(v == Select(M, k), ULT(sha3(L_store, n), 5), ULT(sha3(L_plain, n), 6))


def test_opaque_array_uf_peeled_after_unification():
    # The two memories agree below their stores only under d = 0 (base B is A shifted by d):
    # the peeled goal A[w] != (λa. A[a - r - d])[r + w] is refuted with the product dropped.
    shifted = Lambda([i], Select(A, i - r - d))
    ca, cb = _chains(A, shifted, r)
    F = And(_merged_sha3(), d == 0, x * y == z, Select(ca, w) != Select(cb, r + w))
    proved, answer, lemmas = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer == "unsat"
    names = [l.name for l in lemmas]
    assert "opaque_array_uf_peeled" in names and "opaque_array_uf_light" not in names, names
    assert all(l.answer == "unsat" for l in lemmas)
    assert be.solve_query(simplify(proved), 3000) == "unsat"


def test_peeled_miss_falls_back_to_the_unpeeled_query():
    # UNSAT only through the stores (they overwrite the cell where the bases differ): the peeled
    # query is SAT, the proof comes from the unpeeled light query.
    base_a = Lambda([i], If(i == f, BitVecVal(1, 8), Select(M, i)))
    ca, cb = _chains(base_a, M, BitVecVal(0, 64))
    F = And(_merged_sha3(), x * y == z, Select(ca, w) != Select(cb, w))
    _, answer, lemmas = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer == "unsat"
    names = [l.name for l in lemmas]
    assert "opaque_array_uf_light" in names and "opaque_array_uf_peeled" not in names, names


def test_peeled_soundness_satisfiable_formula_is_not_refuted():
    # Bases differ below matching stores (d free): SAT, and nothing may refute it.
    shifted = Lambda([i], Select(A, i - r - d))
    ca, cb = _chains(A, shifted, r)
    F = And(_merged_sha3(), x * y == z, Select(ca, w) != Select(cb, r + w))
    _, answer, _ = _prover()._retry_with_uf_unification(F, "unknown")
    assert answer != "unsat"
