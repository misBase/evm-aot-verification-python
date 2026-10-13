"""The "bvabs" route: a pure-BV over-approximation, bit-blasted after Ackermannization."""
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, Extract, Function, Lambda, Select, Store,
                ULE, ULT, ZeroExt)

import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver, generalize_array_terms, refute_over_bv_abstraction

MEM = BitVecSort(64), BitVecSort(8)


def _memory_cost(w):
    """EVM memory cost 3w + w²/512 in 64 bits, as the x86 codegen computes it."""
    return 3 * w + ZeroExt(9, Extract(63, 9, w * w))


def test_monotone_squares_refuted_with_the_bound():
    a, b = BitVec("ba_a", 64), BitVec("ba_b", 64)
    assert refute_over_bv_abstraction(And(ULE(a, b), ULT(b, 2 ** 32), ULT(b * b, a * a)), 20000)[1] == "unsat"


def test_wrapping_square_is_not_refuted():
    # b = 2^32 wraps b*b to 0 < a*a: the monotonicity axiom needs b < 2^32, so no proof.
    a, b = BitVec("bw_a", 64), BitVec("bw_b", 64)
    assert refute_over_bv_abstraction(And(ULE(a, b), ULT(b * b, a * a)), 20000)[1] != "unsat"


def test_returndatacopy_word_gas_carry_is_impossible():
    """Safe 4524's x86 OOG path: carry(3·words(len) + C(new) - C(old)) with old <= new < 2^32 words."""
    length, new, old = BitVec("rc_len", 64), BitVec("rc_new", 64), BitVec("rc_old", 64)
    words = ZeroExt(5, Extract(63, 5, 31 + length))
    delta = _memory_cost(new) - _memory_cost(old)
    carry = Extract(64, 64, ZeroExt(1, 3 * words) + ZeroExt(1, delta)) == 1
    formula = And(ULE(old, new), ULE(32 * new, 0x1FFFFFFFE0), ULT(new, 2 ** 59), carry)
    assert refute_over_bv_abstraction(formula, 60000)[1] == "unsat"
    # Without old <= new the difference can wrap: C(old) > C(new) is then a real model.
    loose = And(ULE(32 * new, 0x1FFFFFFFE0), ULT(new, 2 ** 59), ULT(old, 2 ** 32), carry)
    assert refute_over_bv_abstraction(loose, 60000)[1] == "sat"


def test_generalisation_keeps_congruence_per_array():
    i, j = BitVec("bg_i", 64), BitVec("bg_j", 64)
    a, b = Array("bg_A", *MEM), Array("bg_B", *MEM)
    f = Function("bg_f", BitVecSort(64), a.sort(), BitVecSort(8))
    assert refute_over_bv_abstraction(And(i == j, Select(a, i) != Select(a, j)), 5000)[1] == "unsat"
    assert refute_over_bv_abstraction(And(i == j, f(i, a) != f(j, a)), 5000)[1] == "unsat"
    # Different arrays: nothing links the applications, and nothing may.
    assert refute_over_bv_abstraction(And(i == j, f(i, a) != f(j, b)), 5000)[1] == "sat"


def test_generalisation_never_invents_a_refutation():
    """Read-over-write is forgotten: a formula refuted only through it stays unrefuted."""
    i, j = BitVec("bn_i", 64), BitVec("bn_j", 64)
    a = Array("bn_A", *MEM)
    formula = And(i == j, Select(Store(a, i, BitVecVal(1, 8)), j) != 1)
    generalized = generalize_array_terms(formula)
    assert "select" not in generalized.sexpr() and "store" not in generalized.sexpr()
    assert refute_over_bv_abstraction(formula, 5000)[1] == "sat"


def test_array_equalities_are_left_to_other_routes():
    a = Array("bl_A", *MEM)
    x = BitVec("bl_x", 64)
    assert refute_over_bv_abstraction(Lambda([x], Select(a, x)) != a, 5000)[1] == "unknown"


def test_route_proves_what_exact_solving_left_unknown(monkeypatch):
    a, b = BitVec("br_a", 64), BitVec("br_b", 64)
    monkeypatch.setattr(be, "solve_query", lambda formula, timeout_ms: "unknown")
    records = []
    formula = And(ULE(a, b), ULT(b, 2 ** 32), ULT(b * b, a * a))
    assert BlockEquivalenceProver([], [], {}, timeout_ms=5000)._check("pair_0_0", formula, records)
    assert records[-1].proved and "bvmul" not in records[-1].formula


def test_route_abstract_sat_is_not_a_counterexample(monkeypatch):
    a, b = BitVec("bs_a", 64), BitVec("bs_b", 64)
    monkeypatch.setattr(be, "solve_query", lambda formula, timeout_ms: "unknown")
    monkeypatch.setattr(be, "_LAST_RESORT_MS", 1000)
    records = []
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=2000)
    # Satisfiable only through wrap-around; the abstraction's SAT must not be reported as the answer.
    prover._check("pair_0_0", And(ULE(a, b), ULT(b * b, a * a)), records)
    assert records[-1].answer == "unknown" and not records[-1].proved


def test_normalised_route_refutes_host_call_congruence_over_memory_views(monkeypatch):
    """x86 passes f a byte read at R15 + q through its absolute-address view, EVM the same byte at q.

    Only after the offset-view rewrite are the two arguments one term; the plain
    abstraction gives them different constants (abstract SAT). Every other
    solve_query is forced "unknown" and the other routes fail, so the proof must
    come from bvabs on the normalised formula, with the rewrite's lemmas attached.
    """
    M = Array("hc_M", *MEM)
    r15, p, q, a = (BitVec(f"hc_{n}", 64) for n in ("r15", "p", "q", "a"))
    x86, evm = Lambda([a], Select(M, a - r15)), M
    for k in range(4):
        v = BitVec(f"hc_v{k}", 8)
        x86, evm = Store(x86, r15 + p + k, v), Store(evm, p + k, v)
    f = Function("hc_call", BitVecSort(8), BitVecSort(8))
    formula = And(f(Select(x86, r15 + q)) == 1, f(Select(evm, q)) != 1)
    assert refute_over_bv_abstraction(formula, 5000)[1] == "sat"
    real = be.solve_query
    # Only the (fresh-constant) offset-view step lemma may reach the solver.
    monkeypatch.setattr(be, "solve_query", lambda g, t: real(g, t) if "ov_step_" in g.sexpr() else "unknown")
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    monkeypatch.setattr(prover, "_retry_over_lia", lambda g: (g, "unknown", ()))
    monkeypatch.setattr(prover, "_retry_over_nonlinear_mul", lambda g, ans, split=False: (g, "unknown", ()))
    monkeypatch.setattr(prover, "_retry_with_uf_unification", lambda g, ans: (g, "unknown", ()))
    records = []
    assert prover._check("pair_0_0", formula, records)
    lemmas = records[-1].lemmas
    assert records[-1].proved and any(l.name.startswith("normalize_") for l in lemmas)
    assert any(s.name == "offset_view_step_lemma" for l in lemmas for s in l.lemmas)
