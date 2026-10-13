"""RETURN at a symbolic fmp with symbolic msize (Safe pc=771 shape).

After UF unification merges x86's recomputed RETURN word count
((31 + 32*e) >> 5) with EVM's e, the pair is refuted only if MLOAD's
charge `9 - C(w0)` (w0 = msize >> 5 <= 2) cannot wrap. The multiplication
UF leaves C(w0) free, so the abstraction is SAT; reading the UF as bvmul
again over the unified formula (concretize_mul) refutes it.
"""
from z3 import And, BitVec, BitVecVal, Concat, Extract, LShR, Not, Solver, ULE, ULT, sat, unsat

from verification.block_equivalence import BlockEquivalenceProver, abstract_nonlinear_mul, concretize_mul

m, x, g = BitVec("rg_msize", 64), BitVec("rg_x", 64), BitVec("rg_gas", 64)


def cost(w):
    return 3 * w + LShR(w * w, 9)


def shape(msize_bound):
    w0, e = LShR(m, 5), LShR(x + 31, 5)
    z5 = BitVecVal(0, 5)
    k = Concat(z5, Extract(63, 5, 31 + 32 * Concat(z5, Extract(63, 5, x + 31))))  # x86 round trip
    return And(ULT(m, msize_bound), ULE(x, 137438953440),
               ULE(cost(e), g), ULE(cost(k), g + 1),  # same RETURN cost, two word-count forms
               ULT(9, cost(w0)))  # MLOAD charge 9 - C(w0) wraps


def check(formula):
    s = Solver()
    s.set(timeout=10000)
    s.add(formula)
    return s.check()


def test_concretize_undoes_the_abstraction():
    functions = {}
    f = shape(96)
    abstract, changed = abstract_nonlinear_mul(f, functions=functions)
    assert changed
    assert check(Not(concretize_mul(abstract, functions) == f)) == unsat


def test_wrap_is_refuted_via_exact_products():
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=10000)
    _, answer, lemmas = prover._retry_with_uf_unification(shape(96), "unknown")
    assert answer == "unsat"
    assert lemmas[-1].name == "exact" and all(l.answer == "unsat" for l in lemmas)


def test_real_counterexample_is_not_proved():
    # msize < 160 admits w0 = 4, C(4) = 12 > 9: a genuine model.
    formula = shape(160)
    assert check(formula) == sat
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    assert prover._retry_with_uf_unification(formula, "unknown")[1] != "unsat"
    records = []
    assert not prover._check("pair", formula, records)
    assert records[-1].answer == "sat"
