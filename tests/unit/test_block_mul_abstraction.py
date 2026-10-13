"""The multiplication retry may add models, but must never remove one."""
from z3 import BitVecs, BitVecSort, Function, Solver, And, sat, unsat

from verification.block_equivalence import abstract_nonlinear_mul


def answer(formula):
    solver = Solver()
    solver.set(timeout=3000)
    solver.add(formula)
    return solver.check()


def test_congruence_proves_without_multiplication_semantics():
    x, y, a, b = BitVecs("x y a b", 64)
    relaxed, changed = abstract_nonlinear_mul(And(x == a, y == b, x * y != a * b))
    assert changed and answer(relaxed) == unsat


def test_input_function_cannot_collide_with_the_fresh_abstraction():
    x, y = BitVecs("x y", 64)
    attacker = Function("__nlmul64_2", BitVecSort(64), BitVecSort(64), BitVecSort(64))
    original = x * y != attacker(x, y)
    relaxed, changed = abstract_nonlinear_mul(original)
    assert changed and answer(original) == sat and answer(relaxed) == sat


def test_relaxed_sat_does_not_establish_original_sat():
    x, y = BitVecs("x y", 8)
    original = And(x == 0, x * y != 0)
    relaxed, changed = abstract_nonlinear_mul(original)
    assert changed and answer(original) == unsat and answer(relaxed) == sat


def test_prover_uses_exact_solver_when_relaxation_is_sat():
    from verification.block_equivalence import BlockEquivalenceProver
    x, y = BitVecs("retry_x retry_y", 8)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    records = []
    assert prover._check("exact", And(x == 0, x * y != 0), records)
    assert not prover._check("mismatch", And(x == 2, y == 3, x * y != 7), records)
    assert records[-1].answer == "sat"
