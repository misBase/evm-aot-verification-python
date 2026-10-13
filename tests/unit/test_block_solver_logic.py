"""Select the BV/array tactic only after checking the entire expression DAG."""
from z3 import (And, Array, BitVec, BitVecSort, BoolSort, ForAll, Int, IntSort,
                Lambda, Select, Solver, sat, unsat)
from verification.block_equivalence import _bv_array_formula, _solver


def test_bv_arrays_and_lambda_keep_their_semantics():
    x = BitVec("logic_x", 64)
    memory = Array("logic_mem", BitVecSort(64), BitVecSort(8))
    formula = Select(Lambda([x], Select(memory, x + 1)), x) != Select(memory, x + 1)
    assert _bv_array_formula(formula)
    solver = _solver(3000, formula)
    solver.add(formula)
    assert solver.check() == unsat


def test_ints_nested_array_sorts_and_quantifiers_use_general_solver():
    x = Int("logic_sp")
    a = Array("logic_int_array", IntSort(), BoolSort())
    assert not _bv_array_formula(x == 3)
    assert not _bv_array_formula(Select(a, x))
    y = BitVec("logic_bound", 8)
    assert not _bv_array_formula(ForAll([y], y == 0))
    formula = And(x > 1, x < 3)
    solver = _solver(3000, formula)
    solver.add(formula)
    assert solver.check() == sat
