"""pin_split: case split on ITE conditions that pin initial-memory bytes (BlockEquivalenceProver._check)."""
from z3 import And, Array, BitVec, BitVecSort, If, Select, Solver, unsat

import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver, pin_split

MEM = Array("pin_mem0", BitVecSort(64), BitVecSort(8))
X, Y = BitVec("pin_x", 64), BitVec("pin_y", 64)
# fmp == 0x40 as the simplifier writes it: one byte pin per byte of the word.
PINNED = And(Select(MEM, 0x5e) == 0, Select(MEM, 0x5f) == 0x40)
READ = If(PINNED, X, Y)


def _unsat(formula):
    solver = Solver()
    solver.add(formula)
    return solver.check() == unsat


def test_both_sides_refuted_gives_residual_and_case_proofs():
    split = pin_split(And(READ == 3, X != 3, Y != 3), 3000)
    assert split not in (None, "sat")
    residual, lemmas = split
    assert [l.name for l in lemmas] == ["pin_case_0"] and all(l.proved for l in lemmas)
    assert _unsat(residual)


def test_satisfiable_case_is_a_model_of_the_formula():
    assert pin_split(And(READ == 3, Y != 3), 3000) == "sat"


def test_residual_keeps_the_unpinned_models():
    # Refuted only when fmp is pinned: the residual must stay satisfiable.
    residual, _ = pin_split(And(READ == 3, X != 3), 3000)
    assert not _unsat(residual)


def test_no_pinned_condition_is_not_applicable():
    assert pin_split(And(If(X == 1, X, Y) == 3, Y != 3), 3000) is None
    # A pin on a symbolic index is not a concrete memory word.
    assert pin_split(And(If(Select(MEM, X) == 1, X, Y) == 3, Y != 3), 3000) is None


def _unknown_first(monkeypatch):
    real, calls = be.solve_query, []

    def fake(formula, timeout_ms):
        calls.append(formula)
        return "unknown" if len(calls) == 1 else real(formula, timeout_ms)
    monkeypatch.setattr(be, "solve_query", fake)


def test_check_proves_with_the_case_proofs_as_lemmas(monkeypatch):
    _unknown_first(monkeypatch)
    records = []
    assert BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair_0_0", And(READ == 3, X != 3, Y != 3),
                                                                      records)
    assert "pin_case_0" in [l.name for l in records[-1].lemmas]


def test_check_reports_a_satisfiable_case(monkeypatch):
    _unknown_first(monkeypatch)
    records = []
    assert not BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair_0_0", And(READ == 3, Y != 3),
                                                                          records)
    assert records[-1].answer == "sat"
