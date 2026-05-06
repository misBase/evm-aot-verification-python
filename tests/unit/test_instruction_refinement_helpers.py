"""Tests for single-instruction refinement helper rewrites."""

from z3 import BitVec, BitVecVal, Concat, Extract, If, Solver, simplify, unsat

from tests.support.instruction_refinement import _normalize_refinement_bv


def _bytewise_zero_ite_concat(condition, source, high=255, low=0):
    return Concat(
        *[
            If(condition, BitVecVal(0, 8), Extract(offset + 7, offset, source))
            for offset in range(high - 7, low - 1, -8)
        ]
    )


def test_normalize_refinement_bv_folds_bytewise_zero_ite_concat():
    source = BitVec("source", 512)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)

    normalized = _normalize_refinement_bv(_bytewise_zero_ite_concat(condition, source))
    expected = If(condition, BitVecVal(0, 256), Extract(255, 0, source))

    solver = Solver()
    solver.add(normalized != expected)
    assert solver.check() == unsat


def test_normalize_refinement_bv_rejects_mixed_conditions():
    source = BitVec("source", 16)
    condition_a = BitVec("condition_a", 1) == BitVecVal(1, 1)
    condition_b = BitVec("condition_b", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition_a, BitVecVal(0, 8), Extract(15, 8, source)),
        If(condition_b, BitVecVal(0, 8), Extract(7, 0, source)),
    )

    assert _normalize_refinement_bv(expr).eq(simplify(expr))


def test_normalize_refinement_bv_rejects_mixed_sources():
    source_a = BitVec("source_a", 16)
    source_b = BitVec("source_b", 16)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition, BitVecVal(0, 8), Extract(15, 8, source_a)),
        If(condition, BitVecVal(0, 8), Extract(7, 0, source_b)),
    )

    assert _normalize_refinement_bv(expr).eq(simplify(expr))


def test_normalize_refinement_bv_rejects_non_contiguous_extracts():
    source = BitVec("source", 24)
    condition = BitVec("condition", 1) == BitVecVal(1, 1)
    expr = Concat(
        If(condition, BitVecVal(0, 8), Extract(23, 16, source)),
        If(condition, BitVecVal(0, 8), Extract(7, 0, source)),
    )

    assert _normalize_refinement_bv(expr).eq(simplify(expr))
