"""Isolation routing must count divisions by a literal: they still blast a full divider."""
from z3 import BitVec, BitVecVal, URem, UDiv, ZeroExt, simplify

from common.arithmetic import mulmod_semantics
from common.isolated_sat import expensive_bitblast

A, B = BitVec("eb_a", 256), BitVec("eb_b", 256)


def test_mulmod_by_literal_modulus_is_expensive_after_simplify():
    formula = simplify(mulmod_semantics(A, B, BitVecVal((1 << 256) - 1, 256)) == 0)
    assert expensive_bitblast(formula)


def test_symbolic_modulus_still_expensive():
    assert expensive_bitblast(simplify(mulmod_semantics(A, B, BitVec("eb_m", 256)) == 0))


def test_power_of_two_and_narrow_literal_divisions_stay_cheap():
    wide = ZeroExt(256, A) * ZeroExt(256, B)
    assert not expensive_bitblast(URem(ZeroExt(256, A), BitVecVal(1 << 255, 512)) == 0)
    assert not expensive_bitblast(UDiv(BitVec("eb_x", 64), BitVecVal(10, 64)) == 0)
    assert expensive_bitblast(URem(wide, BitVecVal(10, 512)) == 0)
