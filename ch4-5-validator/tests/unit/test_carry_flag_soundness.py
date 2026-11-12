"""_carry_flag rewrites the top bit of a sum; every rewrite it returns must be an exact identity."""
import pytest
from z3 import BitVec, BitVecVal, Concat, Extract, If, Solver, sat, simplify

from verification.block_equivalence import _carry_flag

N = 6
A, B = BitVec("cf_a", N - 1), BitVec("cf_b", N - 1)
ZA, ZB = Concat(BitVecVal(0, 1), A), Concat(BitVecVal(0, 1), B)
FREE = BitVec("cf_free", N)
NEG = BitVecVal((1 << N) - 1, N)


@pytest.mark.parametrize("make", [
    lambda c: c + ZA + ZB,
    lambda c: c + ZA,
    lambda c: c + ZA + NEG * ZB,
    lambda c: c + ZA + FREE,       # unclassified summand: must not be dropped
    lambda c: ZA + ZB + FREE,
])
@pytest.mark.parametrize("c", [0, 1, 20, 31, 33, 63])
def test_every_returned_rewrite_is_exact(make, c):
    e = Extract(N - 1, N - 1, simplify(make(BitVecVal(c, N))))
    rewrite = _carry_flag(e)
    if rewrite is None:
        return
    solver = Solver()
    solver.add(e != If(rewrite, BitVecVal(1, 1), BitVecVal(0, 1)))
    assert solver.check() != sat, f"unsound carry rewrite for {e}"


def test_unclassified_summand_blocks_the_rewrite():
    assert _carry_flag(Extract(N - 1, N - 1, simplify(BitVecVal(1, N) + ZA + FREE))) is None
