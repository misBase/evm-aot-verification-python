"""value_cut over-approximates: its UNSAT must be the original formula's UNSAT, never the reverse."""
import random
import sys
import time

import pytest

from z3 import (UGT, ULT, And, BitVec, BitVecVal, Concat, Extract, If, Not, Or, Solver, SolverFor, URem, UDiv,
                ZeroExt, is_false, sat, simplify, unsat)

import common.isolated_sat as isolated
from common.arithmetic import mulmod_semantics
from verification.block_equivalence import refute_divrem_congruence, value_cut

W = 6


def _random_term(rng, leaves, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(leaves)
    x, y = _random_term(rng, leaves, depth - 1), _random_term(rng, leaves, depth - 1)
    op = rng.choice(["mul", "urem", "udiv", "add", "sub", "wide"])
    if op == "mul":
        return x * y
    if op == "urem":
        return URem(x, y)
    if op == "udiv":
        return UDiv(x, y)
    if op == "add":
        return x + y
    if op == "sub":
        return x - y
    return Extract(W - 1, 0, URem(ZeroExt(W, x) * ZeroExt(W, y), ZeroExt(W, y | BitVecVal(1, W))))


def test_abstraction_unsat_implies_exact_unsat_on_random_formulas():
    rng = random.Random(5)
    leaves = [BitVec(n, W) for n in ("vx", "vy", "vz")] + [BitVecVal(v, W) for v in (0, 1, 7, 63)]
    checked = 0
    for _ in range(300):
        s, t = _random_term(rng, leaves, 3), _random_term(rng, leaves, 3)
        f = rng.choice([s != t, ULT(s, t), And(s == t, UGT(t, s)), Or(s == t, s != t)])
        cut, changed = value_cut(f)
        if not changed:
            continue
        abstract, exact = Solver(), Solver()
        abstract.add(cut)
        exact.add(f)
        if abstract.check() == unsat:
            assert exact.check() == unsat, f"value_cut refuted a satisfiable formula: {f}"
            checked += 1
    assert checked > 10  # the property was exercised, not vacuous


A, B, DEN = BitVec("vc_a", 256), BitVec("vc_b", 256), BitVec("vc_den", 256)
M = BitVecVal((1 << 256) - 1, 256)


def _prod1(mm, prod0):
    return mm - prod0 - If(ULT(mm, prod0), BitVecVal(1, 256), BitVecVal(0, 256))


def _limb_sub(x, y):
    """x - y as a limb borrow chain (two 128-bit limbs: the shape of x86 SUB/SBB, cheap to bit-blast)."""
    limbs, borrow = [], BitVecVal(0, 129)
    for i in range(2):
        d = (ZeroExt(1, Extract(128 * i + 127, 128 * i, x)) - ZeroExt(1, Extract(128 * i + 127, 128 * i, y))
             - borrow)
        limbs.append(Extract(127, 0, d))
        borrow = ZeroExt(128, Extract(128, 128, d))
    return Concat(*reversed(limbs))


def _x86_prod1(mm, prod0):
    return _limb_sub(_limb_sub(mm, prod0), If(ULT(mm, prod0), BitVecVal(1, 256), BitVecVal(0, 256)))


def _disagreement():
    """EVM: den > prod1 with word SUBs; x86: the same branch over limb SUB/SBB. They disagree on no input."""
    mm, prod0 = mulmod_semantics(A, B, M), A * B
    return UGT(DEN, _prod1(mm, prod0)) != UGT(DEN, _x86_prod1(mm, prod0))


def test_fullmath_branch_disagreement_refutes_without_512_bit_reasoning():
    disagree = _disagreement()
    assert not is_false(simplify(disagree))  # simplify alone does not decide it
    cut, changed = value_cut(disagree)
    assert changed and not isolated.expensive_bitblast(cut)
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", 60_000)
    solver.add(cut)
    assert solver.check() == unsat


def test_divrem_route_uses_the_value_cut_first():
    abstract, answer, records = refute_divrem_congruence(_disagreement(), 120_000)
    assert answer == "unsat" and records and all(r.proved for r in records)


def test_semantic_facts_are_not_claimed():
    # mulmod(0, b, M) == 0 needs the multiplication's meaning: the cut stays satisfiable.
    needs_meaning = And(A == 0, mulmod_semantics(A, B, M) != 0)
    cut, changed = value_cut(needs_meaning)
    solver = SolverFor("QF_AUFBV")
    solver.add(cut)
    assert changed and solver.check() == sat  # abstract SAT: proves nothing, falls through


@pytest.mark.skipif(sys.platform != "linux", reason="the isolated child's AS limit reads Linux /proc")
def test_isolated_refutation_probe_applies_the_value_cut():
    began = time.monotonic()
    answer = isolated.isolated_sat(_disagreement(), 120_000, rlimit=2_000_000_000, refute_probe=True)
    assert answer == "unsat", f"child probe answered {answer} after {time.monotonic() - began:.0f}s"
