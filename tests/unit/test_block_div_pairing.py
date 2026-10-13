"""SafeMath mul-overflow check (CErc20 pc=14263): `a == 0 || (a*b)/a == b`.

x86 takes compileEVMDiv's `divisor > dividend -> 0` branch, so no division
is left to pair with EVM's holiman_udiv; that arm is dead only if both
products agree. They are built differently: EVM holiman Mul(top, second),
x86 compileEVMMul Mul(second, top) replayed in machine add order, low limb
reloaded byte-wise. Bit-blasting cannot relate them; the LIA route can.
"""

from random import Random

from z3 import (And, BitVec, BitVecVal, Concat, Extract, If, Not, Or, SolverFor, ULT, ZeroExt, is_true,
                simplify, substitute, unsat)

from common.uint256 import Uint256
from evm_ir.semantics import EVMOperationSemantics
from verification.block_equivalence import BlockEquivalenceProver
from verification.linear_encoding import lia_query, split_limb_joins
from x86_64.summaries.mul_proof import _mul64, _umul_hop, _umul_step_x86_order


def _limbs(name):
    return [BitVec(f"{name}_z{i}", 64) for i in range(4)]


def _x86_mul(p, q):
    """compileEVMMul limb order (p = second, q = top), x86 add order."""
    carry0, z0 = _mul64(p[0], q[0])
    carry0, res1 = _umul_hop(carry0, p[1], q[0])
    carry0, res2 = _umul_hop(carry0, p[2], q[0])
    carry1, z1 = _umul_hop(res1, p[0], q[1])
    carry1, res2 = _umul_step_x86_order(res2, p[1], q[1], carry1)
    carry2, z2 = _umul_hop(res2, p[0], q[2])
    return [z0, z1, z2, p[3] * q[0] + p[2] * q[1] + p[0] * q[3] + p[1] * q[2] + carry0 + carry1 + carry2]


def _below(x, y):
    return x.lt_semantics(y)  # SUB/SBB borrow chain, as compileSubValuesForCompare


def _at_most(x, y):
    return Not(y.lt_semantics(x))


def _obligation(x86_compare=_below, full=True):
    """x86 path (no jump) ∧ EVM jumps; UNSAT iff the branch agrees.

    full=False keeps only the core: EVM DIV skipping its `y > x -> 0` arm.
    """
    top, second = _limbs("s10"), _limbs("s11")  # after DUP1 DUP3: s10 on top
    a, b = Concat(*reversed(top)), Concat(*reversed(second))
    ops = EVMOperationSemantics()
    product = ops.mul_semantics(a, b)
    quotient = ops.div_semantics(product, b)
    evm_jumps = Or(b == 0, quotient == a) if full else Not(Uint256.from_bv256(product).lt_semantics(Uint256(*second)))
    x86 = _x86_mul(second, top)
    low = simplify(Extract(7, 0, x86[0]), bv_sort_ac=True)  # byte-wise reload of the low limb
    x86[0] = Concat(Extract(63, 8, x86[0]), low)
    # divisor != 0, dividend < divisor -> quotient 0; EQ against a fails at limb 0
    x86_no_jump = And(b != 0, x86_compare(Uint256(*x86), Uint256(*second)), top[0] != 0)
    return And(x86_no_jump, evm_jumps), top, second


def test_obligation_mentions_holiman_udiv_only_on_evm_side():
    formula, _, _ = _obligation()
    assert "holiman_udiv" in formula.sexpr()


def test_lia_refutes_swapped_x86_order_product():
    x, y = _limbs("x"), _limbs("y")
    evm = Uint256(*x).mul_semantics(Uint256(*y))
    x86 = _x86_mul(y, x)
    differ = Or(*[getattr(evm, f"z{i}") != x86[i] for i in range(4)])
    solver = SolverFor("QF_LIA")
    solver.set("timeout", 30_000)
    solver.add(lia_query(simplify(differ, bv_sort_ac=True)))
    assert solver.check() == unsat


def test_block_check_proves_branch_agreement_via_lia():
    formula, _, _ = _obligation(full=False)
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=30_000)
    records = []
    assert prover._check("pair", formula, records)
    names = [lemma.name for lemma in records[-1].lemmas]
    assert "lia" in names and any(n.startswith("join_") for n in names)


def test_lia_route_rejects_real_divergence():
    # x86 compares with <= : at P == b (a == 1) EVM's DIV leaves its 0 arm.
    formula, top, second = _obligation(x86_compare=_at_most, full=False)
    witness = [(v, BitVecVal(1 if v.eq(top[0]) else 5 if v.eq(second[0]) else 0, 64)) for v in top + second]
    assert is_true(simplify(substitute(formula, *witness)))  # genuinely SAT
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=30_000)
    proved, answer, lemmas = prover._retry_over_lia(formula)
    assert answer == "unknown" and lemmas == () and proved.eq(formula)


def test_lia_encoding_is_exact_on_the_linear_fragment():
    x, y = BitVec("x", 64), BitVec("y", 64)
    carry = Extract(64, 64, ZeroExt(1, x) + ZeroExt(1, y))
    term = Concat(carry, Extract(63, 8, x + y * 3) | Extract(55, 0, ~y)) + Extract(56, 0, If(ULT(x, y), x, y))
    rng = Random(7)
    for _ in range(20):
        values = [(x, BitVecVal(rng.getrandbits(64), 64)), (y, BitVecVal(rng.getrandbits(64), 64))]
        expected = simplify(substitute(term, *values))
        for value, answer in ((expected, "sat"), (expected + 1, "unsat")):
            solver = SolverFor("QF_LIA")
            solver.add(lia_query(And(*[v == c for v, c in values], term == value)))
            assert str(solver.check()) == answer


def test_opaque_products_keep_only_valid_bounds():
    a, b = BitVec("a", 64), BitVec("b", 64)
    wide = ZeroExt(64, a) * ZeroExt(64, b)
    for formula, answer in ((wide == BitVecVal((1 << 128) - 1, 128), "unsat"),  # (2^64-1)^2 < 2^128-1
                            (wide == BitVecVal((1 << 64) - 1, 128) * ((1 << 64) - 1), "sat"),
                            (a * b == BitVecVal((1 << 64) - 1, 64), "sat")):  # wrapping product: no bound
        solver = SolverFor("QF_LIA")
        solver.add(lia_query(formula))
        assert str(solver.check()) == answer


def test_split_limb_join_requires_the_real_low_part():
    x, y = BitVec("x", 64), BitVec("y", 64)
    limb = x * y + x
    low = simplify(Extract(7, 0, limb), bv_sort_ac=True)
    assert len(split_limb_joins(Concat(Extract(63, 8, limb), low) == 0)) == 1
    assert split_limb_joins(Concat(Extract(63, 8, limb), low + 1) == 0) == []
    assert split_limb_joins(Concat(Extract(63, 8, limb), Extract(7, 0, y)) == 0) == []
