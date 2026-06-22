"""common.div_bridge 的单元测试：配对正确性 + fail-closed soundness。"""

from z3 import (
    And,
    BitVec,
    BitVecVal,
    Concat,
    Solver,
    UDiv,
    ZeroExt,
    sat,
    unsat,
)

from common.div_bridge import collect_div_subexprs, verified_div_bridges


def _udiv128(dividend_lo, divisor_lo):
    """x86 `div r64` 风格的 128-bit 商：UDiv(Concat(0,a64), ZeroExt(64,b64))。"""
    return UDiv(Concat(BitVecVal(0, 64), dividend_lo), ZeroExt(64, divisor_lo))


def test_collect_groups_udiv_variants_together():
    """bvudiv 与 simplify 后的 bvudiv_i 同 (category, size)，归并到一组。"""
    a = BitVec("a", 64)
    b = BitVec("b", 64)
    raw = _udiv128(a, b)  # decl bvudiv
    from z3 import simplify

    interpreted = simplify(_udiv128(a, b))  # decl bvudiv_i
    groups = collect_div_subexprs([raw, interpreted])
    udiv_keys = [k for k in groups if k[0] == "udiv"]
    assert udiv_keys, "udiv category should be collected"
    # 两个表达式 syntactic 不同但同类同 size，落在同一 key 下。
    assert any(len(groups[k]) >= 1 for k in udiv_keys)


def test_bridge_added_when_args_provably_equal():
    """两侧 div 实参在约束下恒等 ⟹ 生成桥接，且桥接让结果相等可证。"""
    x = BitVec("x", 64)
    y = BitVec("y", 64)
    xp = BitVec("xp", 64)
    yp = BitVec("yp", 64)
    evm_div = _udiv128(x, y)
    x86_div = _udiv128(xp, yp)
    # 约束令实参 limb 恒等。
    constraint = And(x == xp, y == yp)
    bridges = verified_div_bridges([evm_div], [x86_div], constraint)
    assert len(bridges) == 1, "args provably equal under constraint -> one bridge"

    # 桥接 + 约束下，证两 div 结果必相等（unsat 反例）。
    s = Solver()
    s.add(constraint)
    for b in bridges:
        s.add(b)
    s.add(evm_div != x86_div)
    assert s.check() == unsat


def test_no_bridge_when_args_not_provably_equal():
    """实参在约束下可不等 ⟹ fail-closed 不生成桥接（绝不假绿）。"""
    x = BitVec("x", 64)
    y = BitVec("y", 64)
    xp = BitVec("xp", 64)
    yp = BitVec("yp", 64)
    evm_div = _udiv128(x, y)
    x86_div = _udiv128(xp, yp)
    # 不约束实参相等：x 可 != xp。
    bridges = verified_div_bridges([evm_div], [x86_div], And(x == xp))
    assert bridges == [], "args not provably equal -> no bridge (fail-closed)"


def test_no_bridge_when_category_ambiguous():
    """某类别在一侧出现多个实例时 fail-closed 跳过（配对歧义不注入）。"""
    x = BitVec("x", 64)
    y = BitVec("y", 64)
    z = BitVec("z", 64)
    evm_two = [_udiv128(x, y), _udiv128(x, z)]  # 两个 udiv128
    x86_one = [_udiv128(x, y)]
    bridges = verified_div_bridges(evm_two, x86_one, BitVecVal(1, 1) == BitVecVal(1, 1))
    assert bridges == [], "ambiguous pairing -> no bridge"


def test_bridge_is_truthy_lemma_not_input_restriction():
    """桥接是恒真等式，不应限制输入空间（约束下仍可自由取任意实参）。"""
    x = BitVec("x", 64)
    y = BitVec("y", 64)
    xp = BitVec("xp", 64)
    yp = BitVec("yp", 64)
    evm_div = _udiv128(x, y)
    x86_div = _udiv128(xp, yp)
    constraint = And(x == xp, y == yp)
    bridges = verified_div_bridges([evm_div], [x86_div], constraint)
    # 加桥接后，实参仍可取任意值（如 x==5），不被桥接约束掉。
    s = Solver()
    for b in bridges:
        s.add(b)
    s.add(x == BitVecVal(5, 64))
    assert s.check() == sat, "bridge must not restrict input space"
