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


def test_collect_handles_deeper_nesting_than_python_recursion_limit():
    """深层嵌套不得撑爆 Python 递归——遍历必须是显式栈。

    曾经是递归 walker，在默认上限 1000 处抛 RecursionError，而"修法"是调高
    recursionlimit——只盖住 pytest，CLI 照样崩。所以这条**刻意跑在默认上限上**。
    """
    import sys

    limit = sys.getrecursionlimit()
    depth = limit * 3               # 远超递归版能承受的深度

    a, b = BitVec("deep_a", 64), BitVec("deep_b", 64)
    node = _udiv128(a, b)
    for _ in range(depth):
        node = node + BitVecVal(1, 128)

    grouped = collect_div_subexprs(node)

    assert len(grouped) == 1, "埋在深处的 UDiv 没被收集到"
    assert sum(len(v) for v in grouped.values()) == 1


def test_uf_named_like_builtin_division_is_never_bridged():
    """名字不是语义：同名 UF 冒充 bvudiv/bvurem 时不得产生桥接（否则可把 sat 证成 unsat）。"""
    from z3 import BitVecSort, Function, URem

    a, b = BitVec("uf_a", 8), BitVec("uf_b", 8)
    for name, op in (("bvudiv", UDiv), ("bvurem", URem)):
        fake = Function(name, BitVecSort(8), BitVecSort(8), BitVecSort(8))
        assert verified_div_bridges([op(a, b)], [fake(a, b)], a == 9) == []


def test_holiman_ufs_pair_only_with_the_same_declaration():
    from z3 import BitVecSort, Function

    a, b, ap, bp = (BitVec(n, 8) for n in ("h_a", "h_b", "h_ap", "h_bp"))
    same = Function("holiman_udiv", BitVecSort(8), BitVecSort(8), BitVecSort(8))
    assert len(verified_div_bridges([same(a, b)], [same(ap, bp)], And(a == ap, b == bp))) == 1
    x, y = BitVec("h_x", 16), BitVec("h_y", 16)
    wide = Function("holiman_udiv", BitVecSort(16), BitVecSort(8), BitVecSort(8))
    assert verified_div_bridges([same(a, b)], [wide(x, b)], a == 1) == []


def test_raw_and_simplified_division_still_bridge():
    """bvudiv 与 simplify 后的 bvudiv_i 同语义（含除 0），仍应配对。"""
    from z3 import simplify

    x, y, xp, yp = (BitVec(n, 64) for n in ("r_x", "r_y", "r_xp", "r_yp"))
    raw, interpreted = _udiv128(x, y), simplify(_udiv128(xp, yp))
    assert raw.decl().kind() != interpreted.decl().kind()
    assert len(verified_div_bridges([raw], [interpreted], And(x == xp, y == yp))) == 1
