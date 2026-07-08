#!/usr/bin/env python3
"""store_forwarding 归一化器单元测试。"""

from z3 import (
    Array, BitVec, BitVecSort, BitVecVal, Concat, Extract, Lambda, Select,
    Store, simplify, is_true, eq,
)

from common.store_forwarding import (
    forward_selects,
    linearize_address,
    resolve_select_over_store,
    unshift_store_chain,
)

B = BitVec("B", 64)
O = BitVec("O", 64)
ARR = Array("A", BitVecSort(64), BitVecSort(8))
V1 = BitVec("v1", 8)
V2 = BitVec("v2", 8)


def test_linearize_groups_terms_and_constants():
    key1, c1 = linearize_address(B + O + 5 + 3)
    key2, c2 = linearize_address(3 + O + B + 5)
    assert key1 == key2 and c1 == c2 == 8

    key3, c3 = linearize_address(B + 5)
    assert key3 != key1


def test_resolve_hit_and_skip():
    chain = Store(Store(ARR, B + O + 1, V1), B + O + 2, V2)
    # 命中最外层
    assert eq(resolve_select_over_store(Select(chain, B + O + 2)), V2)
    # 跳过外层（判异）命中内层
    assert eq(resolve_select_over_store(Select(chain, B + O + 1)), V1)
    # 全链判异：剥到链底
    stripped = resolve_select_over_store(Select(chain, B + O + 7))
    assert stripped is not None
    assert eq(stripped, Select(ARR, B + O + 7))


def test_resolve_bails_on_unknown_base():
    other = BitVec("other", 64)
    chain = Store(ARR, other, V1)  # 异基：可能别名
    assert resolve_select_over_store(Select(chain, B + O)) is None


def test_forward_selects_rewrites_nested():
    chain = Store(ARR, B + 8, V1)
    expr = Concat(Select(chain, B + 8), Select(chain, B + 9))
    rewritten = forward_selects(expr)
    assert eq(rewritten, Concat(V1, Select(ARR, B + 9)))


def test_unshift_store_chain_removes_lambda_view():
    mem0 = Array("mem0", BitVecSort(64), BitVecSort(8))
    r15 = BitVec("r15", 64)
    addr = BitVec("__a", 64)
    view = Lambda([addr], Select(mem0, addr - r15))
    chain = Store(Store(view, r15 + 5, V1), r15 + O + 9, V2)

    unshifted = unshift_store_chain(chain, r15, mem0)
    assert unshifted is not None
    expected = Store(Store(mem0, BitVecVal(5, 64), V1), BitVecVal(9, 64) + O, V2)
    # 结构可能项序不同，用 z3 判等价（具体地址代入）
    from z3 import Solver, Not, unsat
    s = Solver()
    s.add(Not(unshifted == expected))
    assert s.check() == unsat


def test_unshift_bails_without_base_term():
    mem0 = Array("mem0", BitVecSort(64), BitVecSort(8))
    r15 = BitVec("r15", 64)
    chain = Store(mem0, BitVecVal(5, 64), V1)  # 地址不含 r15
    assert unshift_store_chain(chain, r15, mem0) is None
