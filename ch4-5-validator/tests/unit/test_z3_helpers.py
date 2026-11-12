"""测试 Z3 辅助工具函数。"""

import pytest
from z3 import BitVecVal, If, BitVec, BitVecSort, Function
from utils.z3_helpers import (
    is_bv_const_value,
    get_bv_const_value,
    get_simplified_bv_const_value,
    expr_mentions_symbol,
    is_if_expression,
    extract_if_branches,
    analyze_jump_target,
    JumpTargetAnalysis
)


def test_is_bv_const_value():
    """测试常量 BitVec 检测。"""
    # 常量值
    assert is_bv_const_value(BitVecVal(42, 256))
    assert is_bv_const_value(BitVecVal(0, 256))

    # 符号值
    x = BitVec('x', 256)
    assert not is_bv_const_value(x)


def test_get_bv_const_value():
    """测试从 BitVecVal 提取整数值。"""
    assert get_bv_const_value(BitVecVal(42, 256)) == 42
    assert get_bv_const_value(BitVecVal(0, 256)) == 0

    x = BitVec('x', 256)
    assert get_bv_const_value(x) is None


def test_get_simplified_bv_const_value():
    """测试先化简再提取 BitVec 常量。"""
    assert get_simplified_bv_const_value(BitVecVal(40, 256) + BitVecVal(2, 256)) == 42

    x = BitVec('x', 256)
    assert get_simplified_bv_const_value(x + BitVecVal(0, 256)) is None


def test_expr_mentions_symbol_only_matches_uninterpreted_constants():
    """测试未解释常量名称扫描。"""
    calldata_size = BitVec("CallDataSize", 64)
    offset = BitVec("Offset", 64)
    same_named_func = Function("CallDataSize", BitVecSort(64), BitVecSort(64))

    assert expr_mentions_symbol(offset + calldata_size, "CallDataSize")
    assert not expr_mentions_symbol(offset, "CallDataSize")
    assert not expr_mentions_symbol(same_named_func(offset), "CallDataSize")


def test_is_if_expression():
    """测试 If 表达式检测。"""
    x = BitVec('x', 256)
    if_expr = If(x == 0, BitVecVal(10, 256), BitVecVal(20, 256))
    assert is_if_expression(if_expr)

    const = BitVecVal(42, 256)
    assert not is_if_expression(const)


def test_extract_if_branches():
    """测试提取 If 分支。"""
    x = BitVec('x', 256)
    if_expr = If(x == 0, BitVecVal(10, 256), BitVecVal(20, 256))

    cond, then_br, else_br = extract_if_branches(if_expr)
    assert then_br.as_long() == 10
    assert else_br.as_long() == 20


def test_analyze_jump_target_constant():
    """测试分析常量跳转目标。"""
    const_target = BitVecVal(42, 256)
    result = analyze_jump_target(const_target)

    assert result.is_static is True
    assert len(result.targets) == 1
    assert result.targets[0] == (42, None)


def test_analyze_jump_target_if():
    """测试分析 If 表达式跳转目标。"""
    x = BitVec('x', 256)
    if_target = If(x == 0, BitVecVal(10, 256), BitVecVal(20, 256))

    result = analyze_jump_target(if_target)

    assert result.is_static is True
    assert len(result.targets) == 2
    assert result.targets[0][0] == 10
    assert result.targets[1][0] == 20


def test_analyze_jump_target_nested_if():
    """测试分析嵌套 If 表达式。"""
    x = BitVec('x', 256)
    y = BitVec('y', 256)
    nested_if = If(
        x == 0,
        If(y == 0, BitVecVal(10, 256), BitVecVal(20, 256)),
        BitVecVal(30, 256)
    )

    result = analyze_jump_target(nested_if)

    assert result.is_static is True
    # 应该提取出 3 个目标：10, 20, 30
    assert len(result.targets) == 3
    target_pcs = [t[0] for t in result.targets]
    assert 10 in target_pcs
    assert 20 in target_pcs
    assert 30 in target_pcs


def test_analyze_jump_target_dynamic():
    """测试分析动态（符号）跳转目标。"""
    x = BitVec('x', 256)
    result = analyze_jump_target(x)

    assert result.is_static is False
    assert len(result.targets) == 0
