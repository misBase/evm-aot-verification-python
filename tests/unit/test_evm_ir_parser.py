#!/usr/bin/env python3
"""测试EVM IR JSON解析器。"""

import os

from evm_ir.json_parser import load_ir_from_json
from evm_ir.models import EvmOperator


def test_operator_parses_immediate_set():
    """resolved_multi JUMP 携带 immediate_set（十进制字符串列表）。

    P1 前置：loop pairing 守卫必须能用它区分 resolved_multi 与真正的
    dynamic_unresolved 跳转。
    """
    op = EvmOperator.from_json({
        "kind": "JUMP",
        "pc": 973,
        "immediate_set": ["974", "1024"],
    })

    assert op.immediate_set == [974, 1024]
    assert op.immediate is None
    assert not op.is_static

    # round-trip
    assert op.to_json()["immediate_set"] == [974, 1024]


def test_operator_without_immediate_set_defaults_to_none():
    op = EvmOperator.from_json({"kind": "JUMP", "pc": 1, "immediate": "7", "is_static": True})

    assert op.immediate_set is None
    assert "immediate_set" not in op.to_json()


def test_json_parsing():
    """测试从JSON文件解析EVM IR。"""
    # 获取示例IR文件的路径
    test_dir = os.path.dirname(__file__)
    ir_file = os.path.join(test_dir, "..", "data", "add_with_push.json")
    
    # 从JSON加载IR
    ir_result = load_ir_from_json(ir_file)
    
    # 验证解析结果结构
    assert ir_result is not None, "IR result should not be None"
    assert len(ir_result.blocks) > 0, "IR should contain at least one block"
    
    # 验证块结构
    block = ir_result.blocks[0]
    assert hasattr(block, 'pc'), "Block should have PC attribute"
    assert hasattr(block, 'stack_depth'), "Block should have stack_depth attribute"
    assert hasattr(block, 'operations'), "Block should have operations attribute"
    assert len(block.operations) > 0, "Block should have at least one operation"
    
    # 验证操作结构
    for op in block.operations:
        assert hasattr(op, 'kind'), "Operation should have kind attribute"
        assert hasattr(op, 'pc'), "Operation should have pc attribute"
    
    # 验证example_ir.json中的特定操作
    operation_kinds = [op.kind.upper() for op in block.operations]
    assert 'TAG' in operation_kinds, "Should contain TAG operation"
    assert 'PUSH' in operation_kinds, "Should contain PUSH operation"
    assert 'ADD' in operation_kinds, "Should contain ADD operation"
    assert 'STOP' in operation_kinds, "Should contain STOP operation"
    
    # 验证PUSH操作有立即值
    push_ops = [op for op in block.operations if op.kind.upper().startswith('PUSH')]
    for push_op in push_ops:
        assert push_op.immediate is not None, f"PUSH operation at pc={push_op.pc} should have immediate value"

