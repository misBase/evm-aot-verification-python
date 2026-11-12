#!/usr/bin/env python3
"""测试程序级等价性验证。"""

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from verification.program_verifier import ProgramEquivalenceChecker
import os


def test_program_verifier_import():
    """测试程序验证器是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


def test_evm_program_from_json():
    """测试从JSON创建EVM程序。"""
    # 获取测试IR文件路径
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_with_push.json")
    
    # 加载并创建程序
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    assert len(evm_program.blocks) > 0, \
        f"Program should have at least one block, got {len(evm_program.blocks)}"


def test_x86_program_from_hex():
    """测试从十六进制创建x86程序。"""
    # ADD操作的十六进制序列
    hex_sequence = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
    base_addr = 0x6c
    
    x86_program = X86Program.from_hex(hex_sequence, base_addr=base_addr)
    
    assert len(x86_program.instructions) > 0, \
        f"Program should have at least one instruction, got {len(x86_program.instructions)}"


def test_evm_program_contains_add_operation():
    """测试EVM程序结构和操作检测。

    此测试验证我们可以正确解析和检查EVM程序结构，
    包括在块内查找特定操作。
    """
    # 获取测试IR文件路径
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "add_with_push.json")
    
    # 加载EVM程序
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    # 验证程序结构
    assert len(evm_program.blocks) > 0, \
        f"EVM program should have at least one block, got {len(evm_program.blocks)}"
    
    # 测试我们可以找到ADD操作
    has_add = False
    add_count = 0
    for block in evm_program.blocks:
        assert len(block.operations) > 0, \
            f"Block should have at least one operation, got {len(block.operations)}"
        for op in block.operations:
            if op.kind.upper() == "ADD":
                has_add = True
                add_count += 1
    
    assert has_add, "EVM program should contain ADD operation"
    assert add_count > 0, f"Should find at least one ADD operation, found {add_count}"


if __name__ == "__main__":
    # 直接运行时，使用pytest运行测试
    import pytest
    pytest.main([__file__, "-v"])

