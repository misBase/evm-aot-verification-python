#!/usr/bin/env python3
"""测试EVM和x86-64操作语义。"""

from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics, EVMOperationSemantics
from x86_64.semantics import X86SemanticsModel
from x86_64.models import Register
from verification.refinement_checker import RefinementChecker
from z3 import BitVecVal, simplify

# x86-64 ADD操作十六进制序列（来自AOT编译器输出）
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


def test_basic_imports():
    """测试所有模块是否可以导入。"""
    # 如果导入失败，将自动抛出异常
    pass


def test_add_semantics():
    """测试EVM和x86-64的ADD语义。"""
    # 测试EVM ADD语义
    evm_op = EVMOperationSemantics()
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    result = evm_op.add_semantics(val1.to_bv256(), val2.to_bv256())
    expected = BitVecVal(0x70, 256)
    
    assert simplify(result == expected), \
        f"EVM ADD failed: expected {expected}, got {simplify(result)}"
    
    # 测试x86 ADD语义
    x86_model = X86SemanticsModel()
    val1_limbs = [BitVecVal(0x60, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    val2_limbs = [BitVecVal(0x10, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    
    x86_result = x86_model.build_sequence_from_limbs(
        X86_ADD_HEX_SEQUENCE,
        val1_limbs, 
        val2_limbs,
        base_addr=X86_ADD_BASE_ADDR,
        result_registers=[Register.RBX, Register.RDX, Register.RCX, Register.RAX]
    )
    assert simplify(x86_result == expected), \
        f"x86 ADD failed: expected {expected}, got {simplify(x86_result)}"


def test_refinement_checker():
    """使用具体值测试精化检查器。"""
    checker = RefinementChecker(timeout_ms=5000, verbose=False)
    
    # 使用等价值测试
    evm_result = BitVecVal(0x70, 256)
    x86_result = BitVecVal(0x70, 256)
    
    verified, msg = checker.check_refinement(evm_result, x86_result)
    assert verified, f"Equivalent values should verify, but got: {msg}"
    
    # 使用不同值测试
    evm_result2 = BitVecVal(0x70, 256)
    x86_result2 = BitVecVal(0x71, 256)
    
    verified2, msg2 = checker.check_refinement(evm_result2, x86_result2)
    assert not verified2, \
        f"Different values should not verify (0x70 != 0x71), but verification passed: {msg2}"



