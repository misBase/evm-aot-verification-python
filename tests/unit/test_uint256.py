#!/usr/bin/env python3
"""直接测试Uint256.add_semantics()方法（类似于Go的y.Add(&x, y)）。"""

from common.uint256 import Uint256
from z3 import BitVecVal, simplify


def test_uint256_add_direct():
    """直接测试Uint256.add_semantics()方法，类似于Go的y.Add(&x, y)。"""
    # 测试用例1：简单加法
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    # 直接调用add_semantics（类似于Go的y.Add(&x, y)）
    result = val1.add_semantics(val2)
    
    expected = Uint256.from_int(0x70)
    assert simplify(result.z0 == expected.z0), \
        f"z0 mismatch: expected {simplify(expected.z0)}, got {simplify(result.z0)}"
    assert simplify(result.z1 == expected.z1), \
        f"z1 mismatch: expected {simplify(expected.z1)}, got {simplify(result.z1)}"
    assert simplify(result.z2 == expected.z2), \
        f"z2 mismatch: expected {simplify(expected.z2)}, got {simplify(result.z2)}"
    assert simplify(result.z3 == expected.z3), \
        f"z3 mismatch: expected {simplify(expected.z3)}, got {simplify(result.z3)}"
    
    # 测试用例2：带进位的加法
    val3 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
    val4 = Uint256.from_int(0x01)
    
    result2 = val3.add_semantics(val4)
    
    # 应该有z0=0, z1=1（进位传播）
    assert simplify(result2.z0 == 0), \
        f"z0 should be 0 after carry, got {simplify(result2.z0)}"
    assert simplify(result2.z1 == 1), \
        f"z1 should be 1 after carry, got {simplify(result2.z1)}"
    
    # 测试用例3：符号加法
    val5 = Uint256.symbolic("a")
    val6 = Uint256.symbolic("b")
    
    result3 = val5.add_semantics(val6)
    
    assert hasattr(result3, 'z0') and hasattr(result3, 'z1'), \
        "Result should have correct structure (z0, z1, z2, z3 attributes)"
    assert hasattr(result3, 'z2') and hasattr(result3, 'z3'), \
        "Result should have correct structure (z2, z3 attributes)"

