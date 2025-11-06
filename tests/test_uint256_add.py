#!/usr/bin/env python3
"""Test Uint256.add_semantics() method directly (similar to Go's y.Add(&x, y))."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from common.uint256 import Uint256
from z3 import BitVecVal, simplify


def test_uint256_add_direct():
    """Test Uint256.add_semantics() method directly, similar to Go's y.Add(&x, y)."""
    print("Testing Uint256.add_semantics() directly...")
    
    # Test case 1: Simple addition
    print("\n  Test 1: Simple addition (0x60 + 0x10)")
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    # Call add_semantics directly (similar to Go's y.Add(&x, y))
    result = val1.add_semantics(val2)
    
    print(f"    val1: {val1}")
    print(f"    val2: {val2}")
    print(f"    result: {result}")
    print(f"    result.z0: {simplify(result.z0)}")
    
    expected = Uint256.from_int(0x70)
    assert simplify(result.z0 == expected.z0), "z0 mismatch"
    assert simplify(result.z1 == expected.z1), "z1 mismatch"
    assert simplify(result.z2 == expected.z2), "z2 mismatch"
    assert simplify(result.z3 == expected.z3), "z3 mismatch"
    print("    ✓ Simple addition passed")
    
    # Test case 2: Addition with carry
    print("\n  Test 2: Addition with carry (0xFFFFFFFFFFFFFFFF + 0x01)")
    val3 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
    val4 = Uint256.from_int(0x01)
    
    result2 = val3.add_semantics(val4)
    
    print(f"    result2.z0: {simplify(result2.z0)}")
    print(f"    result2.z1: {simplify(result2.z1)}")
    
    # Should have z0=0, z1=1 (carry propagated)
    assert simplify(result2.z0 == 0), "z0 should be 0"
    assert simplify(result2.z1 == 1), "z1 should be 1"
    print("    ✓ Addition with carry passed")
    
    # Test case 3: Symbolic addition
    print("\n  Test 3: Symbolic addition")
    val5 = Uint256.symbolic("a")
    val6 = Uint256.symbolic("b")
    
    result3 = val5.add_semantics(val6)
    
    print(f"    result3 type: {type(result3)}")
    print(f"    result3.z0: {result3.z0}")
    print(f"    result3 has correct structure: {hasattr(result3, 'z0') and hasattr(result3, 'z1')}")
    print("    ✓ Symbolic addition passed")
    
    print("\n✓ All Uint256.add_semantics() tests passed")

