#!/usr/bin/env python3
"""Basic tests for the refactored code structure."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics, EVMOperationSemantics
from x86_64.semantics import X86SemanticsModel
from x86_64.models import Register
from verification.refinement_checker import RefinementChecker
from z3 import BitVecVal, simplify

# x86-64 ADD operation hex sequence (from AOT compiler output)
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


def test_basic_imports():
    """Test that all modules can be imported."""
    print("✓ All modules imported successfully")


def test_add_semantics():
    """Test ADD semantics."""
    print("\nTesting ADD semantics...")
    
    # Test EVM ADD semantics
    evm_op = EVMOperationSemantics()
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    result = evm_op.add_semantics(val1.to_bv256(), val2.to_bv256())
    expected = BitVecVal(0x70, 256)
    
    print(f"  EVM ADD: 0x60 + 0x10 = {simplify(result)}")
    print(f"  Expected: {expected}")
    assert simplify(result == expected), "EVM ADD result mismatch"
    
    # Test x86 ADD semantics
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
    print(f"  x86 ADD: {simplify(x86_result)}")
    assert simplify(x86_result == expected), "x86 ADD result mismatch"
    
    print("✓ ADD semantics test passed")


def test_refinement_checker():
    """Test refinement checker with concrete values."""
    print("\nTesting refinement checker...")
    
    checker = RefinementChecker(timeout_ms=5000, verbose=False)
    
    # Test with equivalent values
    evm_result = BitVecVal(0x70, 256)
    x86_result = BitVecVal(0x70, 256)
    
    verified, msg = checker.check_refinement(evm_result, x86_result)
    print(f"  Equivalent values: {verified}")
    assert verified, "Equivalent values should verify"
    
    # Test with different values
    evm_result2 = BitVecVal(0x70, 256)
    x86_result2 = BitVecVal(0x71, 256)
    
    verified2, msg2 = checker.check_refinement(evm_result2, x86_result2)
    print(f"  Different values: {verified2}")
    assert not verified2, "Different values should not verify"
    
    print("✓ Refinement checker test passed")


def main():
    """Run all tests."""
    print("=" * 70)
    print("Testing Refactored Code Structure")
    print("=" * 70)
    
    try:
        test_basic_imports()
        test_add_semantics()
        test_refinement_checker()
        
        print("\n" + "=" * 70)
        print("All tests passed! ✓")
        print("=" * 70)
        return True
    except Exception as e:
        print(f"\n✗ Test failed with error: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)

