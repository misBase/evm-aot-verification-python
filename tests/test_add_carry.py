#!/usr/bin/env python3
"""Test ADD operation with carry propagation."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from common.uint256 import Uint256
from evm_ir.semantics import EVMOperationSemantics
from x86_64.semantics import X86SemanticsModel
from x86_64.models import Register
from verification.refinement_checker import RefinementChecker
from z3 import BitVecVal, simplify

# x86-64 ADD operation hex sequence (from AOT compiler output)
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


def test_add_with_carry():
    """Test ADD with values that cause carry propagation."""
    print("Testing ADD with carry propagation...")
    
    evm_op = EVMOperationSemantics()
    x86_model = X86SemanticsModel()
    checker = RefinementChecker(timeout_ms=10000, verbose=False)
    
    # Test case 1: Max uint64 + 1 (should cause carry)
    print("\n  Test 1: 0xFFFFFFFFFFFFFFFF + 0x01")
    val1 = Uint256.from_int(0xFFFFFFFFFFFFFFFF)
    val2 = Uint256.from_int(0x01)
    
    # EVM ADD
    evm_result = evm_op.add_semantics(val1.to_bv256(), val2.to_bv256())
    evm_result_uint = Uint256.from_bv256(evm_result)
    
    # x86 ADD
    x86_result = x86_model.build_sequence_from_limbs(
        X86_ADD_HEX_SEQUENCE,
        [val1.z0, val1.z1, val1.z2, val1.z3],
        [val2.z0, val2.z1, val2.z2, val2.z3],
        base_addr=X86_ADD_BASE_ADDR,
        result_registers=[Register.RBX, Register.RDX, Register.RCX, Register.RAX]
    )
    
    # Check equivalence
    verified, msg = checker.check_refinement(evm_result, x86_result)
    print(f"    EVM result (z0): {simplify(evm_result_uint.z0)}")
    print(f"    EVM result (z1): {simplify(evm_result_uint.z1)}")
    print(f"    Verified: {verified}")
    assert verified, "ADD with carry should verify"
    
    # Test case 2: Large values with multiple carries
    print("\n  Test 2: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF + 0x01")
    val3 = Uint256.from_int(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
    val4 = Uint256.from_int(0x01)
    
    evm_result2 = evm_op.add_semantics(val3.to_bv256(), val4.to_bv256())
    x86_result2 = x86_model.build_sequence_from_limbs(
        X86_ADD_HEX_SEQUENCE,
        [val3.z0, val3.z1, val3.z2, val3.z3],
        [val4.z0, val4.z1, val4.z2, val4.z3],
        base_addr=X86_ADD_BASE_ADDR,
        result_registers=[Register.RBX, Register.RDX, Register.RCX, Register.RAX]
    )
    
    verified2, msg2 = checker.check_refinement(evm_result2, x86_result2)
    print(f"    Verified: {verified2}")
    assert verified2, "ADD with multiple carries should verify"
    
    print("\n✓ ADD with carry propagation test passed")

