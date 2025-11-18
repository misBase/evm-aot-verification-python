#!/usr/bin/env python3
"""
Test translation verification using program-level logical semantics.

This module contains tests that verify the refinement relation between 
EVM bytecode and AOT-compiled x86-64 machine code. These tests focus on
verification logic, including symbolic proofs and concrete value tests.
"""

from __future__ import annotations

import os
import pytest
from z3 import BitVecVal
from common.uint256 import Uint256
from evm_ir.semantics import EVMIRSemantics
from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from verification.refinement_checker import RefinementChecker
from verification.program_verifier import ProgramEquivalenceChecker


# x86-64 machine code sequences for EVM operations
# These are extracted from the AOT compiler output

# ADD operation sequence (addresses 0x6c-0x9b)
# Includes: 8 compute instructions + 4 store instructions
# Instructions:
#   mov rax, [r14-0x40]   ; Load val1.z0
#   add rax, [r14-0x20]   ; Add val2.z0, set carry
#   mov rcx, [r14-0x38]   ; Load val1.z1
#   adc rcx, [r14-0x18]   ; Add val2.z1 + carry
#   mov rdx, [r14-0x30]   ; Load val1.z2
#   adc rdx, [r14-0x10]   ; Add val2.z2 + carry
#   mov rbx, [r14-0x28]   ; Load val1.z3
#   adc rbx, [r14-0x08]   ; Add val2.z3 + carry
#   mov [r14-0x40], rax   ; Store result.z0
#   mov [r14-0x38], rcx   ; Store result.z1
#   mov [r14-0x30], rdx   ; Store result.z2
#   mov [r14-0x28], rbx   ; Store result.z3
X86_ADD_HEX_SEQUENCE = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
X86_ADD_BASE_ADDR = 0x6c


# ===========================
# Pytest Fixtures
# ===========================

@pytest.fixture
def evm_semantics() -> EVMIRSemantics:
    """Fixture providing EVM IR semantics instance."""
    return EVMIRSemantics()


@pytest.fixture
def x86_add_program() -> X86Program:
    """Fixture providing x86-64 ADD program."""
    return X86Program.from_hex(X86_ADD_HEX_SEQUENCE, base_addr=X86_ADD_BASE_ADDR)


@pytest.fixture
def refinement_checker() -> RefinementChecker:
    """Fixture providing refinement checker with default timeout."""
    return RefinementChecker(timeout_ms=10000, verbose=False)


@pytest.fixture
def refinement_checker_verbose() -> RefinementChecker:
    """Fixture providing refinement checker with verbose output for symbolic tests."""
    return RefinementChecker(timeout_ms=60000, verbose=True)


# ===========================
# Test Functions
# ===========================

def test_verifier_import():
    """Test that verifier modules can be imported."""
    # If import fails, an exception will be raised automatically
    pass


def test_verify_add_symbolic(
    evm_semantics: EVMIRSemantics,
    x86_add_program: X86Program,
    refinement_checker_verbose: RefinementChecker
):
    """Test symbolic ADD verification - proves correctness for all inputs.
    
    This is a formal proof that the x86 ADD implementation is semantically
    equivalent to the EVM ADD operation for all possible 256-bit inputs.
    
    This test proves: ∀ a, b ∈ Uint256. x86_ADD_Program(a, b) ≡ EVM_ADD_Program(a, b)
    """
    # Create symbolic inputs
    evm_val1 = Uint256.symbolic("evm_val1")
    evm_val2 = Uint256.symbolic("evm_val2")
    
    # Build EVM ADD semantic formula
    evm_a_bv = evm_val1.to_bv256()
    evm_b_bv = evm_val2.to_bv256()
    evm_result = evm_semantics.op_semantics.add_semantics(evm_a_bv, evm_b_bv)
    
    # Build x86 program semantics using the same symbolic values
    x86_result_dict = x86_add_program.build_program_semantics_from_limbs(
        [evm_val1.z0, evm_val1.z1, evm_val1.z2, evm_val1.z3],
        [evm_val2.z0, evm_val2.z1, evm_val2.z2, evm_val2.z3]
    )
    x86_result = x86_result_dict['semantic_formula']
    
    # Check refinement relation (proves equivalence for all inputs)
    verified, msg = refinement_checker_verbose.check_refinement(evm_result, x86_result)
    
    assert verified, (
        f"Symbolic ADD verification failed. "
        f"This should prove equivalence for all 256-bit inputs. Error: {msg}"
    )


def test_verify_add_program_pair():
    """Test program-level verification using JSON IR and x86 hex sequence.
    
    This test verifies the equivalence between an EVM program loaded from JSON
    and an x86-64 program created from hex sequence, similar to the main.py
    verification workflow.
    
    This test uses:
    - add_ir.json: EVM IR JSON file containing ADD operation
    - X86_ADD_HEX_SEQUENCE: x86-64 machine code for ADD operation
    - ProgramEquivalenceChecker: Program-level verifier
    """
    # Get the test data directory path
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "data", "add_ir.json")
    
    # Load EVM program from JSON
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    # Create x86 program from hex sequence
    x86_program = X86Program.from_hex(X86_ADD_HEX_SEQUENCE, base_addr=X86_ADD_BASE_ADDR)
    
    # Verify program pair using ProgramEquivalenceChecker
    checker = ProgramEquivalenceChecker(timeout_ms=60000, verbose=False)
    verified, msg = checker.verify_program_pair(evm_program, x86_program)
    
    assert verified, (
        f"Program pair verification failed. "
        f"EVM program from {ir_path} and x86 program should be equivalent. Error: {msg}"
    )
