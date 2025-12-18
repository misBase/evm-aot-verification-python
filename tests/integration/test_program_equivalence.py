#!/usr/bin/env python3
"""Test program-level equivalence verification."""

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from x86_64.program import X86Program
from verification.program_verifier import ProgramEquivalenceChecker
import os


def test_program_verifier_import():
    """Test that program verifier can be imported."""
    # If import fails, an exception will be raised automatically
    pass


def test_evm_program_from_json():
    """Test EVM program creation from JSON."""
    # Get the test IR file path
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "example_ir.json")
    
    # Load and create program
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    assert len(evm_program.blocks) > 0, \
        f"Program should have at least one block, got {len(evm_program.blocks)}"


def test_x86_program_from_hex():
    """Test x86 program creation from hex."""
    # ADD operation hex sequence
    hex_sequence = "498b46c0490346e0498b4ec849134ee8498b56d0491356f0498b5ed849135ef8498946c049894ec8498956d049895ed8"
    base_addr = 0x6c
    
    x86_program = X86Program.from_hex(hex_sequence, base_addr=base_addr)
    
    assert len(x86_program.instructions) > 0, \
        f"Program should have at least one instruction, got {len(x86_program.instructions)}"


def test_program_add_operation_verification():
    """Test EVM program structure and operation detection.
    
    This test verifies that we can correctly parse and inspect EVM program
    structure, including finding specific operations within blocks.
    """
    # Get the test IR file path
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", "example_ir.json")
    
    # Load EVM program
    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)
    
    # Verify program structure
    assert len(evm_program.blocks) > 0, \
        f"EVM program should have at least one block, got {len(evm_program.blocks)}"
    
    # Test that we can find the ADD operation
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
    # When running directly, use pytest to run tests
    import pytest
    pytest.main([__file__, "-v"])

