#!/usr/bin/env python3
"""Test EVM IR JSON parsing."""

import os

from evm_ir.json_parser import load_ir_from_json


def test_json_parsing():
    """Test parsing EVM IR from JSON file."""
    # Get the path to the example IR file
    test_dir = os.path.dirname(__file__)
    ir_file = os.path.join(test_dir, "data", "example_ir.json")
    
    # Load IR from JSON
    ir_result = load_ir_from_json(ir_file)
    
    # Verify parsing result structure
    assert ir_result is not None, "IR result should not be None"
    assert len(ir_result.blocks) > 0, "IR should contain at least one block"
    
    # Verify block structure
    block = ir_result.blocks[0]
    assert hasattr(block, 'pc'), "Block should have PC attribute"
    assert hasattr(block, 'stack_depth'), "Block should have stack_depth attribute"
    assert hasattr(block, 'operations'), "Block should have operations attribute"
    assert len(block.operations) > 0, "Block should have at least one operation"
    
    # Verify operation structure
    for op in block.operations:
        assert hasattr(op, 'kind'), "Operation should have kind attribute"
        assert hasattr(op, 'pc'), "Operation should have pc attribute"
    
    # Verify specific operations from example_ir.json
    operation_kinds = [op.kind.upper() for op in block.operations]
    assert 'TAG' in operation_kinds, "Should contain TAG operation"
    assert 'PUSH' in operation_kinds, "Should contain PUSH operation"
    assert 'ADD' in operation_kinds, "Should contain ADD operation"
    assert 'STOP' in operation_kinds, "Should contain STOP operation"
    
    # Verify PUSH operations have immediate values
    push_ops = [op for op in block.operations if op.kind.upper().startswith('PUSH')]
    for push_op in push_ops:
        assert push_op.immediate is not None, f"PUSH operation at pc={push_op.pc} should have immediate value"

