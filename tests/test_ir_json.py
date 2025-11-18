#!/usr/bin/env python3
"""Test EVM IR JSON parsing."""

import os

from evm_ir.json_parser import load_ir_from_json
from evm_ir.semantics import EVMIRSemantics
from common.uint256 import Uint256
from z3 import BitVecVal, simplify


def test_json_parsing():
    """Test parsing EVM IR from JSON and semantic modeling."""
    # Get the path to the example IR file
    test_dir = os.path.dirname(__file__)
    ir_file = os.path.join(test_dir, "data", "example_ir.json")
    
    # Load IR from JSON
    ir_result = load_ir_from_json(ir_file)
    
    assert len(ir_result.blocks) > 0, "IR should contain at least one block"
    
    # Verify block structure
    block = ir_result.blocks[0]
    assert hasattr(block, 'pc'), "Block should have PC attribute"
    assert hasattr(block, 'stack_depth'), "Block should have stack_depth attribute"
    assert hasattr(block, 'operations'), "Block should have operations attribute"
    assert len(block.operations) > 0, "Block should have at least one operation"
    
    # Test semantic modeling with symbolic inputs
    semantics = EVMIRSemantics()
    val1 = Uint256.symbolic("test_val1")
    val2 = Uint256.symbolic("test_val2")
    input_stack = [val1.to_bv256(), val2.to_bv256()]
    
    result = semantics.build_block_semantics(block, input_stack)
    
    assert 'output_count' in result, "Result should contain output_count"
    assert 'semantic_formula' in result, "Result should contain semantic_formula"
    
    # Test with concrete values
    val1_concrete = Uint256.from_int(0x60)
    val2_concrete = Uint256.from_int(0x10)
    input_stack_concrete = [val1_concrete.to_bv256(), val2_concrete.to_bv256()]
    
    result_concrete = semantics.build_block_semantics(block, input_stack_concrete)
    result_value = simplify(result_concrete['semantic_formula'])
    expected = BitVecVal(0x70, 256)
    
    assert simplify(result_value == expected), \
        f"Semantic result mismatch: expected {expected}, got {result_value}"

