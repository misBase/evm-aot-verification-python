#!/usr/bin/env python3
"""Test EVM IR JSON parsing."""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from evm_ir.json_parser import load_ir_from_json
from evm_ir.semantics import EVMIRSemantics
from common.uint256 import Uint256
from z3 import BitVecVal, simplify


def test_json_parsing():
    """Test parsing EVM IR from JSON."""
    print("Testing EVM IR JSON parsing...")
    
    # Get the path to the example IR file
    test_dir = os.path.dirname(__file__)
    ir_file = os.path.join(test_dir, "example_ir.json")
    
    # Load IR from JSON
    ir_result = load_ir_from_json(ir_file)
    
    print(f"  Loaded {len(ir_result.blocks)} block(s)")
    
    for i, block in enumerate(ir_result.blocks):
        print(f"\n  Block {i}:")
        print(f"    PC: {block.pc}")
        print(f"    Stack depth: {block.stack_depth}")
        print(f"    Operations: {len(block.operations)}")
        for op in block.operations:
            print(f"      - {op.kind} (pc={op.pc})")
    
    # Test semantic modeling
    print("\n  Testing semantic modeling...")
    semantics = EVMIRSemantics()
    
    # Create symbolic inputs
    val1 = Uint256.symbolic("test_val1")
    val2 = Uint256.symbolic("test_val2")
    input_stack = [val1.to_bv256(), val2.to_bv256()]
    
    # Build semantics for the block
    result = semantics.build_block_semantics(ir_result.blocks[0], input_stack)
    
    print(f"    Output stack size: {result['output_count']}")
    print(f"    Semantic formula type: {type(result['semantic_formula'])}")
    
    # Test with concrete values
    print("\n  Testing with concrete values...")
    val1_concrete = Uint256.from_int(0x60)
    val2_concrete = Uint256.from_int(0x10)
    input_stack_concrete = [val1_concrete.to_bv256(), val2_concrete.to_bv256()]
    
    result_concrete = semantics.build_block_semantics(ir_result.blocks[0], input_stack_concrete)
    result_value = simplify(result_concrete['semantic_formula'])
    expected = BitVecVal(0x70, 256)
    
    print(f"    Result: {result_value}")
    print(f"    Expected: {expected}")
    assert simplify(result_value == expected), "Semantic result mismatch"
    
    print("\n✓ EVM IR JSON parsing test passed")

