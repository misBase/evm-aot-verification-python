"""
EVM IR semantic modeling.

This module provides semantic modeling for EVM IR operations using Z3.
"""

from z3 import BitVec, BitVecRef, BitVecVal, Concat, Extract
from typing import List, Optional, Dict, Any
from .models import EVMBlock, EvmOperator
from common.uint256 import Uint256


class EVMOperationSemantics:
    """Semantic modeling for individual EVM operations."""
    
    def add_semantics(self, a: BitVec, b: BitVec) -> BitVec:
        """Build logical formula for EVM ADD operation.
        
        EVM ADD semantics:
          - Input: two 256-bit values a and b (represented as 4x64-bit limbs)
          - Output: (a + b) mod 2^256
          - Implementation: Delegates to Uint256.add_semantics() method
          
        This follows the same pattern as the Go implementation where
        opAdd calls y.Add(&x, y) on uint256 types.
          
        Args:
            a: First 256-bit operand (Z3 BitVec of size 256, or Uint256)
            b: Second 256-bit operand (Z3 BitVec of size 256, or Uint256)
            
        Returns:
            Logical formula representing (a + b) mod 2^256 as a 256-bit BitVec
        """
        # Convert inputs to Uint256 if they are BitVecs
        # Check if it's a BitVecRef (Z3's BitVec type)
        if isinstance(a, BitVecRef) and a.size() == 256:
            a_uint = Uint256.from_bv256(a)
        elif isinstance(a, Uint256):
            a_uint = a
        elif hasattr(a, 'to_bv256'):
            a_uint = Uint256.from_bv256(a.to_bv256())
        else:
            raise ValueError(f"Unsupported type for operand a: {type(a)}")
        
        if isinstance(b, BitVecRef) and b.size() == 256:
            b_uint = Uint256.from_bv256(b)
        elif isinstance(b, Uint256):
            b_uint = b
        elif hasattr(b, 'to_bv256'):
            b_uint = Uint256.from_bv256(b.to_bv256())
        else:
            raise ValueError(f"Unsupported type for operand b: {type(b)}")
        
        # Call Uint256.add_semantics() method (similar to Go's y.Add(&x, y))
        result_uint = a_uint.add_semantics(b_uint)
        
        # Convert result back to 256-bit BitVec
        return result_uint.to_bv256()
    
    def push_semantics(self, immediate: int, param: int = 1) -> BitVec:
        """Build logical formula for EVM PUSH operation.
        
        Args:
            immediate: Immediate value to push
            param: Number of bytes (1-32 for PUSH1-PUSH32)
            
        Returns:
            Logical formula representing the pushed value as a 256-bit BitVec
        """
        # PUSH operations push immediate values onto the stack
        # The immediate is right-padded to 256 bits
        return BitVecVal(immediate, 256)
    
    def operation_semantics(self, op: EvmOperator, inputs: List[BitVec]) -> BitVec:
        """Get semantic formula for an operation.
        
        Args:
            op: EVM operation
            inputs: List of input values (256-bit BitVecs)
            
        Returns:
            Output value as 256-bit BitVec
        """
        kind = op.kind.upper()
        
        if kind == "ADD":
            if len(inputs) < 2:
                raise ValueError("ADD requires 2 inputs")
            return self.add_semantics(inputs[0], inputs[1])
        
        elif kind.startswith("PUSH"):
            if op.immediate is None:
                raise ValueError("PUSH operation requires immediate value")
            return self.push_semantics(op.immediate, op.param or 1)
        
        else:
            raise NotImplementedError(f"Operation {kind} not yet implemented")


class EVMIRSemantics:
    """Semantic modeling for EVM IR blocks."""
    
    def __init__(self):
        """Initialize the EVM IR semantics model."""
        self.op_semantics = EVMOperationSemantics()
    
    def build_block_semantics(self, block: EVMBlock, input_stack: List[BitVec]) -> Dict[str, Any]:
        """Build semantic formula for an EVM block.
        
        Args:
            block: EVM block to model
            input_stack: Initial stack state (list of 256-bit BitVecs)
            
        Returns:
            Dictionary containing:
            - output_stack: Final stack state
            - semantic_formula: Overall semantic formula for the block
        """
        # Start with input stack
        stack = list(input_stack)
        
        # Process each operation in the block
        for op in block.operations:
            kind = op.kind.upper()
            
            if kind == "TAG":
                # TAG is a no-op for semantics (just marks block entry)
                continue
            
            elif kind == "BLOCKEND":
                # BLOCKEND is a no-op for semantics (just marks block end)
                continue
            
            elif kind == "ADD":
                if len(stack) < 2:
                    raise ValueError(f"Stack underflow in ADD operation at pc={op.pc}")
                b = stack.pop()
                a = stack.pop()
                result = self.op_semantics.add_semantics(a, b)
                stack.append(result)
            
            elif kind.startswith("PUSH"):
                if op.immediate is None:
                    raise ValueError(f"PUSH operation missing immediate at pc={op.pc}")
                value = self.op_semantics.push_semantics(op.immediate, op.param or 1)
                stack.append(value)
            
            elif kind in ["JUMP", "JUMPI", "STOP", "RETURN", "REVERT"]:
                # Control flow operations - for now, we stop processing
                # These will be handled at the control flow level
                break
            
            else:
                # For now, skip unknown operations
                # TODO: Implement more operations
                continue
        
        # Build overall semantic formula
        # For blocks with a single output, the result is the top of the stack
        if stack:
            semantic_formula = stack[-1]  # Top of stack
        else:
            # Empty stack result
            semantic_formula = BitVecVal(0, 256)
        
        return {
            'output_stack': stack,
            'semantic_formula': semantic_formula,
            'output_count': len(stack)
        }
    
    def build_add_block_semantics(self, block: EVMBlock) -> BitVec:
        """Build semantic formula for an ADD-only block (for testing).
        
        This is a convenience method for blocks that only perform ADD.
        
        Args:
            block: EVM block containing ADD operation
            
        Returns:
            Semantic formula for the ADD operation
        """
        # Create symbolic inputs
        val1 = Uint256.symbolic("block_val1")
        val2 = Uint256.symbolic("block_val2")
        
        input_stack = [val1.to_bv256(), val2.to_bv256()]
        
        result = self.build_block_semantics(block, input_stack)
        return result['semantic_formula']

