"""
EVM IR semantic modeling.

This module provides semantic modeling for EVM IR operations using Z3.
"""

from z3 import BitVec, BitVecRef, BitVecVal, Concat, Extract, If, UGE, ULT, And, Or
from typing import List, Optional, Dict, Any, Tuple
from .models import EVMBlock, EvmOperator
from common.uint256 import Uint256
from state.smt_state import SMTState, EVMStackState, EVMMemoryState

# Constants for RETURN instruction
MAX_RETURN_DATA_SIZE = 256  # Maximum return data size in bytes (256 bytes = 2048 bits)


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

def evm_operator_to_z3(op: EvmOperator, state: SMTState) -> SMTState:
    """Convert EVM operator to Z3 formula, updating state.
    
    This is the Alive2-style direct formula construction method.
    Each operator directly builds Z3 expressions without execution simulation.
    
    Args:
        op: EVM operator to convert
        state: Current SMT state (will be modified)
        
    Returns:
        Updated SMT state
    """
    kind = op.kind.upper()
    op_semantics = EVMOperationSemantics()
    
    if kind == "TAG":
        # TAG is a no-op for semantics (just marks block entry)
        return state
    
    elif kind == "BLOCKEND":
        # BLOCKEND is a no-op for semantics (just marks block end)
        return state
    
    elif kind == "ADD":
        # ADD: pop two values, add them, push result
        # Using Z3 Array: value_b = Select(Stack, SP-1), value_a = Select(Stack, SP-2)
        # result = value_a + value_b
        # Stack' = Store(Stack, SP-2, result), SP' = SP - 1
        
        # Pop two values from stack
        b, stack_after_pop1 = state.evm_stack.pop()
        a, stack_after_pop2 = stack_after_pop1.pop()
        
        # Compute addition
        result = op_semantics.add_semantics(a, b)
        
        # Push result
        new_stack_state = stack_after_pop2.push(result)
        state.evm_stack = new_stack_state
        return state
    
    elif kind.startswith("PUSH"):
        # PUSH: push immediate value onto stack
        # Using Z3 Array: SP' = SP + 1, Stack' = Store(Stack, SP, value)
        if op.immediate is None:
            raise ValueError(f"PUSH operation missing immediate at pc={op.pc}")
        
        value = op_semantics.push_semantics(op.immediate, op.param or 1)
        new_stack_state = state.evm_stack.push(value)
        state.evm_stack = new_stack_state
        return state
    
    elif kind == "MLOAD":
        # MLOAD: load 32 bytes from memory, push onto stack
        # Using Z3 Array: offset = Select(Stack, SP-1)
        # value = load_256bit(Memory, offset), Stack' = Store(Stack, SP-1, value)
        
        # Pop offset from stack
        offset_bv, stack_after_pop = state.evm_stack.pop()
        
        # Load 32 bytes (256 bits) from memory using Z3 Array
        mem_value, new_memory_state = state.evm_memory.load_256bit(offset_bv)
        
        # Push loaded value onto stack
        new_stack_state = stack_after_pop.push(mem_value)
        
        # Update state
        state.evm_stack = new_stack_state
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "MSTORE":
        # MSTORE: pop offset and value, store 32 bytes to memory
        # Using Z3 Array: value = Select(Stack, SP-1), offset = Select(Stack, SP-2)
        # Memory' = store_256bit(Memory, offset, value), SP' = SP - 2
        
        # Pop value and offset
        value, stack_after_pop1 = state.evm_stack.pop()
        offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        
        # Store 32 bytes (256 bits) to memory using Z3 Array
        new_memory_state = state.evm_memory.store_256bit(offset_bv, value)
        
        # Update state
        state.evm_stack = stack_after_pop2
        state.evm_memory = new_memory_state
        return state
    
    elif kind == "RETURN":
        # RETURN: pop offset and length, return memory[offset:offset+length]
        # Pop length and offset from stack
        length_bv, stack_after_pop1 = state.evm_stack.pop()
        offset_bv, stack_after_pop2 = stack_after_pop1.pop()
        
        # Truncate length to 64-bit for storage
        from z3 import Extract as Z3Extract
        if length_bv.size() == 256:
            return_length_64 = Z3Extract(63, 0, length_bv)
        elif length_bv.size() == 64:
            return_length_64 = length_bv
        else:
            raise ValueError(f"Unexpected length size: {length_bv.size()}")
        
        if offset_bv.size() == 256:
            return_offset_64 = Z3Extract(63, 0, offset_bv)
        elif offset_bv.size() == 64:
            return_offset_64 = offset_bv
        else:
            raise ValueError(f"Unexpected offset size: {offset_bv.size()}")
        
        # Store return offset and length in state
        # We don't extract the data - we'll compare memory directly in RefinementChecker
        # Note: RETURN only reads memory, it doesn't modify memory or MSize
        state.return_offset = return_offset_64
        state.return_length = return_length_64
        
        # Update stack (both values were popped)
        state.evm_stack = stack_after_pop2
        
        return state
    
    elif kind in ["JUMP", "JUMPI", "STOP", "REVERT"]:
        # Control flow operations - return state as-is
        # These will be handled at the control flow level
        return state
    
    else:
        # Unknown operation - return state unchanged
        # TODO: Implement more operations
        return state


def execute_block_with_tag(block: EVMBlock, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
    """Execute a block with TAG-based path splitting (Level 1: block-level merging).
    
    TAG instruction creates 3 paths:
    - Path 1: SP < min_depth -> error path (returns error status code)
    - Path 2: SP > max_depth -> error path (returns error status code)
    - Path 3: min_depth <= SP <= max_depth -> normal execution path
    
    These 3 paths are merged using Z3 If expressions.
    
    Args:
        block: EVM block to execute
        state: Initial SMT state
        
    Returns:
        Tuple of (merged_state, result_dict) where:
        - merged_state: State with merged results from all 3 paths
        - result_dict: Dictionary with merged return values (offset, length, memory, has_return)
    """
    from z3 import IntVal
    
    # Get stack pointer as Int (SP is Int type in EVMStackState)
    sp = state.evm_stack.SP
    
    # Convert min_depth and max_depth to Int for comparison
    min_depth_int = IntVal(block.min_depth)
    max_depth_int = IntVal(block.max_depth)
    
    # Build path conditions
    # Path 1: SP < min_depth -> error
    path1_condition = sp < min_depth_int
    
    # Path 2: SP > max_depth -> error
    path2_condition = sp > max_depth_int
    
    # Path 3: min_depth <= SP <= max_depth -> normal
    path3_condition = And(sp >= min_depth_int, sp <= max_depth_int)
    
    # Execute Path 1: SP < min_depth -> error path
    # Error paths return error status code (no return data)
    from z3 import BitVecVal
    path1_state = state.copy()
    path1_state.return_offset = BitVecVal(0, 64)
    path1_state.return_length = BitVecVal(0, 64)
    # Note: In actual implementation, we might set a specific error status code
    # For now, we use 0 to indicate no return (error)
    
    # Execute Path 2: SP > max_depth -> error path
    path2_state = state.copy()
    path2_state.return_offset = BitVecVal(0, 64)
    path2_state.return_length = BitVecVal(0, 64)
    
    # Execute Path 3: min_depth <= SP <= max_depth -> normal execution
    path3_state = state.copy()
    
    # Execute all operations in the block (skip TAG and BLOCKEND)
    for op in block.operations:
        kind = op.kind.upper()
        if kind == "TAG":
            # TAG is handled at block level, skip here
            continue
        elif kind == "BLOCKEND":
            # BLOCKEND is a marker, skip
            continue
        else:
            # Execute the operation
            path3_state = op.to_z3(path3_state)
    
    # Merge the 3 paths using If expressions
    # Structure: If(path1_cond, path1_result, If(path2_cond, path2_result, path3_result))
    merged_state = state.copy()
    
    # Merge return_offset
    merged_state.return_offset = If(
        path1_condition,
        path1_state.return_offset,
        If(
            path2_condition,
            path2_state.return_offset,
            path3_state.return_offset
        )
    )
    
    # Merge return_length
    merged_state.return_length = If(
        path1_condition,
        path1_state.return_length,
        If(
            path2_condition,
            path2_state.return_length,
            path3_state.return_length
        )
    )
    
    # Merge memory (EVM memory Array)
    # Note: Memory merging is more complex, we need to merge the entire Array
    # For now, we use path3's memory (normal path) since error paths don't modify memory
    # In a more sophisticated implementation, we might need to merge Arrays element-wise
    merged_state.evm_memory = path3_state.evm_memory
    
    # Merge stack
    # Similar to memory, we use path3's stack for normal execution
    # Error paths don't modify stack meaningfully
    merged_state.evm_stack = path3_state.evm_stack
    
    # Build result dictionary
    from z3 import Ne
    has_return = Ne(merged_state.return_length, BitVecVal(0, 64))
    
    result = {
        'offset': merged_state.return_offset,
        'length': merged_state.return_length,
        'memory': merged_state.evm_memory.Memory,
        'base_addr': None,  # EVM memory uses direct offset
        'has_return': has_return
    }
    
    return merged_state, result

