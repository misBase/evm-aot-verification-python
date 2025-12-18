"""
Memory mapping between EVM stack and x86-64 memory.

This module provides mapping functions to convert between EVM stack representation
and x86-64 memory layout for verification purposes.
"""

from typing import List, Dict
from z3 import BitVec, Concat, Extract
from common.uint256 import Uint256
from state.smt_state import SMTState, EVMStackState, X86MemoryState


class StackMemoryMapper:
    """Maps between EVM stack and x86-64 memory layout.
    
    The AOT compiler maps EVM stack elements to x86 memory offsets:
    - stack[0] → [R14-0x40..R14-0x28] (4×64-bit limbs)
    - stack[1] → [R14-0x20..R14-0x08] (4×64-bit limbs)
    - stack[2] → [R14+0x00..R14+0x18] (if needed)
    - etc.
    """
    
    # Base offsets for stack elements in x86 memory
    # Each stack element occupies 32 bytes (4×64-bit limbs)
    STACK_ELEMENT_SIZE = 32  # bytes
    STACK_BASE_OFFSET = -0x40  # First stack element starts at R14-0x40
    
    @staticmethod
    def stack_index_to_base_offset(stack_index: int) -> int:
        """Convert stack index to x86 memory base offset.
        
        Args:
            stack_index: EVM stack index (0 = top of stack)
            
        Returns:
            Base offset relative to R14 for the stack element
        """
        # Stack elements are stored with decreasing offsets (more negative = higher in stack)
        # stack[0] at -0x40, stack[1] at -0x20, etc.
        # Each stack element is 32 bytes (0x20), spacing is 0x20 bytes
        # stack[0]: -0x40, stack[1]: -0x40 + 0x20 = -0x20
        return StackMemoryMapper.STACK_BASE_OFFSET + (stack_index * 0x20)
    
    @staticmethod
    def stack_to_memory_layout(stack_value: BitVec, stack_index: int) -> Dict[int, BitVec]:
        """Convert EVM stack value to x86 memory layout.
        
        Args:
            stack_value: 256-bit BitVec representing stack element
            stack_index: Stack index (0 = top of stack)
            
        Returns:
            Dictionary mapping memory offsets to 64-bit limbs
            {base_offset: z0, base_offset+8: z1, base_offset+16: z2, base_offset+24: z3}
            
        Note: x86 memory is now byte-addressable (Array[BitVec[64], BitVec[8]]),
        but this function returns 64-bit limbs for convenience. The limbs will
        be stored as 8 bytes each in little-endian order.
        """
        if stack_value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {stack_value.size()}")
        
        # Get base offset for this stack element
        base_offset = StackMemoryMapper.stack_index_to_base_offset(stack_index)
        
        # Extract 4 limbs from 256-bit value
        z0 = Extract(63, 0, stack_value)    # LSB
        z1 = Extract(127, 64, stack_value)
        z2 = Extract(191, 128, stack_value)
        z3 = Extract(255, 192, stack_value)  # MSB
        
        # Map to x86 memory offsets
        return {
            base_offset: z0,
            base_offset + 8: z1,
            base_offset + 16: z2,
            base_offset + 24: z3,
        }
    
    @staticmethod
    def memory_to_stack_value(memory: X86MemoryState, stack_index: int) -> BitVec:
        """Extract EVM stack value from x86 memory layout.
        
        Args:
            memory: X86MemoryState containing memory values
            stack_index: Stack index (0 = top of stack)
            
        Returns:
            256-bit BitVec representing the stack element
        """
        # Get base offset for this stack element
        base_offset = StackMemoryMapper.stack_index_to_base_offset(stack_index)
        
        # Load 4 limbs from memory
        z0 = memory.load_limb(base_offset)
        z1 = memory.load_limb(base_offset + 8)
        z2 = memory.load_limb(base_offset + 16)
        z3 = memory.load_limb(base_offset + 24)
        
        # Concatenate to form 256-bit value: [z3|z2|z1|z0]
        return Concat(z3, z2, z1, z0)
    
    @staticmethod
    def initialize_x86_memory_from_stack(
        x86_memory: X86MemoryState,
        stack_values: List[BitVec]
    ) -> X86MemoryState:
        """Initialize x86 memory from EVM stack values.
        
        Args:
            x86_memory: X86MemoryState to initialize
            stack_values: List of 256-bit BitVec stack values
            
        Returns:
            New X86MemoryState with initialized memory
        """
        new_memory = x86_memory
        for stack_index, stack_value in enumerate(stack_values):
            layout = StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)
            for offset, limb in layout.items():
                new_memory = new_memory.store_limb(offset, limb)
        return new_memory
    
    @staticmethod
    def extract_stack_from_x86_memory(
        x86_memory: X86MemoryState,
        num_elements: int
    ) -> List[BitVec]:
        """Extract EVM stack values from x86 memory.
        
        Args:
            x86_memory: X86MemoryState containing memory values
            num_elements: Number of stack elements to extract
            
        Returns:
            List of 256-bit BitVec stack values
        """
        stack_values = []
        for stack_index in range(num_elements):
            stack_value = StackMemoryMapper.memory_to_stack_value(x86_memory, stack_index)
            stack_values.append(stack_value)
        return stack_values


def stack_to_memory_layout(stack_value: BitVec, stack_index: int) -> Dict[int, BitVec]:
    """Convenience function: Convert stack value to memory layout.
    
    Args:
        stack_value: 256-bit BitVec
        stack_index: Stack index
        
    Returns:
        Dictionary mapping offsets to limbs
    """
    return StackMemoryMapper.stack_to_memory_layout(stack_value, stack_index)


def memory_to_stack_value(memory: X86MemoryState, stack_index: int) -> BitVec:
    """Convenience function: Extract stack value from memory.
    
    Args:
        memory: X86MemoryState
        stack_index: Stack index
        
    Returns:
        256-bit BitVec
    """
    return StackMemoryMapper.memory_to_stack_value(memory, stack_index)

