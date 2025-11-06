"""
x86-64 execution state management.

This module provides ExecutionState class to maintain register, memory, and flag state
during instruction sequence execution.
"""

from z3 import BitVec, BitVecVal
from typing import Dict, Optional
from .models import Register


class ExecutionState:
    """Maintains execution state for x86-64 instruction execution.
    
    Tracks:
    - Registers: 64-bit values for each register
    - Memory: Values at memory offsets (relative to R14 base register)
    - Flags: CPU flags (CF, ZF, SF, etc.) - 1-bit values
    """
    
    def __init__(self, initial_memory: Optional[Dict[int, BitVec]] = None):
        """Initialize execution state.
        
        Args:
            initial_memory: Initial memory state (dict mapping offsets to BitVec values)
        """
        # Initialize all registers to symbolic variables (will be set on first use)
        self.registers: Dict[Register, BitVec] = {}
        
        # Initialize memory from provided initial state
        self.memory: Dict[int, BitVec] = {}
        if initial_memory:
            self.memory.update(initial_memory)
        
        # Initialize flags (CF = carry flag, most important for ADD/ADC)
        self.flags: Dict[str, BitVec] = {}
        # CF starts at 0
        self.flags['CF'] = BitVecVal(0, 1)
    
    def get_register(self, reg: Register) -> BitVec:
        """Get register value, initializing if not present.
        
        Args:
            reg: Register to get
            
        Returns:
            Current register value (64-bit BitVec)
        """
        if reg not in self.registers:
            # Initialize with symbolic variable
            self.registers[reg] = BitVec(f"{reg.value}_init", 64)
        return self.registers[reg]
    
    def set_register(self, reg: Register, value: BitVec) -> None:
        """Set register value.
        
        Args:
            reg: Register to set
            value: Value to set (must be 64-bit BitVec)
        """
        if value.size() != 64:
            raise ValueError(f"Register value must be 64 bits, got {value.size()}")
        self.registers[reg] = value
    
    def load_memory(self, offset: int) -> BitVec:
        """Load value from memory at given offset (relative to R14).
        
        Args:
            offset: Memory offset (e.g., -0x40)
            
        Returns:
            Value at memory location (64-bit BitVec)
        """
        if offset not in self.memory:
            # Create symbolic variable if not present
            self.memory[offset] = BitVec(f"mem_{offset:+d}", 64)
        return self.memory[offset]
    
    def store_memory(self, offset: int, value: BitVec) -> None:
        """Store value to memory at given offset (relative to R14).
        
        Args:
            offset: Memory offset
            value: Value to store (must be 64-bit BitVec)
        """
        if value.size() != 64:
            raise ValueError(f"Memory value must be 64 bits, got {value.size()}")
        self.memory[offset] = value
    
    def get_flag(self, flag_name: str) -> BitVec:
        """Get flag value, initializing if not present.
        
        Args:
            flag_name: Flag name (e.g., 'CF')
            
        Returns:
            Flag value (1-bit BitVec)
        """
        if flag_name not in self.flags:
            # Initialize with 0
            self.flags[flag_name] = BitVecVal(0, 1)
        return self.flags[flag_name]
    
    def set_flag(self, flag_name: str, value: BitVec) -> None:
        """Set flag value.
        
        Args:
            flag_name: Flag name (e.g., 'CF')
            value: Flag value (must be 1-bit BitVec)
        """
        if value.size() != 1:
            raise ValueError(f"Flag value must be 1 bit, got {value.size()}")
        self.flags[flag_name] = value

