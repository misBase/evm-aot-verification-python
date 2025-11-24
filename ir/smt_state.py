"""
SMT State Management for Z3 formula modeling.

This module provides unified state management for EVM IR and x86-64 programs,
modeling stack, memory, and registers as symbolic variables.
"""

from typing import Dict, Optional, List, TYPE_CHECKING
from z3 import BitVec, BitVecVal, Array, ArraySort, BitVecSort, IntSort, Int, Select, Store

if TYPE_CHECKING:
    from x86_64.models import Register


class EVMStackState:
    """EVM stack state representation.
    
    Models the EVM stack using Z3 Array: Stack : Array[Int, BitVec[256]]
    Stack pointer SP : Int (range 0-1024)
    Stack top element: Stack[SP-1]
    """
    
    def __init__(self, initial_depth: int = 0, stack_array: Optional[Array] = None, sp: Optional[Int] = None):
        """Initialize EVM stack state.
        
        Args:
            initial_depth: Initial stack depth (for backward compatibility)
            stack_array: Optional existing Stack array
            sp: Optional existing SP pointer
        """
        # Stack : Array[Int, BitVec[256]]
        if stack_array is None:
            self.Stack = Array('Stack', IntSort(), BitVecSort(256))
        else:
            self.Stack = stack_array
        
        # SP : Int (stack pointer, range 0-1024)
        if sp is None:
            self.SP = Int('SP')
        else:
            self.SP = sp
        
        # For backward compatibility, track depth
        self.depth = initial_depth
    
    def push(self, value: BitVec) -> 'EVMStackState':
        """Push a value onto the stack.
        
        PUSH operation: SP' = SP + 1, Stack' = Store(Stack, SP, value)
        
        Args:
            value: 256-bit BitVec value to push
            
        Returns:
            New EVMStackState with updated Stack and SP
        """
        if value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {value.size()}")
        
        # SP' = SP + 1
        new_sp = self.SP + 1
        # Stack' = Store(Stack, SP, value)
        new_stack = Store(self.Stack, self.SP, value)
        
        # Create new state
        new_state = EVMStackState(initial_depth=self.depth + 1, stack_array=new_stack, sp=new_sp)
        return new_state
    
    def pop(self) -> tuple[BitVec, 'EVMStackState']:
        """Pop a value from the stack.
        
        POP operation: value = Select(Stack, SP-1), SP' = SP - 1
        
        Returns:
            Tuple of (popped_value, new_state)
        """
        # value = Select(Stack, SP-1)
        value = Select(self.Stack, self.SP - 1)
        # SP' = SP - 1
        new_sp = self.SP - 1
        # Stack remains the same (we don't modify it, just change SP)
        
        new_state = EVMStackState(initial_depth=max(0, self.depth - 1), stack_array=self.Stack, sp=new_sp)
        return value, new_state
    
    def peek(self, index: int = 0) -> BitVec:
        """Peek at a stack value without popping.
        
        Args:
            index: Stack index (0 = top of stack, 1 = second from top, etc.)
            
        Returns:
            256-bit BitVec value at index
        """
        # Stack index 0 is at SP-1, index 1 is at SP-2, etc.
        stack_index = self.SP - 1 - index
        return Select(self.Stack, stack_index)
    
    @property
    def top(self) -> BitVec:
        """Get the top element of the stack (Stack[SP-1]).
        
        Returns:
            256-bit BitVec value at stack top
        """
        return Select(self.Stack, self.SP - 1)
    
    def back(self, n: int) -> BitVec:
        """Get the value at back(n) position in the stack.
        
        back(0) is the top of stack (Stack[SP-1])
        back(1) is the second from top (Stack[SP-2])
        etc.
        
        Args:
            n: Stack index (0 = top of stack, 1 = second from top, etc.)
            
        Returns:
            256-bit BitVec value at back(n) position
        """
        # back(n) = Stack[SP-1-n]
        stack_index = self.SP - 1 - n
        return Select(self.Stack, stack_index)
    
    def copy(self) -> 'EVMStackState':
        """Create a copy of the stack state.
        
        Returns:
            New EVMStackState instance with same Stack and SP
        """
        # Note: In Z3, arrays and integers are immutable expressions,
        # so we can reuse them directly
        new_state = EVMStackState(initial_depth=self.depth, stack_array=self.Stack, sp=self.SP)
        return new_state


class EVMMemoryState:
    """EVM memory state representation.
    
    Models EVM memory using Z3 Array: Memory : Array[BitVec[64], BitVec[8]]
    Memory size: MSize : BitVec[64] (tracks maximum accessed address)
    
    Note: Although EVM theoretically supports 256-bit addresses, in practice
    AOT-compiled code uses 64-bit addresses, and actual EVM programs never
    use addresses >= 2^64. Using 64-bit addresses simplifies verification
    and improves Z3 solver performance.
    """
    
    def __init__(self, memory_array: Optional[Array] = None, msize: Optional[BitVec] = None):
        """Initialize EVM memory state.
        
        Args:
            memory_array: Optional existing Memory array
            msize: Optional existing MSize variable
        """
        # Memory : Array[BitVec[64], BitVec[8]] - address is 64-bit, value is 8-bit (byte)
        if memory_array is None:
            self.Memory = Array('Memory', BitVecSort(64), BitVecSort(8))
        else:
            self.Memory = memory_array
        
        # MSize : BitVec[64] - tracks maximum accessed address (memory size)
        if msize is None:
            self.MSize = BitVec('MSize', 64)
        else:
            self.MSize = msize
    
    def load_256bit(self, offset: BitVec) -> tuple[BitVec, 'EVMMemoryState']:
        """Load 32 bytes (256 bits) from memory.
        
        MLOAD operation: reads 32 bytes starting at offset
        Memory layout: big-endian (byte at offset is MSB)
        
        Args:
            offset: 64-bit or 256-bit BitVec memory offset (256-bit will be truncated)
            
        Returns:
            Tuple of (256-bit value, new_state with updated MSize)
        """
        from z3 import Concat, If, UGE, Extract as Z3Extract
        
        # If offset is 256-bit, truncate to 64-bit (take lower 64 bits)
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")
        
        # Load 32 bytes: Memory[offset], Memory[offset+1], ..., Memory[offset+31]
        # Concatenate in big-endian order: [byte0|byte1|...|byte31] where byte0 is MSB
        bytes_list = []
        for i in range(32):
            byte_offset = offset + BitVecVal(i, 64)
            byte_val = Select(self.Memory, byte_offset)
            bytes_list.append(byte_val)
        
        # Concatenate: [byte0|byte1|...|byte31] = 256-bit value
        value = Concat(*bytes_list)
        
        # Update MSize: MSize' = If(offset + 32 > MSize, offset + 32, MSize)
        new_msize = If(UGE(offset + BitVecVal(32, 64), self.MSize), 
                       offset + BitVecVal(32, 64), 
                       self.MSize)
        
        new_state = EVMMemoryState(memory_array=self.Memory, msize=new_msize)
        return value, new_state
    
    def store_256bit(self, offset: BitVec, value: BitVec) -> 'EVMMemoryState':
        """Store 32 bytes (256 bits) to memory.
        
        MSTORE operation: writes 32 bytes starting at offset
        Memory layout: big-endian (byte at offset is MSB)
        
        Args:
            offset: 64-bit or 256-bit BitVec memory offset (256-bit will be truncated)
            value: 256-bit BitVec value to store
            
        Returns:
            New EVMMemoryState with updated Memory and MSize
        """
        from z3 import Extract, If, UGE, Extract as Z3Extract
        
        if value.size() != 256:
            raise ValueError(f"Value must be 256 bits, got {value.size()}")
        
        # If offset is 256-bit, truncate to 64-bit (take lower 64 bits)
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")
        
        # Extract 32 bytes from value: byte0 (MSB) to byte31 (LSB)
        # Store them at Memory[offset], Memory[offset+1], ..., Memory[offset+31]
        new_memory = self.Memory
        for i in range(32):
            # Extract byte i: bits [255-8*i : 248-8*i] (byte0 is MSB)
            byte_val = Extract(255 - 8*i, 248 - 8*i, value)
            byte_offset = offset + BitVecVal(i, 64)
            new_memory = Store(new_memory, byte_offset, byte_val)
        
        # Update MSize: MSize' = If(offset + 32 > MSize, offset + 32, MSize)
        new_msize = If(UGE(offset + BitVecVal(32, 64), self.MSize), 
                       offset + BitVecVal(32, 64), 
                       self.MSize)
        
        new_state = EVMMemoryState(memory_array=new_memory, msize=new_msize)
        return new_state
    
    def get_byte(self, offset: BitVec) -> BitVec:
        """Get a single byte from memory.
        
        Args:
            offset: 64-bit or 256-bit BitVec memory offset (256-bit will be truncated)
            
        Returns:
            8-bit BitVec value
        """
        from z3 import Extract as Z3Extract
        
        # If offset is 256-bit, truncate to 64-bit
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")
        
        return Select(self.Memory, offset)
    
    def set_byte(self, offset: BitVec, value: BitVec) -> 'EVMMemoryState':
        """Set a single byte in memory.
        
        Args:
            offset: 64-bit or 256-bit BitVec memory offset (256-bit will be truncated)
            value: 8-bit BitVec value
            
        Returns:
            New EVMMemoryState with updated Memory and MSize
        """
        from z3 import If, UGE, Extract as Z3Extract
        
        if value.size() != 8:
            raise ValueError(f"Memory byte must be 8 bits, got {value.size()}")
        
        # If offset is 256-bit, truncate to 64-bit
        if offset.size() == 256:
            offset = Z3Extract(63, 0, offset)
        elif offset.size() != 64:
            raise ValueError(f"Offset must be 64 or 256 bits, got {offset.size()}")
        
        new_memory = Store(self.Memory, offset, value)
        
        # Update MSize: MSize' = If(offset + 1 > MSize, offset + 1, MSize)
        new_msize = If(UGE(offset + BitVecVal(1, 64), self.MSize), 
                       offset + BitVecVal(1, 64), 
                       self.MSize)
        
        new_state = EVMMemoryState(memory_array=new_memory, msize=new_msize)
        return new_state
    
    def copy(self) -> 'EVMMemoryState':
        """Create a copy of the memory state.
        
        Returns:
            New EVMMemoryState instance with same Memory and MSize
        """
        new_state = EVMMemoryState(memory_array=self.Memory, msize=self.MSize)
        return new_state


class X86MemoryState:
    """x86-64 memory state representation.
    
    Models x86-64 memory using Z3 Array: Memory : Array[BitVec[64], BitVec[8]]
    Supports symbolic indexing (e.g., [r14+rax] where offset is symbolic)
    Uses byte-level addressing for precise memory modeling.
    """
    
    def __init__(self, memory_array: Optional[Array] = None):
        """Initialize x86-64 memory state.
        
        Args:
            memory_array: Optional existing Memory array
        """
        # Memory : Array[BitVec[64], BitVec[8]] - offset is 64-bit, value is 8-bit (byte)
        if memory_array is None:
            self.Memory = Array('X86Memory', BitVecSort(64), BitVecSort(8))
        else:
            self.Memory = memory_array
    
    def load_byte(self, offset: BitVec) -> BitVec:
        """Load a single byte from memory.
        
        Supports symbolic offsets (e.g., base_offset + reg_value)
        
        Args:
            offset: 64-bit BitVec memory offset (can be symbolic)
            
        Returns:
            8-bit BitVec value
        """
        if isinstance(offset, int):
            # Convert int to BitVec for backward compatibility
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")
        
        return Select(self.Memory, offset)
    
    def store_byte(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """Store a single byte to memory.
        
        Supports symbolic offsets (e.g., base_offset + reg_value)
        
        Args:
            offset: 64-bit BitVec memory offset (can be symbolic)
            value: 8-bit BitVec value
            
        Returns:
            New X86MemoryState with updated Memory
        """
        if isinstance(offset, int):
            # Convert int to BitVec for backward compatibility
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")
        
        if value.size() != 8:
            raise ValueError(f"Memory byte must be 8 bits, got {value.size()}")
        
        new_memory = Store(self.Memory, offset, value)
        new_state = X86MemoryState(memory_array=new_memory)
        return new_state
    
    def load_64bit(self, offset: BitVec) -> BitVec:
        """Load a 64-bit value from memory (little-endian).
        
        Args:
            offset: 64-bit BitVec memory offset
            
        Returns:
            64-bit BitVec value
        """
        from z3 import Concat
        
        if isinstance(offset, int):
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")
        
        # Load 8 bytes in little-endian order: [byte0|byte1|...|byte7]
        # where byte0 is at offset (LSB), byte7 is at offset+7 (MSB)
        bytes_list = []
        for i in range(8):
            byte_offset = offset + BitVecVal(i, 64)
            byte_val = Select(self.Memory, byte_offset)
            bytes_list.append(byte_val)
        
        # Concatenate in little-endian order: [byte7|byte6|...|byte0]
        return Concat(*reversed(bytes_list))
    
    def store_64bit(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """Store a 64-bit value to memory (little-endian).
        
        Args:
            offset: 64-bit BitVec memory offset
            value: 64-bit BitVec value
            
        Returns:
            New X86MemoryState with updated Memory
        """
        from z3 import Extract
        
        if isinstance(offset, int):
            offset = BitVecVal(offset, 64)
        elif offset.size() != 64:
            raise ValueError(f"Memory offset must be 64 bits, got {offset.size()}")
        
        if value.size() != 64:
            raise ValueError(f"Value must be 64 bits, got {value.size()}")
        
        # Store 8 bytes in little-endian order
        new_memory = self.Memory
        for i in range(8):
            # Extract byte i: bits [8*i+7 : 8*i] (byte0 is LSB)
            byte_val = Extract(8*i+7, 8*i, value)
            byte_offset = offset + BitVecVal(i, 64)
            new_memory = Store(new_memory, byte_offset, byte_val)
        
        new_state = X86MemoryState(memory_array=new_memory)
        return new_state
    
    def load_limb(self, offset: BitVec) -> BitVec:
        """Load a 64-bit limb from memory (backward compatibility).
        
        This is an alias for load_64bit() to maintain backward compatibility.
        
        Args:
            offset: 64-bit BitVec memory offset (can be symbolic)
            
        Returns:
            64-bit BitVec value
        """
        return self.load_64bit(offset)
    
    def store_limb(self, offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """Store a 64-bit limb to memory (backward compatibility).
        
        This is an alias for store_64bit() to maintain backward compatibility.
        
        Args:
            offset: 64-bit BitVec memory offset (can be symbolic)
            value: 64-bit BitVec value
            
        Returns:
            New X86MemoryState with updated Memory
        """
        return self.store_64bit(offset, value)
    
    def load_256bit(self, base_offset: BitVec) -> BitVec:
        """Load a 256-bit value from memory (4×64-bit limbs, little-endian).
        
        Args:
            base_offset: 64-bit BitVec base offset for the 256-bit value (LSB offset)
            
        Returns:
            256-bit BitVec
        """
        from z3 import Concat
        
        if isinstance(base_offset, int):
            base_offset = BitVecVal(base_offset, 64)
        
        # Load 4 limbs: z0 (LSB) at base_offset, z1 at base_offset+8, etc.
        z0 = self.load_64bit(base_offset)
        z1 = self.load_64bit(base_offset + BitVecVal(8, 64))
        z2 = self.load_64bit(base_offset + BitVecVal(16, 64))
        z3 = self.load_64bit(base_offset + BitVecVal(24, 64))
        
        # Concatenate: [z3|z2|z1|z0] for 256-bit value
        return Concat(z3, z2, z1, z0)
    
    def store_256bit(self, base_offset: BitVec, value: BitVec) -> 'X86MemoryState':
        """Store a 256-bit value to memory (4×64-bit limbs, little-endian).
        
        Args:
            base_offset: 64-bit BitVec base offset for the 256-bit value (LSB offset)
            value: 256-bit BitVec
            
        Returns:
            New X86MemoryState with updated Memory
        """
        from z3 import Extract
        
        if isinstance(base_offset, int):
            base_offset = BitVecVal(base_offset, 64)
        
        if value.size() != 256:
            raise ValueError(f"Value must be 256 bits, got {value.size()}")
        
        # Extract 4 limbs: z0 (LSB), z1, z2, z3 (MSB)
        z0 = Extract(63, 0, value)
        z1 = Extract(127, 64, value)
        z2 = Extract(191, 128, value)
        z3 = Extract(255, 192, value)
        
        # Store limbs (each store returns a new state)
        new_state = self.store_64bit(base_offset, z0)
        new_state = new_state.store_64bit(base_offset + BitVecVal(8, 64), z1)
        new_state = new_state.store_64bit(base_offset + BitVecVal(16, 64), z2)
        new_state = new_state.store_64bit(base_offset + BitVecVal(24, 64), z3)
        
        return new_state
    
    def copy(self) -> 'X86MemoryState':
        """Create a copy of the memory state.
        
        Returns:
            New X86MemoryState instance with same Memory
        """
        new_state = X86MemoryState(memory_array=self.Memory)
        return new_state


class X86RegisterState:
    """x86-64 register state representation.
    
    Models x86-64 registers as 64-bit symbolic variables.
    """
    
    def __init__(self):
        """Initialize x86-64 register state."""
        # Registers: reg[Register] is a 64-bit BitVec
        # Use string keys to avoid circular import
        self._registers: Dict[str, BitVec] = {}
        # Flags: flags[name] is a 1-bit BitVec
        self._flags: Dict[str, BitVec] = {}
        # CF (carry flag) starts at 0
        self._flags['CF'] = BitVecVal(0, 1)
    
    def get_register(self, reg) -> BitVec:
        """Get register value.
        
        Args:
            reg: Register to get (Register enum or string)
            
        Returns:
            64-bit BitVec
        """
        # Convert Register enum to string key
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        if reg_key not in self._registers:
            self._registers[reg_key] = BitVec(f"{reg_key}_init", 64)
        return self._registers[reg_key]
    
    def set_register(self, reg, value: BitVec) -> None:
        """Set register value.
        
        Args:
            reg: Register to set (Register enum or string)
            value: 64-bit BitVec
        """
        if value.size() != 64:
            raise ValueError(f"Register value must be 64 bits, got {value.size()}")
        # Convert Register enum to string key
        reg_key = reg.value if hasattr(reg, 'value') else str(reg)
        self._registers[reg_key] = value
    
    def get_flag(self, flag_name: str) -> BitVec:
        """Get flag value.
        
        Args:
            flag_name: Flag name (e.g., 'CF')
            
        Returns:
            1-bit BitVec
        """
        if flag_name not in self._flags:
            self._flags[flag_name] = BitVecVal(0, 1)
        return self._flags[flag_name]
    
    def set_flag(self, flag_name: str, value: BitVec) -> None:
        """Set flag value.
        
        Args:
            flag_name: Flag name
            value: 1-bit BitVec
        """
        if value.size() != 1:
            raise ValueError(f"Flag value must be 1 bit, got {value.size()}")
        self._flags[flag_name] = value
    
    def copy(self) -> 'X86RegisterState':
        """Create a copy of the register state.
        
        Returns:
            New X86RegisterState instance
        """
        new_state = X86RegisterState()
        new_state._registers = self._registers.copy()
        new_state._flags = self._flags.copy()
        return new_state


class SMTState:
    """Unified SMT state for program verification.
    
    Manages all symbolic state: EVM stack/memory, x86 memory/registers.
    """
    
    def __init__(self):
        """Initialize unified SMT state."""
        self.evm_stack = EVMStackState()
        self.evm_memory = EVMMemoryState()
        self.x86_memory = X86MemoryState()
        self.x86_registers = X86RegisterState()
        
        # RETURN instruction tracking
        # Store offset and length instead of extracting Array
        # This allows direct memory comparison without max_bytes limitation
        # Use conditional symbolic values: 0 means no return value
        from z3 import BitVecVal
        self.return_offset: BitVec = BitVecVal(0, 64)  # Return offset (64-bit), 0 = no return
        self.return_length: BitVec = BitVecVal(0, 64)  # Return length (64-bit), 0 = no return
    
    def copy(self) -> 'SMTState':
        """Create a copy of the state.
        
        Returns:
            New SMTState instance
        """
        new_state = SMTState()
        new_state.evm_stack = self.evm_stack.copy()
        new_state.evm_memory = self.evm_memory.copy()
        new_state.x86_memory = self.x86_memory.copy()
        new_state.x86_registers = self.x86_registers.copy()
        new_state.return_offset = self.return_offset
        new_state.return_length = self.return_length
        return new_state

