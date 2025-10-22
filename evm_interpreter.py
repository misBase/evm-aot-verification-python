"""
EVM Interpreter Model for Verification

This module models the EVM execution semantics using Z3 symbolic values.
It represents 256-bit integers as 4x64-bit limbs (z0, z1, z2, z3).
"""

from z3 import BitVec, BitVecVal, Concat, Extract, LShR, simplify
from typing import Tuple


class Uint256:
    """Represents a 256-bit unsigned integer as 4x64-bit limbs.
    
    Layout: [z3 (bits 192-255) | z2 (bits 128-191) | z1 (bits 64-127) | z0 (bits 0-63)]
    """
    
    def __init__(self, z0, z1, z2, z3):
        """Initialize with 4x64-bit limbs."""
        self.z0 = z0  # Least significant limb
        self.z1 = z1
        self.z2 = z2
        self.z3 = z3  # Most significant limb
    
    def to_bv256(self):
        """Convert to a single 256-bit bitvector."""
        return Concat(self.z3, self.z2, self.z1, self.z0)
    
    @staticmethod
    def from_bv256(bv):
        """Create Uint256 from a 256-bit bitvector."""
        z0 = Extract(63, 0, bv)
        z1 = Extract(127, 64, bv)
        z2 = Extract(191, 128, bv)
        z3 = Extract(255, 192, bv)
        return Uint256(z0, z1, z2, z3)
    
    @staticmethod
    def from_int(value):
        """Create Uint256 from a Python integer."""
        bv = BitVecVal(value, 256)
        return Uint256.from_bv256(bv)
    
    @staticmethod
    def symbolic(name):
        """Create a symbolic Uint256 variable."""
        z0 = BitVec(f"{name}_z0", 64)
        z1 = BitVec(f"{name}_z1", 64)
        z2 = BitVec(f"{name}_z2", 64)
        z3 = BitVec(f"{name}_z3", 64)
        return Uint256(z0, z1, z2, z3)
    
    def __repr__(self):
        return f"Uint256(z0={self.z0}, z1={self.z1}, z2={self.z2}, z3={self.z3})"


class EVMStack:
    """Models the EVM stack."""
    
    def __init__(self):
        self.items = []
    
    def push(self, value: Uint256):
        """Push a 256-bit value onto the stack."""
        self.items.append(value)
    
    def pop(self) -> Uint256:
        """Pop a 256-bit value from the stack."""
        if not self.items:
            raise IndexError("Stack underflow")
        return self.items.pop()
    
    def peek(self, index=0) -> Uint256:
        """Peek at a value on the stack without popping."""
        if index >= len(self.items):
            raise IndexError("Stack index out of range")
        return self.items[-(index + 1)]
    
    def __len__(self):
        return len(self.items)
    
    def __repr__(self):
        return f"EVMStack({len(self.items)} items)"


class EVMInterpreter:
    """Symbolic EVM interpreter for verification."""
    
    def __init__(self, initial_stack=None):
        """Initialize with optional symbolic stack.
        
        Args:
            initial_stack: List of Uint256 values for initial stack state.
                          If None, creates an empty stack.
        """
        self.stack = EVMStack()
        if initial_stack:
            for val in initial_stack:
                self.stack.push(val)
    
    def push1(self, value: int):
        """PUSH1 opcode: Push a 1-byte value onto the stack."""
        uint256_val = Uint256.from_int(value)
        self.stack.push(uint256_val)
    
    def add(self) -> Uint256:
        """ADD opcode: Pop two values, add them (mod 2^256), push result.
        
        Returns the result for verification purposes.
        """
        # Pop two operands (top two items)
        b = self.stack.pop()  # Second operand (top of stack)
        a = self.stack.pop()  # First operand
        
        # Perform 256-bit addition with carry propagation
        result = self._add_uint256(a, b)
        
        # Push result back
        self.stack.push(result)
        
        return result
    
    def _add_uint256(self, a: Uint256, b: Uint256) -> Uint256:
        """Add two Uint256 values with carry propagation.
        
        This models the EVM ADD operation which performs modular arithmetic.
        """
        # Add limb 0 (LSB)
        sum0, carry0 = self._add64_carry(a.z0, b.z0, BitVecVal(0, 64))
        
        # Add limb 1 with carry
        sum1, carry1 = self._add64_carry(a.z1, b.z1, carry0)
        
        # Add limb 2 with carry
        sum2, carry2 = self._add64_carry(a.z2, b.z2, carry1)
        
        # Add limb 3 (MSB) with carry (overflow is discarded)
        sum3, _ = self._add64_carry(a.z3, b.z3, carry2)
        
        return Uint256(sum0, sum1, sum2, sum3)
    
    def _add64_carry(self, x, y, c) -> Tuple:
        """Add two 64-bit values with carry input, return sum and carry output.
        
        Args:
            x: First 64-bit operand
            y: Second 64-bit operand
            c: Carry input (0 or 1 as 64-bit value)
        
        Returns:
            (sum, carry) where both are 64-bit values
        """
        # Extend to 65 bits to capture carry
        x_ext = Concat(BitVecVal(0, 1), x)
        y_ext = Concat(BitVecVal(0, 1), y)
        c_ext = Concat(BitVecVal(0, 1), c)
        
        # Perform addition
        sum_ext = x_ext + y_ext + c_ext
        
        # Extract result and carry
        sum_val = Extract(63, 0, sum_ext)
        carry_val = Extract(64, 64, sum_ext)
        
        # Extend carry back to 64 bits
        carry_64 = Concat(BitVecVal(0, 63), carry_val)
        
        return sum_val, carry_64
    
    def get_top(self) -> Uint256:
        """Get the top value from the stack."""
        return self.stack.peek(0)
    
    def execute_bytecode(self, bytecode: bytes) -> Uint256:
        """Execute EVM bytecode symbolically.
        
        Args:
            bytecode: Raw EVM bytecode
            
        Returns:
            The top value on the stack after execution
        """
        pc = 0
        while pc < len(bytecode):
            opcode = bytecode[pc]
            
            if opcode == 0x60:  # PUSH1
                pc += 1
                value = bytecode[pc]
                self.push1(value)
            elif opcode == 0x01:  # ADD
                self.add()
            else:
                raise ValueError(f"Unsupported opcode: 0x{opcode:02x} at pc={pc}")
            
            pc += 1
        
        return self.get_top()


def verify_evm_add_symbolic():
    """Test ADD with symbolic stack values."""
    # Create symbolic stack with two values
    val1 = Uint256.symbolic("stack_val1")
    val2 = Uint256.symbolic("stack_val2")
    
    # Initialize interpreter with symbolic stack
    interp = EVMInterpreter(initial_stack=[val1, val2])
    
    # Execute ADD
    result = interp.add()
    
    print(f"EVM Symbolic ADD Test")
    print(f"  Input 1: {val1}")
    print(f"  Input 2: {val2}")
    print(f"  Result: {result}")
    
    return result


def verify_evm_add_concrete():
    """Test ADD with concrete values."""
    # Create concrete stack
    val1 = Uint256.from_int(0x60)
    val2 = Uint256.from_int(0x10)
    
    # Initialize interpreter with concrete stack
    interp = EVMInterpreter(initial_stack=[val1, val2])
    
    # Execute ADD
    result = interp.add()
    
    # Check result
    result_bv = result.to_bv256()
    expected = BitVecVal(0x70, 256)
    
    print(f"EVM Concrete ADD Test")
    result_simplified = simplify(result_bv)
    print(f"  0x60 + 0x10 = {result_simplified}")
    print(f"  Match: {simplify(result_bv == expected)}")
    
    return result


if __name__ == "__main__":
    print("=== EVM Interpreter Tests ===\n")
    print("[Test 1] Symbolic ADD")
    verify_evm_add_symbolic()
    print("\n[Test 2] Concrete ADD")
    verify_evm_add_concrete()

