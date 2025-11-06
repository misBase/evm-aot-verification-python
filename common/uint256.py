"""
Uint256: Represents a 256-bit unsigned integer as 4x64-bit limbs.

This module provides utilities for working with 256-bit values in the verification system.
"""

from z3 import BitVec, BitVecVal, Concat, Extract


class Uint256:
    """Represents a 256-bit unsigned integer as 4x64-bit limbs.
    
    Layout: [z3 (bits 192-255) | z2 (bits 128-191) | z1 (bits 64-127) | z0 (bits 0-63)]
    """
    
    def __init__(self, z0, z1, z2, z3):
        """Initialize with 4x64-bit limbs.
        
        Args:
            z0: Least significant 64 bits
            z1: Bits 64-127
            z2: Bits 128-191
            z3: Most significant 64 bits (bits 192-255)
        """
        self.z0 = z0  # Least significant limb
        self.z1 = z1
        self.z2 = z2
        self.z3 = z3  # Most significant limb
    
    def to_bv256(self):
        """Convert to a single 256-bit bitvector.
        
        Returns:
            Z3 BitVec of size 256
        """
        return Concat(self.z3, self.z2, self.z1, self.z0)
    
    @staticmethod
    def from_bv256(bv):
        """Create Uint256 from a 256-bit bitvector.
        
        Args:
            bv: Z3 BitVec of size 256
            
        Returns:
            Uint256 instance
        """
        z0 = Extract(63, 0, bv)
        z1 = Extract(127, 64, bv)
        z2 = Extract(191, 128, bv)
        z3 = Extract(255, 192, bv)
        return Uint256(z0, z1, z2, z3)
    
    @staticmethod
    def from_int(value):
        """Create Uint256 from a Python integer.
        
        Args:
            value: Python int (will be truncated to 256 bits)
            
        Returns:
            Uint256 instance
        """
        bv = BitVecVal(value, 256)
        return Uint256.from_bv256(bv)
    
    @staticmethod
    def symbolic(name):
        """Create a symbolic Uint256 variable.
        
        Args:
            name: Base name for the symbolic variables (will create name_z0, name_z1, etc.)
            
        Returns:
            Uint256 with symbolic limbs
        """
        z0 = BitVec(f"{name}_z0", 64)
        z1 = BitVec(f"{name}_z1", 64)
        z2 = BitVec(f"{name}_z2", 64)
        z3 = BitVec(f"{name}_z3", 64)
        return Uint256(z0, z1, z2, z3)
    
    def add_semantics(self, other: 'Uint256') -> 'Uint256':
        """Add two Uint256 values with carry propagation (semantic modeling).
        
        This implements EVM ADD semantics using 4x64-bit limb addition with carry.
        The implementation matches the x86-64 AOT compiler's approach.
        
        Args:
            other: Another Uint256 value to add
            
        Returns:
            New Uint256 instance representing the sum (a + b) mod 2^256
        """
        from z3 import BitVecVal, Concat, Extract
        
        # Perform 4x64-bit additions with carry propagation
        # This matches the x86-64 implementation
        
        # Limb 0: result_z0 = self.z0 + other.z0
        # Extend to 65 bits to capture carry
        sum0_ext = Concat(BitVecVal(0, 1), self.z0) + Concat(BitVecVal(0, 1), other.z0)
        result_z0 = Extract(63, 0, sum0_ext)
        carry0 = Extract(64, 64, sum0_ext)
        
        # Limb 1: result_z1 = self.z1 + other.z1 + carry0
        sum1_ext = (Concat(BitVecVal(0, 1), self.z1) + 
                    Concat(BitVecVal(0, 1), other.z1) + 
                    Concat(BitVecVal(0, 64), carry0))
        result_z1 = Extract(63, 0, sum1_ext)
        carry1 = Extract(64, 64, sum1_ext)
        
        # Limb 2: result_z2 = self.z2 + other.z2 + carry1
        sum2_ext = (Concat(BitVecVal(0, 1), self.z2) + 
                    Concat(BitVecVal(0, 1), other.z2) + 
                    Concat(BitVecVal(0, 64), carry1))
        result_z2 = Extract(63, 0, sum2_ext)
        carry2 = Extract(64, 64, sum2_ext)
        
        # Limb 3: result_z3 = self.z3 + other.z3 + carry2
        # carry3 is discarded (256-bit overflow)
        sum3_ext = (Concat(BitVecVal(0, 1), self.z3) + 
                    Concat(BitVecVal(0, 1), other.z3) + 
                    Concat(BitVecVal(0, 64), carry2))
        result_z3 = Extract(63, 0, sum3_ext)
        
        return Uint256(result_z0, result_z1, result_z2, result_z3)
    
    def __repr__(self):
        return f"Uint256(z0={self.z0}, z1={self.z1}, z2={self.z2}, z3={self.z3})"

