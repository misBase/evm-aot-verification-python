"""
EVM Stack: Models the EVM stack for verification.
"""

from typing import List
from .uint256 import Uint256


class EVMStack:
    """Models the EVM stack."""
    
    def __init__(self):
        """Initialize an empty stack."""
        self.items: List[Uint256] = []
    
    def push(self, value: Uint256):
        """Push a 256-bit value onto the stack.
        
        Args:
            value: Uint256 value to push
        """
        self.items.append(value)
    
    def pop(self) -> Uint256:
        """Pop a 256-bit value from the stack.
        
        Returns:
            Uint256 value from the top of the stack
            
        Raises:
            IndexError: If stack is empty
        """
        if not self.items:
            raise IndexError("Stack underflow")
        return self.items.pop()
    
    def peek(self, index: int = 0) -> Uint256:
        """Peek at a value on the stack without popping.
        
        Args:
            index: Index from top (0 = top element)
            
        Returns:
            Uint256 value at the specified index
            
        Raises:
            IndexError: If index is out of range
        """
        if index >= len(self.items):
            raise IndexError("Stack index out of range")
        return self.items[-(index + 1)]
    
    def __len__(self):
        """Return the number of items on the stack."""
        return len(self.items)
    
    def __repr__(self):
        return f"EVMStack({len(self.items)} items)"

