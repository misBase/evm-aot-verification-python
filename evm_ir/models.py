"""
EVM IR data models.

This module defines the data structures for representing EVM IR blocks and operations.
"""

from typing import List, Optional, Dict, Any, TYPE_CHECKING
from dataclasses import dataclass, field

if TYPE_CHECKING:
    from ir.smt_state import SMTState


@dataclass
class EvmOperator:
    """Represents an EVM operation in the IR."""
    
    kind: str  # Operation kind (e.g., "ADD", "PUSH", "JUMP")
    pc: int  # Program counter (original bytecode position)
    immediate: Optional[int] = None  # Immediate value (for PUSH operations)
    param: Optional[int] = None  # Parameter (for PUSH, DUP, SWAP)
    is_static: bool = False  # Whether jump is static
    block: Optional['EVMBlock'] = None  # Reference to containing block
    
    @classmethod
    def from_json(cls, data: Dict[str, Any], block: Optional['EVMBlock'] = None) -> 'EvmOperator':
        """Create EvmOperator from JSON data.
        
        Args:
            data: Dictionary containing operator data
            block: Optional reference to containing block
            
        Returns:
            EvmOperator instance
        """
        # Handle immediate value: now always string from Go side, but support int for backward compatibility
        immediate = data.get('immediate')
        if immediate is not None:
            # Convert to int (Python 3 int supports arbitrary precision)
            # Go side now always uses string, but we support int for backward compatibility
            immediate = int(immediate)
        
        return cls(
            kind=data.get('kind', ''),
            pc=data.get('pc', 0),
            immediate=immediate,
            param=data.get('param'),
            is_static=data.get('is_static', False),
            block=block
        )
    
    def to_json(self) -> Dict[str, Any]:
        """Convert to JSON-serializable dictionary.
        
        Returns:
            Dictionary representation
        """
        result = {
            'kind': self.kind,
            'pc': self.pc,
        }
        if self.immediate is not None:
            result['immediate'] = self.immediate
        if self.param is not None:
            result['param'] = self.param
        if self.is_static:
            result['is_static'] = self.is_static
        return result
    
    def to_z3(self, state: 'SMTState') -> 'SMTState':
        """Convert this operator to Z3 formula, updating state.
        
        This is the Alive2-style direct formula construction method.
        Delegates to the semantics module for actual implementation.
        
        Args:
            state: Current SMT state (will be modified)
            
        Returns:
            Updated SMT state
        """
        # Import here to avoid circular dependency
        from evm_ir.semantics import evm_operator_to_z3
        return evm_operator_to_z3(self, state)


@dataclass
class EVMBlock:
    """Represents an EVM basic block in the IR."""
    
    pc: int  # Block tag number (PC address)
    stack_depth: int  # Stack depth used by this block
    min_depth: int  # Minimum stack depth required
    max_depth: int  # Maximum stack depth
    static_gas: int  # Static gas cost
    is_jump_target: bool  # Whether this block is a jump target
    is_inner_block: bool  # Whether this is an inner block
    is_stop: bool  # Whether block contains STOP instruction
    operations: List[EvmOperator] = field(default_factory=list)  # Operations in this block
    
    @classmethod
    def from_json(cls, data: Dict[str, Any]) -> 'EVMBlock':
        """Create EVMBlock from JSON data.
        
        Args:
            data: Dictionary containing block data
            
        Returns:
            EVMBlock instance
        """
        block = cls(
            pc=data.get('pc', 0),
            stack_depth=data.get('stack_depth', 0),
            min_depth=data.get('min_depth', 0),
            max_depth=data.get('max_depth', 0),
            static_gas=data.get('static_gas', 0),
            is_jump_target=data.get('is_jump_target', False),
            is_inner_block=data.get('is_inner_block', False),
            is_stop=data.get('is_stop', False),
        )
        
        # Parse operations
        operations_data = data.get('operations', [])
        for op_data in operations_data:
            op = EvmOperator.from_json(op_data, block=block)
            block.operations.append(op)
        
        return block
    
    def to_json(self) -> Dict[str, Any]:
        """Convert to JSON-serializable dictionary.
        
        Returns:
            Dictionary representation
        """
        return {
            'pc': self.pc,
            'stack_depth': self.stack_depth,
            'min_depth': self.min_depth,
            'max_depth': self.max_depth,
            'static_gas': self.static_gas,
            'is_jump_target': self.is_jump_target,
            'is_inner_block': self.is_inner_block,
            'is_stop': self.is_stop,
            'operations': [op.to_json() for op in self.operations]
        }
    
    def __repr__(self):
        return (f"EVMBlock(pc={self.pc}, stack_depth={self.stack_depth}, "
                f"ops={len(self.operations)}, is_jump_target={self.is_jump_target})")

