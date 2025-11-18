"""
EVM IR program-level models.

This module provides program-level semantics for EVM IR, operating on
entire programs (sequences of blocks) rather than individual blocks.
"""

from typing import List, Dict, Any, Optional
from z3 import BitVec, BitVecVal, Solver
from .models import EVMBlock
from .semantics import EVMIRSemantics
from .json_parser import CompilerEVMResult


class EVMProgram:
    """Represents a complete EVM program with multiple blocks.
    
    This wraps CompilerEVMResult and provides program-level verification
    capabilities for the entire IR sequence.
    """
    
    def __init__(self, compiler_result: CompilerEVMResult):
        """Initialize the EVM program.
        
        Args:
            compiler_result: The compilation result containing all blocks
        """
        self.compiler_result = compiler_result
        self.blocks = compiler_result.blocks
        self.semantics = EVMIRSemantics()
        
        # Build a block lookup table by PC
        self.blocks_by_pc: Dict[int, EVMBlock] = {}
        for block in self.blocks:
            self.blocks_by_pc[block.pc] = block
    
    def get_entrypoint(self) -> EVMBlock:
        """Get the program entrypoint (first block).
        
        Returns:
            The first block in the program (entrypoint)
        """
        if len(self.blocks) == 0:
            raise ValueError("Program has no blocks")
        return self.blocks[0]
    
    def get_block_by_pc(self, pc: int) -> Optional[EVMBlock]:
        """Get a block by its PC value.
        
        Args:
            pc: Program counter value
            
        Returns:
            The block at the given PC, or None if not found
        """
        return self.blocks_by_pc.get(pc)
    
    def build_program_semantics(self, initial_stack: List[BitVec]) -> Dict[str, Any]:
        """Build semantic formula for the entire program.
        
        This executes all blocks in sequence starting from the entrypoint,
        following control flow through jumps and branches.
        
        For now, we support straight-line execution (no branches).
        Future versions will support control flow analysis.
        
        Args:
            initial_stack: Initial stack state (list of 256-bit BitVecs)
            
        Returns:
            Dictionary containing:
            - output_stack: Final stack state after program execution
            - semantic_formula: Overall semantic formula for the program
            - executed_blocks: List of blocks that were executed
        """
        current_stack = list(initial_stack)
        executed_blocks = []
        
        # For now, execute all blocks in sequence (straight-line execution)
        # TODO: Add control flow analysis for JUMP/JUMPI
        for block in self.blocks:
            result = self.semantics.build_block_semantics(block, current_stack)
            current_stack = result['output_stack']
            executed_blocks.append(block)
            
            # Check if block ends with a terminating instruction
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind.upper() in ['STOP', 'RETURN', 'REVERT', 'SELFDESTRUCT']:
                    break
        
        # The final semantic formula is the top of the stack
        if current_stack:
            semantic_formula = current_stack[-1]
        else:
            semantic_formula = BitVecVal(0, 256)
        
        return {
            'output_stack': current_stack,
            'semantic_formula': semantic_formula,
            'executed_blocks': executed_blocks,
            'output_count': len(current_stack)
        }
    
    def build_program_semantics_for_operation(self, 
                                              operation_kind: str,
                                              input_stack: Optional[List[BitVec]] = None) -> Dict[str, Any]:
        """Build program semantics focusing on a specific operation type.
        
        This is useful for verifying specific operations like ADD across
        the entire program.
        
        Args:
            operation_kind: The operation kind to focus on (e.g., "ADD")
            input_stack: Optional input stack. If None, creates symbolic inputs
                        or empty stack depending on whether the block has PUSH ops.
            
        Returns:
            Dictionary containing semantic formula and metadata
        """
        from common.uint256 import Uint256
        
        # Find blocks containing the target operation
        target_blocks = []
        for block in self.blocks:
            for op in block.operations:
                if op.kind.upper() == operation_kind.upper():
                    target_blocks.append(block)
                    break
        
        if not target_blocks:
            raise ValueError(f"No blocks found with {operation_kind} operation")
        
        # For single-operation programs (like ADD), we can directly
        # build semantics for the relevant block
        if len(target_blocks) == 1:
            block = target_blocks[0]
            
            # Check if block has PUSH operations before the target operation
            has_push_before_target = False
            for op in block.operations:
                if op.kind.upper() == operation_kind.upper():
                    break
                if op.kind.upper().startswith("PUSH"):
                    has_push_before_target = True
                    break
            
            if input_stack is None:
                # If block has PUSH operations, start with empty stack
                # Otherwise, create symbolic inputs
                if has_push_before_target:
                    input_stack = []
                else:
                    # Create symbolic inputs based on operation requirements
                    if operation_kind.upper() == "ADD":
                        val1 = Uint256.symbolic(f"program_val1")
                        val2 = Uint256.symbolic(f"program_val2")
                        input_stack = [val1.to_bv256(), val2.to_bv256()]
                    else:
                        raise NotImplementedError(f"Default inputs for {operation_kind} not implemented")
            
            return self.semantics.build_block_semantics(block, input_stack)
        
        # For multi-block operations, execute in sequence
        return self.build_program_semantics(input_stack)
    
    def __repr__(self):
        return f"EVMProgram(blocks={len(self.blocks)})"

