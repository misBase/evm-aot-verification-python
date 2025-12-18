"""
EVM IR program-level models.

This module provides program-level semantics for EVM IR, operating on
entire programs (sequences of blocks) rather than individual blocks.
"""

from typing import List, Dict, Any, Optional, Tuple
from z3 import BitVec, BitVecVal, Solver, If, BoolVal, And
from .models import EVMBlock
from .semantics import EVMIRSemantics, execute_block_with_tag
from .json_parser import CompilerEVMResult
from .cfg import build_ir_cfg
from state.smt_state import SMTState


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
    
    def to_z3(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """Build Z3 formula for the entire program using two-level path-aware execution.
        
        Level 1: Execute each block with TAG path merging (3 paths per block)
        Level 2: Execute CFG paths and merge at CFG level
        
        Args:
            state: Initial SMT state with inputs already prepared
        
        Returns:
            Tuple of (final_state, result_dict) where:
            - final_state: Final SMT state after program execution
            - result_dict: Dictionary with merged return values (offset, length, memory, has_return)
        """
        # Build CFG
        cfg = build_ir_cfg(self.blocks)
        
        # Find all paths from entry to terminals
        entry = cfg.get_entry_block()
        terminals = cfg.get_terminal_blocks()
        paths = cfg.find_all_paths(entry, terminals)
        
        if not paths:
            # Fallback: if no paths found, use simple sequential execution
            return self._to_z3_sequential(state)
        
        # Execute each path and collect results
        path_results = []
        for path_blocks, path_condition in paths:
            # Execute path: Level 1 (block-level) + Level 2 (CFG-level)
            path_state = state.copy()
            
            # Execute each block in the path (Level 1: TAG merging happens in each block)
            for block in path_blocks:
                path_state, _ = execute_block_with_tag(block, path_state)
            
            # Extract result for this path
            from z3 import Ne, BitVecVal
            has_return = Ne(path_state.return_length, BitVecVal(0, 64))
            
            path_result = {
                'offset': path_state.return_offset,
                'length': path_state.return_length,
                'memory': path_state.evm_memory.Memory,
                'base_addr': None,
                'has_return': has_return
            }
            
            path_results.append((path_condition, path_result))
        
        # Merge all path results using If expressions (Level 2: CFG-level merging)
        merged_result = self._merge_path_results(path_results)
        
        # Create final state (use state from last path as base, but results are merged)
        final_state = state.copy()
        final_state.return_offset = merged_result['offset']
        final_state.return_length = merged_result['length']
        final_state.evm_memory.Memory = merged_result['memory']
        
        return final_state, merged_result
    
    def _to_z3_sequential(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """Fallback: sequential execution without path analysis.
        
        Args:
            state: Initial SMT state
            
        Returns:
            Tuple of (final_state, result_dict)
        """
        # Process all blocks in sequence
        for block in self.blocks:
            # Execute block with TAG path merging (Level 1)
            state, _ = execute_block_with_tag(block, state)
            
            # Check if block ends with a terminating instruction
            if block.operations:
                last_op = block.operations[-1]
                if last_op.kind.upper() in ['STOP', 'RETURN', 'REVERT', 'SELFDESTRUCT']:
                    break
        
        # Extract result
        from z3 import Ne, BitVecVal
        has_return = Ne(state.return_length, BitVecVal(0, 64))
        
        result = {
            'offset': state.return_offset,
            'length': state.return_length,
            'memory': state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return
        }
        
        return state, result
    
    def _merge_path_results(self, path_results: List[Tuple[Any, Dict[str, Any]]]) -> Dict[str, Any]:
        """Merge path results using nested If expressions.
        
        Args:
            path_results: List of (condition, result_dict) tuples
            
        Returns:
            Merged result dictionary
        """
        if not path_results:
            # Default result if no paths
            from z3 import BitVecVal
            return {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': None,  # Will be set by caller
                'base_addr': None,
                'has_return': BoolVal(False)
            }
        
        if len(path_results) == 1:
            # Single path: return its result
            _, result = path_results[0]
            return result
        
        # Build nested If expressions for each field
        # Structure: If(path1_cond, path1_result, If(path2_cond, path2_result, ...))
        def build_nested_if(field_name: str, default_value):
            """Build nested If expression for a field."""
            expr = default_value
            # Build from last to first (right-associative)
            for i in range(len(path_results) - 1, -1, -1):
                condition, result = path_results[i]
                field_value = result.get(field_name, default_value)
                expr = If(condition, field_value, expr)
            return expr
        
        from z3 import BitVecVal, Array
        from state.smt_state import EVMMemoryState
        
        # Get memory array type from first path result
        first_memory = path_results[0][1]['memory']
        if first_memory is None:
            # Create default memory array
            mem_state = EVMMemoryState()
            first_memory = mem_state.Memory
        
        # Merge each field
        merged_offset = build_nested_if('offset', BitVecVal(0, 64))
        merged_length = build_nested_if('length', BitVecVal(0, 64))
        merged_memory = build_nested_if('memory', first_memory)
        merged_has_return = build_nested_if('has_return', BoolVal(False))
        
        return {
            'offset': merged_offset,
            'length': merged_length,
            'memory': merged_memory,
            'base_addr': None,
            'has_return': merged_has_return
        }
    
    def __repr__(self):
        return f"EVMProgram(blocks={len(self.blocks)})"

