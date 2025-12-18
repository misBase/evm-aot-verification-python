"""
EVM IR program-level models.

This module provides program-level semantics for EVM IR, operating on
entire programs (sequences of blocks) rather than individual blocks.
"""

from typing import List, Dict, Any, Optional, Tuple, Set
from z3 import BitVec, BitVecVal, Solver, If, BoolVal, And
from .models import EVMBlock
from .semantics import EVMIRSemantics, execute_block_with_tag
from .json_parser import CompilerEVMResult
from .cfg import build_ir_cfg, IRCFG
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
        """Build Z3 formula for the entire program using CFG-based symbolic execution.
        
        This method uses symbolic execution instead of path enumeration:
        - Level 1: Execute each block with TAG path merging (3 paths per block)
        - Level 2: Execute CFG-based symbolic execution, merging branches with If expressions
        
        Args:
            state: Initial SMT state with inputs already prepared
        
        Returns:
            Tuple of (final_state, result_dict) where:
            - final_state: Final SMT state after program execution (merged from all paths)
            - result_dict: Dictionary with merged return values (offset, length, memory, has_return)
        """
        # Build CFG
        cfg = build_ir_cfg(self.blocks)
        
        # Validate loops (detect and reject unsupported loops)
        try:
            cfg.validate_loops()
        except Exception as e:
            # Re-raise the exception (could be UnsupportedLoopError)
            raise e
        
        # Get entry and terminal blocks
        entry = cfg.get_entry_block()
        terminals = cfg.get_terminal_blocks()
        
        # Execute symbolically: from entry, merge branches with If expressions
        merged_state = self._execute_symbolic_with_cfg(
            entry, state, cfg, terminals
        )
        
        # Extract result from merged state
        from z3 import BitVecVal
        has_return = merged_state.return_length != BitVecVal(0, 64)
        
        result = {
            'offset': merged_state.return_offset,
            'length': merged_state.return_length,
            'memory': merged_state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return
        }
        
        return merged_state, result
    
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
        from z3 import BitVecVal
        has_return = state.return_length != BitVecVal(0, 64)
        
        result = {
            'offset': state.return_offset,
            'length': state.return_length,
            'memory': state.evm_memory.Memory,
            'base_addr': None,
            'has_return': has_return
        }
        
        return state, result
    
    def _execute_symbolic_with_cfg(
        self, 
        start_block: EVMBlock, 
        state: SMTState, 
        cfg: IRCFG,
        terminals: List[EVMBlock],
        visited: Optional[Set[int]] = None
    ) -> SMTState:
        """Based on CFG symbolic execution: merge branches with If expressions when encountering branches.
        
        This is not path enumeration, but:
        - When encountering conditional branches, recursively execute both branches, then merge with If expressions
        - Use CFG's successors information to guide execution direction
        
        Args:
            start_block: Starting block
            state: Current state
            cfg: Control flow graph
            terminals: List of terminal blocks
            visited: Set of visited block PCs (for loop detection)
        
        Returns:
            Merged state (contains information from all possible paths via If expressions)
        """
        from z3 import BoolVal
        
        if visited is None:
            visited = set()
        
        # Detect loops: if block is already in visited, we've detected a loop
        if start_block.pc in visited:
            # This is a loop! For now, we'll raise an error
            # In the future, we can handle static bounded loops by unrolling
            raise ValueError(
                f"Loop detected during execution at block PC={start_block.pc}. "
                "Loop detection should be done before symbolic execution via validate_loops()."
            )
        
        visited.add(start_block.pc)
        
        # Execute current block (Level 1: TAG path merging)
        executed_state, _ = execute_block_with_tag(start_block, state)
        
        # Check if this is a terminal block
        if start_block in terminals:
            # Reached terminal block: return current state (already contains all path information)
            return executed_state
        
        # Get successor blocks
        successors = cfg.get_successors(start_block)
        
        if len(successors) == 0:
            # No successors: return current state
            return executed_state
        
        elif len(successors) == 1:
            # Unconditional jump or sequential execution: continue to next block
            next_block = successors[0]
            return self._execute_symbolic_with_cfg(
                next_block, executed_state, cfg, terminals, visited.copy()
            )
        
        elif len(successors) == 2:
            # Conditional jump (JUMPI): recursively execute both branches, then merge with If
            # Assume successors[0] is jump target, successors[1] is fall-through
            jump_target = successors[0]
            fallthrough_target = successors[1]
            
            # Extract condition from JUMPI instruction
            # Note: JUMPI doesn't modify state, so condition should still be at stack top
            # after block execution
            condition = self._extract_jumpi_condition(start_block, executed_state)
            
            # IMPORTANT: Each branch must start from an independent copy of the state
            # This ensures that modifications in one branch don't affect the other
            # Even though Z3 expressions are symbolic, we need separate state objects
            # to ensure proper merging with If expressions
            jump_state_input = executed_state.copy()
            fallthrough_state_input = executed_state.copy()
            
            # Recursively execute both branches, each returns a merged state
            jump_state = self._execute_symbolic_with_cfg(
                jump_target, jump_state_input, cfg, terminals, visited.copy()
            )
            
            fallthrough_state = self._execute_symbolic_with_cfg(
                fallthrough_target, fallthrough_state_input, cfg, terminals, visited.copy()
            )
            
            # Merge two branch states with If expression, return a merged state
            merged_state = self._merge_states_with_if(
                condition, jump_state, fallthrough_state
            )
            
            return merged_state
        
        else:
            # Multiple successors (shouldn't happen)
            raise ValueError(f"Block {start_block.pc} has {len(successors)} successors")
    
    def _extract_jumpi_condition(self, block: EVMBlock, state: SMTState):
        """Extract condition from JUMPI instruction.
        
        JUMPI pops two values from stack: condition (top) and target address (second).
        Condition is at stack top, target address is at second from top.
        
        Args:
            block: Block containing JUMPI instruction
            state: State before JUMPI execution (condition should be at stack top)
        
        Returns:
            BoolRef: Condition expression (non-zero = True, zero = False)
        """
        from z3 import BitVecVal
        
        # Find JUMPI instruction in block
        # JUMPI should be the last operation in the block
        if not block.operations:
            return BoolVal(True)
        
        last_op = block.operations[-1]
        if last_op.kind.upper() != "JUMPI":
            # Not a JUMPI block, return True (unconditional)
            return BoolVal(True)
        
        # Before JUMPI executes, condition should be at stack top
        # Get condition value from stack top
        condition_value = state.evm_stack.peek(0)  # Stack top value
        
        # Convert condition value to BoolRef: non-zero = True, zero = False
        zero = BitVecVal(0, 256)
        condition = condition_value != zero
        
        return condition
    
    def _merge_states_with_if(self, condition, state1: SMTState, state2: SMTState) -> SMTState:
        """Merge two states with If expression, return a merged state.
        
        Args:
            condition: BoolRef condition (True -> use state1, False -> use state2)
            state1: First state (when condition is True)
            state2: Second state (when condition is False)
        
        Returns:
            Merged state with all fields merged using If expressions
        """
        from z3 import If
        
        merged = state1.copy()
        
        # Merge simple fields
        merged.return_offset = If(condition, state1.return_offset, state2.return_offset)
        merged.return_length = If(condition, state1.return_length, state2.return_length)
        
        # Merge Array types (Memory and Stack)
        merged.evm_memory.Memory = If(condition, state1.evm_memory.Memory, state2.evm_memory.Memory)
        merged.evm_memory.MSize = If(condition, state1.evm_memory.MSize, state2.evm_memory.MSize)
        
        # Stack merging: need to merge Stack array and SP pointer
        merged.evm_stack.Stack = If(condition, state1.evm_stack.Stack, state2.evm_stack.Stack)
        merged.evm_stack.SP = If(condition, state1.evm_stack.SP, state2.evm_stack.SP)
        
        # Note: Other state fields (x86_memory, x86_registers) are not used in EVM execution
        # but we should merge them for completeness
        merged.x86_memory.Memory = If(condition, state1.x86_memory.Memory, state2.x86_memory.Memory)
        
        return merged
    
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

