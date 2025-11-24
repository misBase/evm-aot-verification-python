"""
x86-64 program-level models.

This module provides program-level semantics for x86-64 machine code,
operating on entire programs (sequences of blocks) rather than individual blocks.
"""

from typing import List, Dict, Any, Optional, Tuple
from z3 import BitVec, BitVecVal, Concat, If, BoolVal, And, Not
from .models import X86Block, X86Instruction, Register
from .semantics import X86SemanticsModel
from .disassembler import disassemble_hex
from .cfg import build_x86_cfg, identify_basic_blocks
from ir.smt_state import SMTState


class X86Program:
    """Represents a complete x86-64 program with multiple blocks.
    
    This provides program-level verification capabilities for entire
    compiled machine code sequences.
    """
    
    def __init__(self, 
                 blocks: Optional[List[X86Block]] = None,
                 hex_sequence: Optional[str] = None,
                 base_addr: int = 0):
        """Initialize the x86 program.
        
        Args:
            blocks: List of pre-parsed X86Block objects (optional)
            hex_sequence: Hex-encoded machine code string (optional)
            base_addr: Base address for the program (default: 0)
        """
        self.blocks = blocks or []
        self.hex_sequence = hex_sequence
        self.base_addr = base_addr
        self.semantics = X86SemanticsModel()
        
        # If hex_sequence is provided but no blocks, disassemble it
        if hex_sequence and not blocks:
            self.instructions = disassemble_hex(hex_sequence, base_addr=base_addr)
        else:
            self.instructions = []
            for block in self.blocks:
                self.instructions.extend(block.instructions)
        
        # Build a block lookup table by start address
        self.blocks_by_addr: Dict[int, X86Block] = {}
        for block in self.blocks:
            self.blocks_by_addr[block.start_addr] = block
    
    @classmethod
    def from_hex(cls, hex_sequence: str, base_addr: int = 0) -> 'X86Program':
        """Create an X86Program from hex-encoded machine code.
        
        Args:
            hex_sequence: Hex-encoded machine code string
            base_addr: Base address for the program
            
        Returns:
            X86Program instance
        """
        return cls(hex_sequence=hex_sequence, base_addr=base_addr)
    
    @classmethod
    def from_blocks(cls, blocks: List[X86Block]) -> 'X86Program':
        """Create an X86Program from a list of blocks.
        
        Args:
            blocks: List of X86Block objects
            
        Returns:
            X86Program instance
        """
        return cls(blocks=blocks)
    
    def get_entrypoint(self) -> Optional[X86Block]:
        """Get the program entrypoint (first block).
        
        Returns:
            The first block in the program, or None if no blocks
        """
        if len(self.blocks) == 0:
            return None
        return self.blocks[0]
    
    def get_block_by_addr(self, addr: int) -> Optional[X86Block]:
        """Get a block by its start address.
        
        Args:
            addr: Block start address
            
        Returns:
            The block at the given address, or None if not found
        """
        return self.blocks_by_addr.get(addr)
    
    def build_program_semantics(self, initial_memory: Dict[int, BitVec]) -> Dict[str, Any]:
        """Build semantic formula for the entire program.
        
        This executes all instructions in sequence, building up a complete
        semantic model of the program's behavior.
        
        For now, we support straight-line execution (no branches).
        Future versions will support control flow analysis.
        
        Args:
            initial_memory: Initial memory state (dict mapping offsets to BitVec values)
            
        Returns:
            Dictionary containing:
            - output_memory: Final memory state
            - semantic_formula: Overall semantic formula for the program
            - executed_instructions: List of instructions that were executed
        """
        from .execution_state import ExecutionState
        
        # Create execution state
        state = ExecutionState(initial_memory=initial_memory.copy())
        
        # Execute all instructions
        if self.instructions:
            self.semantics.executor.execute_sequence(state, self.instructions)
        else:
            # Execute instructions from blocks
            for block in self.blocks:
                self.semantics.executor.execute_sequence(state, block.instructions)
        
        # Extract result from default registers (for 256-bit results)
        result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
        reg_values = [state.get_register(reg) for reg in result_registers]
        semantic_formula = Concat(*reg_values)
        
        return {
            'output_memory': state.memory,
            'semantic_formula': semantic_formula,
            'executed_instructions': self.instructions if self.instructions else 
                                    [insn for block in self.blocks for insn in block.instructions],
            'output_count': 1
        }
    
    def build_program_semantics_from_limbs(self,
                                          val1_limbs: List[BitVec],
                                          val2_limbs: List[BitVec],
                                          result_registers: Optional[List[Register]] = None) -> Dict[str, Any]:
        """Build program semantics with inputs as limb lists.
        
        Convenience method that creates memory variable mapping from limbs and
        executes the entire program.
        
        Args:
            val1_limbs: [z0, z1, z2, z3] for first operand (each 64-bit)
            val2_limbs: [z0, z1, z2, z3] for second operand (each 64-bit)
            result_registers: List of registers to extract result from (in order from high to low).
                            If None, defaults to [RBX, RDX, RCX, RAX] for 256-bit results.
            
        Returns:
            Dictionary containing semantic formula and metadata
        """
        if len(val1_limbs) != 4 or len(val2_limbs) != 4:
            raise ValueError("Expected 4 limbs for 256-bit value")
        
        initial_memory = {
            -0x40: val1_limbs[0],  # val1.z0
            -0x38: val1_limbs[1],  # val1.z1
            -0x30: val1_limbs[2],  # val1.z2
            -0x28: val1_limbs[3],  # val1.z3
            -0x20: val2_limbs[0],  # val2.z0
            -0x18: val2_limbs[1],  # val2.z1
            -0x10: val2_limbs[2],  # val2.z2
            -0x08: val2_limbs[3],  # val2.z3
        }
        
        if result_registers is None:
            result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
        
        # Build semantics for the entire program
        result = self.build_program_semantics(initial_memory)
        
        # Re-extract with specified registers if different
        if result_registers != [Register.RBX, Register.RDX, Register.RCX, Register.RAX]:
            from .execution_state import ExecutionState
            state = ExecutionState(initial_memory=initial_memory.copy())
            
            if self.instructions:
                self.semantics.executor.execute_sequence(state, self.instructions)
            else:
                for block in self.blocks:
                    self.semantics.executor.execute_sequence(state, block.instructions)
            
            reg_values = [state.get_register(reg) for reg in result_registers]
            result['semantic_formula'] = Concat(*reg_values)
        
        return result
    
    def to_z3(self, state: SMTState) -> Tuple[SMTState, Dict[str, Any]]:
        """Build Z3 formula for the entire program using path-aware execution.
        
        This method identifies all execution paths, executes each path symbolically,
        and merges results using Z3 If expressions.
        
        Args:
            state: Initial SMT state with inputs already prepared
        
        Returns:
            Tuple of (final_state, result_dict) where:
            - final_state: Final SMT state after program execution
            - result_dict: Dictionary with merged return values (offset, length, memory, base_addr, has_return)
        """
        # Get instructions to execute
        instructions_to_execute = self.instructions if self.instructions else []
        if not instructions_to_execute:
            # Extract from blocks
            for block in self.blocks:
                instructions_to_execute.extend(block.instructions)
        
        if not instructions_to_execute:
            # No instructions: return default result
            from z3 import BitVecVal, Ne
            r15_value = state.x86_registers.get_register(Register.R15)
            result = {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': state.x86_memory.Memory,
                'base_addr': r15_value,
                'has_return': BoolVal(False)
            }
            return state, result
        
        # Build CFG from instructions
        cfg = build_x86_cfg(instructions_to_execute)
        
        # Find all paths from entry to return blocks
        entry = cfg.get_entry_block()
        terminals = cfg.get_return_blocks()
        paths = cfg.find_all_paths(entry, terminals)
        
        if not paths:
            # Fallback: if no paths found, use simple sequential execution
            return self._to_z3_sequential(state, instructions_to_execute)
        
        # Execute each path and collect results
        path_results = []
        for path_blocks, path_condition in paths:
            # Execute path
            path_state = state.copy()
            
            # Execute all instructions in the path (in order)
            for block in path_blocks:
                for insn in block.instructions:
                    path_state = insn.to_z3(path_state)
            
            # Extract result for this path
            from z3 import Ne, BitVecVal
            r15_value = path_state.x86_registers.get_register(Register.R15)
            has_return = Ne(path_state.return_length, BitVecVal(0, 64))
            
            path_result = {
                'offset': path_state.return_offset,
                'length': path_state.return_length,
                'memory': path_state.x86_memory.Memory,
                'base_addr': r15_value,
                'has_return': has_return
            }
            
            path_results.append((path_condition, path_result))
        
        # Merge all path results using If expressions
        merged_result = self._merge_path_results(path_results)
        
        # Create final state (use state from last path as base, but results are merged)
        final_state = state.copy()
        final_state.return_offset = merged_result['offset']
        final_state.return_length = merged_result['length']
        final_state.x86_memory.Memory = merged_result['memory']
        # Update R15 if needed (though it's usually constant)
        
        return final_state, merged_result
    
    def _to_z3_sequential(self, state: SMTState, instructions: List[X86Instruction]) -> Tuple[SMTState, Dict[str, Any]]:
        """Fallback: sequential execution without path analysis.
        
        Args:
            state: Initial SMT state
            instructions: Instructions to execute
            
        Returns:
            Tuple of (final_state, result_dict)
        """
        # Process each instruction
        for insn in instructions:
            state = insn.to_z3(state)
        
        # Extract result
        from z3 import Ne, BitVecVal
        r15_value = state.x86_registers.get_register(Register.R15)
        has_return = Ne(state.return_length, BitVecVal(0, 64))
        
        result = {
            'offset': state.return_offset,
            'length': state.return_length,
            'memory': state.x86_memory.Memory,
            'base_addr': r15_value,
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
            from .models import Register
            r15_default = BitVecVal(0, 64)  # Default R15 value
            return {
                'offset': BitVecVal(0, 64),
                'length': BitVecVal(0, 64),
                'memory': None,  # Will be set by caller
                'base_addr': r15_default,
                'has_return': BoolVal(False)
            }
        
        if len(path_results) == 1:
            # Single path: return its result
            _, result = path_results[0]
            return result
        
        # Build nested If expressions for each field
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
        from ir.smt_state import X86MemoryState
        from .models import Register
        
        # Get memory array type from first path result
        first_memory = path_results[0][1]['memory']
        if first_memory is None:
            # Create default memory array
            mem_state = X86MemoryState()
            first_memory = mem_state.Memory
        
        # Get default base_addr
        first_base_addr = path_results[0][1].get('base_addr', BitVecVal(0, 64))
        
        # Merge each field
        merged_offset = build_nested_if('offset', BitVecVal(0, 64))
        merged_length = build_nested_if('length', BitVecVal(0, 64))
        merged_memory = build_nested_if('memory', first_memory)
        merged_base_addr = build_nested_if('base_addr', first_base_addr)
        merged_has_return = build_nested_if('has_return', BoolVal(False))
        
        return {
            'offset': merged_offset,
            'length': merged_length,
            'memory': merged_memory,
            'base_addr': merged_base_addr,
            'has_return': merged_has_return
        }
    
    def __repr__(self):
        return f"X86Program(blocks={len(self.blocks)}, instructions={len(self.instructions)}, base_addr=0x{self.base_addr:x})"

