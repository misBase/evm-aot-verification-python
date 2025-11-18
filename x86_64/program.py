"""
x86-64 program-level models.

This module provides program-level semantics for x86-64 machine code,
operating on entire programs (sequences of blocks) rather than individual blocks.
"""

from typing import List, Dict, Any, Optional
from z3 import BitVec, BitVecVal, Concat
from .models import X86Block, X86Instruction, Register
from .semantics import X86SemanticsModel
from .disassembler import disassemble_hex


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
    
    def __repr__(self):
        return f"X86Program(blocks={len(self.blocks)}, instructions={len(self.instructions)}, base_addr=0x{self.base_addr:x})"

