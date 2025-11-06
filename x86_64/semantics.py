"""
x86-64 instruction semantic modeling.

This module provides semantic modeling for x86-64 instructions using Z3.
"""

from z3 import BitVec, BitVecVal, Concat, Extract
from typing import List, Dict, Optional, Any, Tuple
from .models import X86Block, X86Instruction, Register
from .execution_state import ExecutionState
from .inst_executor import InstructionExecutor
from .disassembler import disassemble_hex
from common.uint256 import Uint256


class X86InstructionSemantics:
    """Semantic modeling for individual x86-64 instructions."""
    
    def mov_reg_mem_semantics(self, dest_reg: Register, base_reg: Register, 
                              offset: int, mem_vars: Dict[int, BitVec]) -> BitVec:
        """Model MOV reg, [base+offset] instruction.
        
        Args:
            dest_reg: Destination register
            base_reg: Base register (should be R14 for stack access)
            offset: Memory offset
            mem_vars: Dictionary mapping offsets to symbolic memory variables
            
        Returns:
            Value loaded into destination register
        """
        if base_reg == Register.R14:
            # Loading from EVM stack memory
            if offset not in mem_vars:
                # Create symbolic variable if not present
                mem_vars[offset] = BitVec(f"mem_{offset:+d}", 64)
            return mem_vars[offset]
        else:
            raise ValueError(f"Unsupported base register: {base_reg}")
    
    def add_reg_mem_semantics(self, dest_reg: Register, base_reg: Register,
                              offset: int, mem_vars: Dict[int, BitVec],
                              carry_in: Optional[BitVec] = None) -> Tuple[BitVec, BitVec]:
        """Model ADD/ADC reg, [base+offset] instruction.
        
        Args:
            dest_reg: Destination register
            base_reg: Base register
            offset: Memory offset
            mem_vars: Dictionary mapping offsets to symbolic memory variables
            carry_in: Optional carry input (for ADC)
            
        Returns:
            Tuple of (result, carry_out) where both are 64-bit BitVecs
        """
        # Get current register value (assume it's in mem_vars with special key)
        # For simplicity, we'll track it separately
        reg_val_key = f"reg_{dest_reg.value}"
        if reg_val_key not in mem_vars:
            # Initialize register value
            mem_vars[reg_val_key] = BitVec(f"{dest_reg.value}_init", 64)
        
        reg_val = mem_vars[reg_val_key]
        mem_val = self.mov_reg_mem_semantics(dest_reg, base_reg, offset, mem_vars)
        
        # Perform addition with optional carry
        if carry_in is not None:
            # ADC: add with carry
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            carry_ext = Concat(BitVecVal(0, 64), carry_in)
            sum_ext = reg_ext + mem_ext + carry_ext
        else:
            # ADD: simple addition
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            mem_ext = Concat(BitVecVal(0, 1), mem_val)
            sum_ext = reg_ext + mem_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        # Update register value
        mem_vars[reg_val_key] = result
        
        return result, carry_out
    
    def mov_mem_reg_semantics(self, base_reg: Register, offset: int,
                              src_reg: Register, mem_vars: Dict[int, BitVec]) -> None:
        """Model MOV [base+offset], reg instruction.
        
        Args:
            base_reg: Base register
            offset: Memory offset
            src_reg: Source register
            mem_vars: Dictionary mapping offsets to symbolic memory variables
        """
        if base_reg == Register.R14:
            # Storing to EVM stack memory
            reg_val_key = f"reg_{src_reg.value}"
            if reg_val_key not in mem_vars:
                mem_vars[reg_val_key] = BitVec(f"{src_reg.value}_init", 64)
            mem_vars[offset] = mem_vars[reg_val_key]
        else:
            raise ValueError(f"Unsupported base register: {base_reg}")


class X86SemanticsModel:
    """Semantic modeling for x86-64 instruction sequences."""
    
    def __init__(self):
        """Initialize the x86 semantics model."""
        self.instr_semantics = X86InstructionSemantics()
        self.executor = InstructionExecutor()
    
    def execute_instruction_sequence(self, 
                                    instructions: List[X86Instruction],
                                    initial_memory: Dict[int, BitVec],
                                    result_registers: Optional[List[Register]] = None) -> BitVec:
        """Execute a sequence of instructions and extract the result.
        
        This method creates an execution state, executes the instruction sequence,
        and extracts the final result from the register state.
        
        Args:
            instructions: List of X86Instruction objects to execute
            initial_memory: Initial memory state (dict mapping offsets to BitVec values)
            result_registers: List of registers to extract result from (in order from high to low).
                            If None, defaults to [RBX, RDX, RCX, RAX] for ADD sequence.
                            Each register should be 64-bit, and they will be concatenated
                            to form a 256-bit result.
            
        Returns:
            Logical formula representing the 256-bit result as a BitVec
        """
        # Create execution state with initial memory
        state = ExecutionState(initial_memory=initial_memory)
        
        # Execute instruction sequence
        self.executor.execute_sequence(state, instructions)
        
        # Extract result from registers
        if result_registers is None:
            # Default for ADD sequence: result = [rbx, rdx, rcx, rax]
            result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
        
        # Get register values and combine into 256-bit result
        reg_values = [state.get_register(reg) for reg in result_registers]
        
        # Combine into 256-bit result (high to low)
        result = Concat(*reg_values)
        
        return result
    
    def build_instructions_from_hex(self, hex_str: str, base_addr: int = 0) -> List[X86Instruction]:
        """Build instruction sequence from hex-encoded machine code.
        
        This is a generic method that disassembles hex machine code into
        X86Instruction objects.
        
        Args:
            hex_str: Hex string containing machine code (with or without spaces/0x prefix)
            base_addr: Base address for instructions (default: 0)
            
        Returns:
            List of X86Instruction objects
        """
        return disassemble_hex(hex_str, base_addr=base_addr)
    
    def build_sequence_semantics_from_hex(self,
                                         hex_sequence: str,
                                         mem_vars: Dict[int, BitVec],
                                         base_addr: int = 0,
                                         result_registers: Optional[List[Register]] = None) -> BitVec:
        """Build logical formula for x86 instruction sequence from hex machine code.
        
        This is a generic method that disassembles hex machine code and executes
        the instruction sequence to build semantic formulas.
        
        Args:
            hex_sequence: Hex string containing the instruction sequence
            mem_vars: Dictionary mapping stack offsets to symbolic memory variables
            base_addr: Base address for the instruction sequence (default: 0)
            result_registers: List of registers to extract result from (in order from high to low).
                            If None, defaults to [RBX, RDX, RCX, RAX] for 256-bit results.
                            Each register should be 64-bit, and they will be concatenated
                            to form a 256-bit result.
                                    
        Returns:
            Logical formula representing the result as a BitVec
        """
        # Build the instruction sequence from hex
        instructions = self.build_instructions_from_hex(hex_sequence, base_addr=base_addr)
        
        # Execute the sequence and extract result from registers
        return self.execute_instruction_sequence(
            instructions, 
            mem_vars,
            result_registers=result_registers
        )
    
    def build_sequence_from_limbs(self,
                                 hex_sequence: str,
                                 val1_limbs: List[BitVec],
                                 val2_limbs: List[BitVec],
                                 base_addr: int = 0,
                                 result_registers: Optional[List[Register]] = None) -> BitVec:
        """Build instruction sequence semantics from limb lists.
        
        Convenience method that creates memory variable mapping from limbs and
        executes the instruction sequence from hex machine code.
        
        Args:
            hex_sequence: Hex string containing the instruction sequence
            val1_limbs: [z0, z1, z2, z3] for first operand (each 64-bit)
            val2_limbs: [z0, z1, z2, z3] for second operand (each 64-bit)
            base_addr: Base address for the instruction sequence (default: 0)
            result_registers: List of registers to extract result from (in order from high to low).
                            If None, defaults to [RBX, RDX, RCX, RAX] for 256-bit results.
            
        Returns:
            Logical formula representing the 256-bit result
        """
        if len(val1_limbs) != 4 or len(val2_limbs) != 4:
            raise ValueError("Expected 4 limbs for 256-bit value")
        
        mem_vars = {
            -0x40: val1_limbs[0],  # val1.z0
            -0x38: val1_limbs[1],  # val1.z1
            -0x30: val1_limbs[2],  # val1.z2
            -0x28: val1_limbs[3],  # val1.z3
            -0x20: val2_limbs[0],  # val2.z0
            -0x18: val2_limbs[1],  # val2.z1
            -0x10: val2_limbs[2],  # val2.z2
            -0x08: val2_limbs[3],  # val2.z3
        }
        
        return self.build_sequence_semantics_from_hex(
            hex_sequence, 
            mem_vars, 
            base_addr=base_addr,
            result_registers=result_registers
        )
    
    def build_block_semantics(self, 
                             block: X86Block, 
                             mem_vars: Dict[int, BitVec],
                             hex_sequence: Optional[str] = None,
                             result_registers: Optional[List[Register]] = None) -> Dict[str, Any]:
        """Build semantic formula for an x86 block.
        
        Args:
            block: x86 block to model
            mem_vars: Initial memory state (dictionary mapping offsets to values)
            hex_sequence: Optional hex string containing the instruction sequence.
                         If None, will try to extract from block.instructions.
            result_registers: List of registers to extract result from.
            
        Returns:
            Dictionary containing:
            - output_memory: Final memory state
            - semantic_formula: Overall semantic formula for the block
        """
        # If hex_sequence is provided, use it
        if hex_sequence:
            result = self.build_sequence_semantics_from_hex(
                hex_sequence,
                mem_vars,
                base_addr=block.start_addr,
                result_registers=result_registers
            )
            return {
                'output_memory': mem_vars,
                'semantic_formula': result,
                'output_count': 1
            }
        
        # Otherwise, execute instructions from the block
        # This is a fallback for when we have X86Instruction objects
        if len(block.instructions) > 0:
            state = ExecutionState(initial_memory=mem_vars)
            self.executor.execute_sequence(state, block.instructions)
            
            # Extract result from default registers if not specified
            if result_registers is None:
                result_registers = [Register.RBX, Register.RDX, Register.RCX, Register.RAX]
            
            reg_values = [state.get_register(reg) for reg in result_registers]
            result = Concat(*reg_values)
            
            return {
                'output_memory': state.memory,
                'semantic_formula': result,
                'output_count': 1
            }
        
        # Default: return identity
        return {
            'output_memory': mem_vars,
            'semantic_formula': BitVecVal(0, 256),
            'output_count': 0
        }

