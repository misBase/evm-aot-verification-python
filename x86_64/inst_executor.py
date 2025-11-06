"""
x86-64 instruction executor.

This module provides InstructionExecutor class to execute instruction sequences
using the instruction semantics and execution state.
"""

from typing import List
from z3 import BitVec, BitVecVal, Concat, Extract
from .models import X86Instruction, Register
from .execution_state import ExecutionState
from .disassembler import parse_operands


class InstructionExecutor:
    """Executes x86-64 instruction sequences using semantic modeling."""
    
    def __init__(self):
        """Initialize the instruction executor."""
        pass
    
    def execute_instruction(self, state: ExecutionState, instruction: X86Instruction) -> None:
        """Execute a single instruction, updating the execution state.
        
        Args:
            state: Current execution state
            instruction: Instruction to execute
        """
        mnemonic = instruction.mnemonic.lower()
        op_str = instruction.op_str
        
        # Parse operands
        operands = parse_operands(op_str)
        
        if mnemonic == 'mov':
            self._execute_mov(state, operands)
        elif mnemonic == 'add':
            self._execute_add(state, operands)
        elif mnemonic == 'adc':
            self._execute_adc(state, operands)
        else:
            raise ValueError(f"Unsupported instruction: {mnemonic}")
    
    def _execute_mov(self, state: ExecutionState, operands: dict) -> None:
        """Execute MOV instruction.
        
        Supports:
        - MOV reg, [base+offset]  (load from memory)
        - MOV [base+offset], reg  (store to memory)
        - MOV reg1, reg2          (register to register)
        """
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            if base_reg != Register.R14:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # Load from memory
            mem_val = state.load_memory(offset)
            state.set_register(dest_reg, mem_val)
            
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            base_reg = operands['base_reg']
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            if base_reg != Register.R14:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # Store to memory
            reg_val = state.get_register(src_reg)
            state.store_memory(offset, reg_val)
            
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            src_reg = operands['src_reg']
            
            src_val = state.get_register(src_reg)
            state.set_register(dest_reg, src_val)
        else:
            raise ValueError(f"Unsupported MOV operand combination: {operands}")
    
    def _execute_add(self, state: ExecutionState, operands: dict) -> None:
        """Execute ADD instruction.
        
        Supports:
        - ADD reg, [base+offset]  (add memory to register)
        """
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"ADD instruction must have register destination and memory source: {operands}")
        
        dest_reg = operands['dest_reg']
        base_reg = operands['base_reg']
        offset = operands['offset']
        
        if base_reg != Register.R14:
            raise ValueError(f"Unsupported base register for ADD: {base_reg}")
        
        # Get current register value
        reg_val = state.get_register(dest_reg)
        
        # Load memory value
        mem_val = state.load_memory(offset)
        
        # Perform addition (64-bit with carry generation)
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        sum_ext = reg_ext + mem_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        # Update register
        state.set_register(dest_reg, result)
        
        # Update carry flag
        state.set_flag('CF', carry_out)
    
    def _execute_adc(self, state: ExecutionState, operands: dict) -> None:
        """Execute ADC (add with carry) instruction.
        
        Supports:
        - ADC reg, [base+offset]  (add memory and carry to register)
        """
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"ADC instruction must have register destination and memory source: {operands}")
        
        dest_reg = operands['dest_reg']
        base_reg = operands['base_reg']
        offset = operands['offset']
        
        if base_reg != Register.R14:
            raise ValueError(f"Unsupported base register for ADC: {base_reg}")
        
        # Get current register value
        reg_val = state.get_register(dest_reg)
        
        # Load memory value
        mem_val = state.load_memory(offset)
        
        # Get carry flag
        carry_in = state.get_flag('CF')
        
        # Perform addition with carry (64-bit with carry generation)
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + mem_ext + carry_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        # Update register
        state.set_register(dest_reg, result)
        
        # Update carry flag
        state.set_flag('CF', carry_out)
    
    def execute_sequence(self, state: ExecutionState, instructions: List[X86Instruction]) -> None:
        """Execute a sequence of instructions.
        
        Args:
            state: Initial execution state (will be modified)
            instructions: List of instructions to execute
        """
        for instruction in instructions:
            self.execute_instruction(state, instruction)

