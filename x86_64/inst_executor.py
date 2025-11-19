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
        elif mnemonic == 'sub':
            self._execute_sub(state, operands)
        elif mnemonic == 'cmp':
            self._execute_cmp(state, operands)
        elif mnemonic in ['jb', 'jae', 'jmp']:
            # Conditional/unconditional jumps - for now, we continue execution
            # In a full implementation, we would track control flow
            # For verification purposes, we assume we take the success path
            pass
        elif mnemonic == 'ret':
            # RET instruction - for now, we just continue
            # In a full implementation, we would return from function
            pass
        else:
            raise ValueError(f"Unsupported instruction: {mnemonic}")
    
    def _execute_mov(self, state: ExecutionState, operands: dict) -> None:
        """Execute MOV instruction.
        
        Supports:
        - MOV reg, [base+offset]  (load from memory)
        - MOV [base+offset], reg  (store to memory)
        - MOV reg1, reg2          (register to register)
        - MOV reg, immediate      (load immediate)
        - MOV [base+offset], immediate  (store immediate to memory)
        """
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # Load from memory
            mem_val = state.load_memory(offset)
            state.set_register(dest_reg, mem_val)
            
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            base_reg = operands['base_reg']
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # Store to memory
            reg_val = state.get_register(src_reg)
            state.store_memory(offset, reg_val)
            
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate (e.g., MOV BYTE PTR [r13+0xe0], 0xc)
            base_reg = operands['base_reg']
            offset = operands['offset']
            immediate = operands['immediate']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
            
            # Store immediate to memory (sign-extend or zero-extend based on size)
            # For byte operations, we'll store as 64-bit with proper extension
            imm_val = BitVecVal(immediate & 0xFF, 64)  # Byte operation
            state.store_memory(offset, imm_val)
            
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            src_reg = operands['src_reg']
            
            src_val = state.get_register(src_reg)
            state.set_register(dest_reg, src_val)
            
        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            immediate = operands['immediate']
            
            # Sign-extend immediate to 64 bits
            imm_val = BitVecVal(immediate, 64)
            state.set_register(dest_reg, imm_val)
        else:
            raise ValueError(f"Unsupported MOV operand combination: {operands}")
    
    def _execute_add(self, state: ExecutionState, operands: dict) -> None:
        """Execute ADD instruction.
        
        Supports:
        - ADD reg, [base+offset]  (add memory to register)
        - ADD reg, reg            (add register to register)
        """
        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            
            if base_reg not in [Register.R14, Register.R13]:
                raise ValueError(f"Unsupported base register for ADD: {base_reg}")
            
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
            
        elif operands['src_reg']:
            # ADD reg, reg
            src_reg = operands['src_reg']
            src_val = state.get_register(src_reg)
            
            # Perform addition (64-bit with carry generation)
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            src_ext = Concat(BitVecVal(0, 1), src_val)
            sum_ext = reg_ext + src_ext
            
            # Extract result and carry
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            # Update register
            state.set_register(dest_reg, result)
            
            # Update carry flag
            state.set_flag('CF', carry_out)
        else:
            raise ValueError(f"Unsupported ADD operand combination: {operands}")
    
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
    
    def _execute_sub(self, state: ExecutionState, operands: dict) -> None:
        """Execute SUB instruction.
        
        Supports:
        - SUB reg, immediate  (subtract immediate from register)
        """
        if not operands['dest_reg']:
            raise ValueError(f"SUB instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # SUB reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            state.set_register(dest_reg, result)
        else:
            raise ValueError(f"Unsupported SUB operand combination: {operands}")
    
    def _execute_cmp(self, state: ExecutionState, operands: dict) -> None:
        """Execute CMP instruction.
        
        CMP sets flags based on comparison but doesn't modify operands.
        Supports:
        - CMP reg, immediate  (compare register with immediate)
        """
        if not operands['dest_reg']:
            raise ValueError(f"CMP instruction must have register operand: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # CMP reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            # Compute result for flag setting
            result = reg_val - imm_val
            
            # Set flags based on comparison
            # CF (carry flag): set if unsigned subtraction would borrow
            # For now, we'll compute it symbolically
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            diff_ext = reg_ext - imm_ext
            cf = Extract(64, 64, diff_ext)
            state.set_flag('CF', cf)
            
            # ZF (zero flag): set if result is zero
            # reg_val == imm_val returns a BoolRef, convert to 1-bit BitVec
            zf_bool = (reg_val == imm_val)
            # Convert BoolRef to 1-bit BitVec: IfThenElse(condition, 1, 0)
            from z3 import If
            zf = If(zf_bool, BitVecVal(1, 1), BitVecVal(0, 1))
            state.set_flag('ZF', zf)
        else:
            raise ValueError(f"Unsupported CMP operand combination: {operands}")
    
    def execute_sequence(self, state: ExecutionState, instructions: List[X86Instruction]) -> None:
        """Execute a sequence of instructions.
        
        Args:
            state: Initial execution state (will be modified)
            instructions: List of instructions to execute
        """
        for instruction in instructions:
            self.execute_instruction(state, instruction)

