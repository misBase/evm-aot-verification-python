"""
x86-64 instruction semantic modeling.

This module provides semantic modeling for x86-64 instructions using Z3.
"""

from z3 import BitVec, BitVecVal, Concat, Extract, If
from typing import List, Dict, Optional, Any, Tuple
from .models import X86Block, X86Instruction, Register
from .execution_state import ExecutionState
from .inst_executor import InstructionExecutor
from .disassembler import disassemble_hex, parse_operands
from common.uint256 import Uint256
from ir.smt_state import SMTState

# Constants for RETURN instruction
EVM_NATIVE_CALL_STATUS_CODE_RETURNED = 0  # evmNativeCallStatusCodeReturned = iota
EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET = 200  # 168 + 8 + 8 + 8 + 32
AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE = Register.R13  # Pointer to callEngine instance
AMD64_RESERVED_REGISTER_FOR_MEMORY = Register.R15  # Pointer to EVM memory (memoryElement0Address)


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


def x86_instruction_to_z3(insn: X86Instruction, state: SMTState) -> SMTState:
    """Convert x86-64 instruction to Z3 formula, updating state.
    
    This is the Alive2-style direct formula construction method.
    Each instruction directly builds Z3 expressions without execution simulation.
    
    Args:
        insn: x86-64 instruction to convert
        state: Current SMT state (will be modified)
        
    Returns:
        Updated SMT state
    """
    mnemonic = insn.mnemonic.lower()
    operands = parse_operands(insn.op_str)
    
    if mnemonic == 'mov':
        # MOV: move value from source to destination
        if operands['is_memory'] and operands['dest_reg']:
            # MOV reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            dest_reg = operands['dest_reg']
            
            if base_reg in [Register.R14, Register.R13]:
                # Load from x86 memory (R14 = stack base, R13 = callEngine pointer)
                # offset can be int (concrete) or BitVec (symbolic)
                # If there's an index register, compute: base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    # Support [base+index] addressing mode
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    # Convert concrete offset to BitVec if needed
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                mem_val = state.x86_memory.load_limb(memory_offset)
                state.x86_registers.set_register(dest_reg, mem_val)
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        elif operands['is_memory'] and operands['src_reg']:
            # MOV [base+offset], reg
            base_reg = operands['base_reg']
            offset = operands['offset']
            src_reg = operands['src_reg']
            
            if base_reg in [Register.R14, Register.R13]:
                # Store to x86 memory (R14 = stack base, R13 = callEngine pointer)
                # offset can be int (concrete) or BitVec (symbolic)
                # If there's an index register, compute: base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    # Support [base+index] addressing mode
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    # Convert concrete offset to BitVec if needed
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                reg_val = state.x86_registers.get_register(src_reg)
                new_memory_state = state.x86_memory.store_limb(memory_offset, reg_val)
                state.x86_memory = new_memory_state
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        elif operands['dest_reg'] and operands['src_reg']:
            # MOV reg1, reg2
            dest_reg = operands['dest_reg']
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            state.x86_registers.set_register(dest_reg, src_val)
        
        elif operands['dest_reg'] and operands['immediate'] is not None:
            # MOV reg, immediate
            dest_reg = operands['dest_reg']
            immediate = operands['immediate']
            imm_val = BitVecVal(immediate, 64)
            state.x86_registers.set_register(dest_reg, imm_val)
        
        elif operands['is_memory'] and operands['immediate'] is not None:
            # MOV [base+offset], immediate (byte operation)
            base_reg = operands['base_reg']
            offset = operands['offset']
            immediate = operands['immediate']
            
            if base_reg in [Register.R14, Register.R13]:
                # Store immediate to memory (R14 = stack base, R13 = callEngine pointer)
                imm_val = BitVecVal(immediate & 0xFF, 64)  # Byte operation
                new_memory_state = state.x86_memory.store_limb(offset, imm_val)
                state.x86_memory = new_memory_state
            else:
                raise ValueError(f"Unsupported base register for MOV: {base_reg}")
        
        return state
    
    elif mnemonic == 'add':
        # ADD: add source to destination, set carry flag
        if not operands['dest_reg']:
            raise ValueError(f"ADD instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)
        
        if operands['is_memory']:
            # ADD reg, [base+offset]
            base_reg = operands['base_reg']
            offset = operands['offset']
            
            if base_reg in [Register.R14, Register.R13]:
                # ADD with memory (R14 = stack base, R13 = callEngine pointer)
                # offset can be int (concrete) or BitVec (symbolic)
                # If there's an index register, compute: base_offset + index_reg
                memory_offset = offset
                if 'index_reg' in operands and operands['index_reg']:
                    index_reg = operands['index_reg']
                    index_val = state.x86_registers.get_register(index_reg)
                    if isinstance(offset, int):
                        offset_bv = BitVecVal(offset, 64)
                    else:
                        offset_bv = offset
                    memory_offset = offset_bv + index_val
                
                mem_val = state.x86_memory.load_limb(memory_offset)
                
                # Perform addition (64-bit with carry generation)
                reg_ext = Concat(BitVecVal(0, 1), reg_val)
                mem_ext = Concat(BitVecVal(0, 1), mem_val)
                sum_ext = reg_ext + mem_ext
                
                # Extract result and carry
                result = Extract(63, 0, sum_ext)
                carry_out = Extract(64, 64, sum_ext)
                
                # Update register and carry flag
                state.x86_registers.set_register(dest_reg, result)
                state.x86_registers.set_flag('CF', carry_out)
            else:
                raise ValueError(f"Unsupported base register for ADD: {base_reg}")
        
        elif operands['src_reg']:
            # ADD reg, reg
            src_reg = operands['src_reg']
            src_val = state.x86_registers.get_register(src_reg)
            
            # Perform addition
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            src_ext = Concat(BitVecVal(0, 1), src_val)
            sum_ext = reg_ext + src_ext
            
            result = Extract(63, 0, sum_ext)
            carry_out = Extract(64, 64, sum_ext)
            
            state.x86_registers.set_register(dest_reg, result)
            state.x86_registers.set_flag('CF', carry_out)
        
        return state
    
    elif mnemonic == 'adc':
        # ADC: add with carry
        if not operands['dest_reg'] or not operands['is_memory']:
            raise ValueError(f"ADC instruction must have register destination and memory source: {operands}")
        
        dest_reg = operands['dest_reg']
        base_reg = operands['base_reg']
        offset = operands['offset']
        
        if base_reg not in [Register.R14, Register.R13]:
            raise ValueError(f"Unsupported base register for ADC: {base_reg}")
        
        reg_val = state.x86_registers.get_register(dest_reg)
        # offset can be int (concrete) or BitVec (symbolic)
        # If there's an index register, compute: base_offset + index_reg
        memory_offset = offset
        if 'index_reg' in operands and operands['index_reg']:
            index_reg = operands['index_reg']
            index_val = state.x86_registers.get_register(index_reg)
            if isinstance(offset, int):
                offset_bv = BitVecVal(offset, 64)
            else:
                offset_bv = offset
            memory_offset = offset_bv + index_val
        
        mem_val = state.x86_memory.load_limb(memory_offset)
        carry_in = state.x86_registers.get_flag('CF')
        
        # Perform addition with carry
        reg_ext = Concat(BitVecVal(0, 1), reg_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        sum_ext = reg_ext + mem_ext + carry_ext
        
        result = Extract(63, 0, sum_ext)
        carry_out = Extract(64, 64, sum_ext)
        
        state.x86_registers.set_register(dest_reg, result)
        state.x86_registers.set_flag('CF', carry_out)
        
        return state
    
    elif mnemonic == 'sub':
        # SUB: subtract source from destination
        if not operands['dest_reg']:
            raise ValueError(f"SUB instruction must have register destination: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # SUB reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            state.x86_registers.set_register(dest_reg, result)
        
        return state
    
    elif mnemonic == 'cmp':
        # CMP: compare and set flags (doesn't modify operands)
        if not operands['dest_reg']:
            raise ValueError(f"CMP instruction must have register operand: {operands}")
        
        dest_reg = operands['dest_reg']
        reg_val = state.x86_registers.get_register(dest_reg)
        
        if operands['immediate'] is not None:
            # CMP reg, immediate
            imm_val = BitVecVal(operands['immediate'], 64)
            result = reg_val - imm_val
            
            # Set flags
            reg_ext = Concat(BitVecVal(0, 1), reg_val)
            imm_ext = Concat(BitVecVal(0, 1), imm_val)
            diff_ext = reg_ext - imm_ext
            cf = Extract(64, 64, diff_ext)
            state.x86_registers.set_flag('CF', cf)
            
            # ZF (zero flag)
            zf_bool = (reg_val == imm_val)
            zf = If(zf_bool, BitVecVal(1, 1), BitVecVal(0, 1))
            state.x86_registers.set_flag('ZF', zf)
        
        return state
    
    elif mnemonic == 'ret':
        # RET instruction: check exit status code and extract return data if needed
        # Read status code from x86 memory: [R13 + evmCallEngineExitContextNativeCallStatusCodeOffset]
        
        # Get R13 register value (callEngine pointer)
        r13_value = state.x86_registers.get_register(AMD64_RESERVED_REGISTER_FOR_CALL_ENGINE)
        
        # Calculate status code memory address
        status_code_offset = BitVecVal(EVM_CALL_ENGINE_EXIT_CONTEXT_NATIVE_CALL_STATUS_CODE_OFFSET, 64)
        status_code_addr = r13_value + status_code_offset
        
        # Read status code from x86 memory (8-bit byte)
        status_code = state.x86_memory.load_byte(status_code_addr)
        
        # Check if status code is RETURNED (0)
        # IMPORTANT: Only when status_code == RETURNED should we set return values
        # Other status codes (REVERTED, STOPPED, INVALID, etc.) have different behaviors
        status_code_is_returned = (status_code == BitVecVal(EVM_NATIVE_CALL_STATUS_CODE_RETURNED, 8))
        
        # Only extract return data if status code is RETURNED
        # For other status codes, we don't set return_offset/return_length
        # This matches Go code: only case evmNativeCallStatusCodeReturned sets return values
        
        # IMPORTANT: x86-64 does NOT operate on evm_stack or evm_memory directly
        # x86-64 uses x86 memory (via R14 for stack, R15 for EVM memory)
        # Get offset and length from x86 memory (EVM stack is stored in x86 memory via R14)
        # Go code: offset, size := c.PopUint64(), c.PopUint64()
        # This means: first pop size (stack[0]), then pop offset (stack[1])
        # Stack layout in x86 memory: stack[0] at R14-0x40, stack[1] at R14-0x20
        
        # Get R14 register value (stack base pointer)
        r14_value = state.x86_registers.get_register(Register.R14)
        
        # Extract stack values from x86 memory using absolute addresses
        # stack[0] (top) = size (length) at R14-0x40, stack[1] = offset at R14-0x20
        # We need to load 256-bit values (4×64-bit limbs) from x86 memory
        
        # Stack[0] (size/length): load from R14-0x40 (4×64-bit limbs)
        stack0_base = r14_value + BitVecVal(-0x40, 64)
        size_z0 = state.x86_memory.load_64bit(stack0_base)
        size_z1 = state.x86_memory.load_64bit(stack0_base + BitVecVal(8, 64))
        size_z2 = state.x86_memory.load_64bit(stack0_base + BitVecVal(16, 64))
        size_z3 = state.x86_memory.load_64bit(stack0_base + BitVecVal(24, 64))
        size_stack_value = Concat(size_z3, size_z2, size_z1, size_z0)  # 256-bit value
        
        # Stack[1] (offset): load from R14-0x20 (4×64-bit limbs)
        stack1_base = r14_value + BitVecVal(-0x20, 64)
        offset_z0 = state.x86_memory.load_64bit(stack1_base)
        offset_z1 = state.x86_memory.load_64bit(stack1_base + BitVecVal(8, 64))
        offset_z2 = state.x86_memory.load_64bit(stack1_base + BitVecVal(16, 64))
        offset_z3 = state.x86_memory.load_64bit(stack1_base + BitVecVal(24, 64))
        offset_stack_value = Concat(offset_z3, offset_z2, offset_z1, offset_z0)  # 256-bit value
        
        # Truncate 256-bit stack values to 64-bit for offset and length
        # Go code uses PopUint64(), so we need 64-bit values
        from z3 import Extract as Z3Extract
        if size_stack_value.size() == 256:
            length_bv = Z3Extract(63, 0, size_stack_value)  # Extract lower 64 bits
        elif size_stack_value.size() == 64:
            length_bv = size_stack_value
        else:
            raise ValueError(f"Unexpected size value size: {size_stack_value.size()}")
        
        if offset_stack_value.size() == 256:
            offset_bv = Z3Extract(63, 0, offset_stack_value)  # Extract lower 64 bits
        elif offset_stack_value.size() == 64:
            offset_bv = offset_stack_value
        else:
            raise ValueError(f"Unexpected offset value size: {offset_stack_value.size()}")
        
        # IMPORTANT: Use conditional symbolic values for return_offset and return_length
        # Only set return values if status_code == RETURNED
        # Different status codes have different behaviors (from Go code):
        # - RETURNED (0): Returns data (offset, size) - this is what we verify
        # - REVERTED: Returns error data (different semantic, not a successful return)
        # - STOPPED: Returns nil, nil (no return data)
        # - INVALID: Returns error (no return data)
        # 
        # Use If expression to conditionally set return values:
        # - If status_code == RETURNED: use extracted offset and length
        # - Otherwise: use 0 (no return value)
        
        # R15 register points to EVM memory base address (memoryElement0Address)
        r15_value = state.x86_registers.get_register(AMD64_RESERVED_REGISTER_FOR_MEMORY)
        
        # Conditionally set return values using If expression
        # This allows handling multiple paths symbolically
        zero_64 = BitVecVal(0, 64)
        
        # Only set return values if status_code == RETURNED
        # Otherwise, keep them as 0 (no return value)
        state.return_offset = If(status_code_is_returned, offset_bv, zero_64)
        state.return_length = If(status_code_is_returned, length_bv, zero_64)
        
        return state
    
    elif mnemonic in ['jb', 'jae', 'jmp']:
        # Control flow instructions - return state as-is
        # These will be handled at the control flow level
        return state
    
    else:
        # Unknown instruction - return state unchanged
        # TODO: Implement more instructions
        return state

