"""
x86-64 Semantics Model for Verification

This module models the execution semantics of x86-64 instructions used in
the AOT-compiled EVM code. Now supports symbolic stack operations matching
the AOT compiler's stack layout.
"""

from z3 import BitVec, BitVecVal, Extract, Concat, If, simplify, ULT, UGE
from typing import Dict, Optional, List
from enum import Enum


class Register(Enum):
    """x86-64 register enumeration."""
    RAX = "rax"
    RCX = "rcx"
    RDX = "rdx"
    RBX = "rbx"
    RSI = "rsi"
    RDI = "rdi"
    R8 = "r8"
    R9 = "r9"
    R10 = "r10"
    R11 = "r11"
    R12 = "r12"
    R13 = "r13"  # Reserved for callEngine pointer
    R14 = "r14"  # Reserved for stack base pointer
    R15 = "r15"  # Reserved for memory pointer


class Flags:
    """Models x86-64 CPU flags."""
    
    def __init__(self):
        # Flags for conditional operations
        self.cf = BitVec("cf_init", 1)  # Carry flag
        self.zf = BitVec("zf_init", 1)  # Zero flag
        self.sf = BitVec("sf_init", 1)  # Sign flag
    
    def set_carry(self, value):
        """Set the carry flag."""
        self.cf = value
    
    def get_carry(self):
        """Get the carry flag."""
        return self.cf
    
    def set_zero(self, value):
        """Set the zero flag."""
        self.zf = value
    
    def set_sign(self, value):
        """Set the sign flag."""
        self.sf = value


class X86State:
    """Models the x86-64 execution state including symbolic stack."""
    
    def __init__(self):
        # Register file (64-bit registers)
        self.regs: Dict[Register, any] = {
            Register.RAX: BitVec("rax_init", 64),
            Register.RCX: BitVec("rcx_init", 64),
            Register.RDX: BitVec("rdx_init", 64),
            Register.RBX: BitVec("rbx_init", 64),
            Register.RSI: BitVec("rsi_init", 64),
            Register.RDI: BitVec("rdi_init", 64),
            Register.R8: BitVec("r8_init", 64),
            Register.R9: BitVec("r9_init", 64),
            Register.R10: BitVec("r10_init", 64),
            Register.R11: BitVec("r11_init", 64),
            Register.R12: BitVec("r12_init", 64),
            Register.R13: BitVec("r13_init", 64),
            Register.R14: BitVec("r14_init", 64),
            Register.R15: BitVec("r15_init", 64),
        }
        
        # CPU flags
        self.flags = Flags()
        
        # Memory model: symbolic memory backing the stack
        # Key is offset from R14 (stack base pointer)
        self.memory: Dict[int, any] = {}
    
    def get_reg(self, reg: Register):
        """Get register value."""
        return self.regs[reg]
    
    def set_reg(self, reg: Register, value):
        """Set register value."""
        self.regs[reg] = value
    
    def get_mem_offset(self, offset: int):
        """Get memory value at R14 + offset."""
        if offset not in self.memory:
            # Create symbolic value for uninitialized memory
            self.memory[offset] = BitVec(f"stack_{offset:+d}", 64)
        return self.memory[offset]
    
    def set_mem_offset(self, offset: int, value):
        """Set memory value at R14 + offset."""
        self.memory[offset] = value


class X86Executor:
    """Symbolic executor for x86-64 instructions matching AOT compiler output."""
    
    def __init__(self, initial_stack_values: Optional[List] = None):
        """Initialize with optional symbolic stack.
        
        Args:
            initial_stack_values: List of 8 symbolic 64-bit values representing
                                 two 256-bit stack values:
                                 [val1_z0, val1_z1, val1_z2, val1_z3,
                                  val2_z0, val2_z1, val2_z2, val2_z3]
        """
        self.state = X86State()
        
        # Initialize stack memory if provided
        if initial_stack_values:
            # Stack layout (growing down from R14):
            # [R14 - 0x40] = val1_z0 (first value, limb 0)
            # [R14 - 0x38] = val1_z1
            # [R14 - 0x30] = val1_z2
            # [R14 - 0x28] = val1_z3
            # [R14 - 0x20] = val2_z0 (second value, limb 0)
            # [R14 - 0x18] = val2_z1
            # [R14 - 0x10] = val2_z2
            # [R14 - 0x08] = val2_z3
            offsets = [-0x40, -0x38, -0x30, -0x28, -0x20, -0x18, -0x10, -0x08]
            for offset, value in zip(offsets, initial_stack_values):
                self.state.set_mem_offset(offset, value)
    
    # === Basic Instructions ===
    
    def mov_reg_imm(self, dest: Register, imm: int):
        """MOV dest, immediate - Move immediate value to register."""
        self.state.set_reg(dest, BitVecVal(imm, 64))
    
    def mov_reg_reg(self, dest: Register, src: Register):
        """MOV dest, src - Move register to register."""
        value = self.state.get_reg(src)
        self.state.set_reg(dest, value)
    
    def mov_reg_mem(self, dest: Register, base: Register, offset: int):
        """MOV dest, [base + offset] - Load from memory to register."""
        if base == Register.R14:
            # Loading from stack memory
            value = self.state.get_mem_offset(offset)
            self.state.set_reg(dest, value)
        else:
            # General memory access (not used in our case)
            base_addr = self.state.get_reg(base)
            addr_key = f"{base.value}+{offset}"
            if addr_key not in self.state.memory:
                self.state.memory[addr_key] = BitVec(f"mem_{addr_key}", 64)
            value = self.state.memory[addr_key]
            self.state.set_reg(dest, value)
    
    def mov_mem_reg(self, base: Register, offset: int, src: Register):
        """MOV [base + offset], src - Store register to memory."""
        value = self.state.get_reg(src)
        if base == Register.R14:
            # Storing to stack memory
            self.state.set_mem_offset(offset, value)
        else:
            # General memory access
            addr_key = f"{base.value}+{offset}"
            self.state.memory[addr_key] = value
    
    # === Arithmetic Instructions ===
    
    def add_reg_imm(self, dest: Register, imm: int):
        """ADD dest, immediate - Add immediate to register, set flags."""
        old_val = self.state.get_reg(dest)
        
        # Extend to 65 bits to capture carry
        old_ext = Concat(BitVecVal(0, 1), old_val)
        imm_ext = Concat(BitVecVal(0, 1), BitVecVal(imm, 64))
        
        # Perform addition
        sum_ext = old_ext + imm_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry = Extract(64, 64, sum_ext)
        
        # Update register and flags
        self.state.set_reg(dest, result)
        self.state.flags.set_carry(carry)
    
    def add_reg_reg(self, dest: Register, src: Register):
        """ADD dest, src - Add register to register, set flags."""
        dest_val = self.state.get_reg(dest)
        src_val = self.state.get_reg(src)
        
        # Extend to 65 bits to capture carry
        dest_ext = Concat(BitVecVal(0, 1), dest_val)
        src_ext = Concat(BitVecVal(0, 1), src_val)
        
        # Perform addition
        sum_ext = dest_ext + src_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry = Extract(64, 64, sum_ext)
        
        # Update register and flags
        self.state.set_reg(dest, result)
        self.state.flags.set_carry(carry)
    
    def add_reg_mem(self, dest: Register, base: Register, offset: int):
        """ADD dest, [base + offset] - Add memory to register."""
        dest_val = self.state.get_reg(dest)
        
        if base == Register.R14:
            mem_val = self.state.get_mem_offset(offset)
        else:
            addr_key = f"{base.value}+{offset}"
            if addr_key not in self.state.memory:
                self.state.memory[addr_key] = BitVec(f"mem_{addr_key}", 64)
            mem_val = self.state.memory[addr_key]
        
        # Extend to 65 bits to capture carry
        dest_ext = Concat(BitVecVal(0, 1), dest_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        
        # Perform addition
        sum_ext = dest_ext + mem_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry = Extract(64, 64, sum_ext)
        
        # Update register and flags
        self.state.set_reg(dest, result)
        self.state.flags.set_carry(carry)
    
    def adc_reg_imm(self, dest: Register, imm: int):
        """ADC dest, immediate - Add with carry."""
        old_val = self.state.get_reg(dest)
        carry_in = self.state.flags.get_carry()
        
        # Extend to 65 bits
        old_ext = Concat(BitVecVal(0, 1), old_val)
        imm_ext = Concat(BitVecVal(0, 1), BitVecVal(imm, 64))
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        
        # Perform addition with carry
        sum_ext = old_ext + imm_ext + carry_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry = Extract(64, 64, sum_ext)
        
        # Update register and flags
        self.state.set_reg(dest, result)
        self.state.flags.set_carry(carry)
    
    def adc_reg_mem(self, dest: Register, base: Register, offset: int):
        """ADC dest, [base + offset] - Add with carry from memory."""
        dest_val = self.state.get_reg(dest)
        carry_in = self.state.flags.get_carry()
        
        if base == Register.R14:
            mem_val = self.state.get_mem_offset(offset)
        else:
            addr_key = f"{base.value}+{offset}"
            if addr_key not in self.state.memory:
                self.state.memory[addr_key] = BitVec(f"mem_{addr_key}", 64)
            mem_val = self.state.memory[addr_key]
        
        # Extend to 65 bits
        dest_ext = Concat(BitVecVal(0, 1), dest_val)
        mem_ext = Concat(BitVecVal(0, 1), mem_val)
        carry_ext = Concat(BitVecVal(0, 64), carry_in)
        
        # Perform addition with carry
        sum_ext = dest_ext + mem_ext + carry_ext
        
        # Extract result and carry
        result = Extract(63, 0, sum_ext)
        carry = Extract(64, 64, sum_ext)
        
        # Update register and flags
        self.state.set_reg(dest, result)
        self.state.flags.set_carry(carry)
    
    def sub_reg_imm(self, dest: Register, imm: int):
        """SUB dest, immediate - Subtract immediate from register."""
        old_val = self.state.get_reg(dest)
        imm_val = BitVecVal(imm, 64)
        result = old_val - imm_val
        self.state.set_reg(dest, result)
    
    # === Comparison Instructions ===
    
    def cmp_reg_imm(self, reg: Register, imm: int):
        """CMP reg, immediate - Compare register with immediate (sets flags)."""
        reg_val = self.state.get_reg(reg)
        imm_val = BitVecVal(imm, 64)
        
        # Compute difference
        diff = reg_val - imm_val
        
        # Set zero flag
        self.state.flags.set_zero(If(diff == 0, BitVecVal(1, 1), BitVecVal(0, 1)))
        
        # Set carry flag (for unsigned comparison)
        # CF = 1 if reg < imm (unsigned)
        self.state.flags.set_carry(If(ULT(reg_val, imm_val), BitVecVal(1, 1), BitVecVal(0, 1)))
    
    # === Control Flow (for modeling, not actual execution) ===
    
    def jb(self, target):
        """JB (Jump if Below) - Jump if CF=1."""
        return self.state.flags.cf
    
    def jae(self, target):
        """JAE (Jump if Above or Equal) - Jump if CF=0."""
        return If(self.state.flags.cf == 0, BitVecVal(1, 1), BitVecVal(0, 1))
    
    def jmp(self, target):
        """JMP - Unconditional jump (always taken)."""
        return BitVecVal(1, 1)
    
    def ret(self):
        """RET - Return from function."""
        pass
    
    # === High-Level ADD Operation ===
    
    def execute_aot_add_from_stack(self):
        """Execute ADD operation matching the disassembly (0x6c - 0xac).
        
        This reads two 256-bit values from the stack, adds them,
        and stores the result back to the stack.
        
        Stack layout:
          [R14 - 0x40..0x28] = First value (4 limbs)
          [R14 - 0x20..0x08] = Second value (4 limbs)
          Result stored at [R14 - 0x40..0x28]
        
        Disassembly:
          6c: mov rax, [r14-0x40]
          70: add rax, [r14-0x20]
          74: mov rcx, [r14-0x38]
          78: adc rcx, [r14-0x18]
          7c: mov rdx, [r14-0x30]
          80: adc rdx, [r14-0x10]
          84: mov rbx, [r14-0x28]
          88: adc rbx, [r14-0x08]
          8c: mov [r14-0x40], rax
          90: mov [r14-0x38], rcx
          94: mov [r14-0x30], rdx
          98: mov [r14-0x28], rbx
        """
        # Limb 0: Load and add
        self.mov_reg_mem(Register.RAX, Register.R14, -0x40)  # Load val1.z0
        self.add_reg_mem(Register.RAX, Register.R14, -0x20)  # Add val2.z0
        
        # Limb 1: Load and add with carry
        self.mov_reg_mem(Register.RCX, Register.R14, -0x38)  # Load val1.z1
        self.adc_reg_mem(Register.RCX, Register.R14, -0x18)  # Add val2.z1 + CF
        
        # Limb 2: Load and add with carry
        self.mov_reg_mem(Register.RDX, Register.R14, -0x30)  # Load val1.z2
        self.adc_reg_mem(Register.RDX, Register.R14, -0x10)  # Add val2.z2 + CF
        
        # Limb 3: Load and add with carry
        self.mov_reg_mem(Register.RBX, Register.R14, -0x28)  # Load val1.z3
        self.adc_reg_mem(Register.RBX, Register.R14, -0x08)  # Add val2.z3 + CF
        
        # Store result back to stack
        self.mov_mem_reg(Register.R14, -0x40, Register.RAX)  # Store result.z0
        self.mov_mem_reg(Register.R14, -0x38, Register.RCX)  # Store result.z1
        self.mov_mem_reg(Register.R14, -0x30, Register.RDX)  # Store result.z2
        self.mov_mem_reg(Register.R14, -0x28, Register.RBX)  # Store result.z3
    
    def get_stack_result_uint256(self):
        """Get the 256-bit result from the stack (top value).
        
        Returns the value at [R14-0x40..0x28] as a 256-bit bitvector.
        """
        z0 = self.state.get_mem_offset(-0x40)
        z1 = self.state.get_mem_offset(-0x38)
        z2 = self.state.get_mem_offset(-0x30)
        z3 = self.state.get_mem_offset(-0x28)
        
        # Concatenate to form 256-bit value
        return Concat(z3, z2, z1, z0)


def test_x86_add_symbolic():
    """Test the x86-64 ADD execution with symbolic stack."""
    from z3 import BitVec
    
    print("=== x86-64 Symbolic ADD Test ===")
    
    # Create symbolic stack values
    val1_z0 = BitVec("val1_z0", 64)
    val1_z1 = BitVec("val1_z1", 64)
    val1_z2 = BitVec("val1_z2", 64)
    val1_z3 = BitVec("val1_z3", 64)
    val2_z0 = BitVec("val2_z0", 64)
    val2_z1 = BitVec("val2_z1", 64)
    val2_z2 = BitVec("val2_z2", 64)
    val2_z3 = BitVec("val2_z3", 64)
    
    stack_values = [val1_z0, val1_z1, val1_z2, val1_z3,
                   val2_z0, val2_z1, val2_z2, val2_z3]
    
    # Execute ADD
    executor = X86Executor(initial_stack_values=stack_values)
    executor.execute_aot_add_from_stack()
    result = executor.get_stack_result_uint256()
    
    print(f"x86-64 Result: {result}")
    
    return result


def test_x86_add_concrete():
    """Test the x86-64 ADD execution with concrete values."""
    print("\n=== x86-64 Concrete ADD Test ===")
    
    # Create concrete stack: 0x60 + 0x10
    val1 = [BitVecVal(0x60, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    val2 = [BitVecVal(0x10, 64), BitVecVal(0, 64), BitVecVal(0, 64), BitVecVal(0, 64)]
    
    stack_values = val1 + val2
    
    # Execute ADD
    executor = X86Executor(initial_stack_values=stack_values)
    executor.execute_aot_add_from_stack()
    result = executor.get_stack_result_uint256()
    
    result_simplified = simplify(result)
    print(f"x86-64 Result: {result_simplified}")
    print(f"Expected: 0x70")
    
    expected = BitVecVal(0x70, 256)
    print(f"Match: {simplify(result == expected)}")
    
    return result


if __name__ == "__main__":
    print("=== x86-64 Executor Tests ===\n")
    print("[Test 1] Symbolic ADD")
    test_x86_add_symbolic()
    print("\n[Test 2] Concrete ADD")
    test_x86_add_concrete()
