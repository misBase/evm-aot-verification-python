"""
x86-64 data models.

This module defines data structures for representing x86-64 blocks and instructions.
"""

from typing import List, Optional, Dict, Any
from dataclasses import dataclass, field
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


@dataclass
class X86Instruction:
    """Represents an x86-64 instruction."""
    
    addr: int  # Instruction address
    mnemonic: str  # Instruction mnemonic (e.g., "mov", "add", "adc")
    op_str: str  # Operand string
    bytes: bytes  # Instruction bytes
    size: int  # Instruction size in bytes
    
    def __post_init__(self):
        """Set size if not provided."""
        if self.size == 0:
            self.size = len(self.bytes)


@dataclass
class X86Block:
    """Represents an x86-64 basic block."""
    
    start_addr: int  # Block start address
    end_addr: int  # Block end address
    instructions: List[X86Instruction] = field(default_factory=list)  # Instructions in block
    tag_marker: Optional[int] = None  # Tag marker address (if any)
    is_jump_target: bool = False  # Whether this block is a jump target
    corresponding_evm_block: Optional[int] = None  # Corresponding EVM block PC
    
    def __repr__(self):
        return (f"X86Block(start=0x{self.start_addr:x}, end=0x{self.end_addr:x}, "
                f"instructions={len(self.instructions)})")

