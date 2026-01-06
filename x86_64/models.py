"""
x86-64数据模型。

本模块定义用于表示x86-64块和指令的数据结构。
"""

from typing import List, Optional, Dict, Any, TYPE_CHECKING, TYPE_CHECKING as TYPE_CHECKING_RUNTIME
from dataclasses import dataclass, field
from enum import Enum
import capstone as cs_module

if TYPE_CHECKING:
    from state.smt_state import SMTState


class Register(Enum):
    """x86-64寄存器枚举。"""
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
    R13 = "r13"  # 保留用于callEngine指针
    R14 = "r14"  # 保留用于栈基址指针
    R15 = "r15"  # 保留用于内存指针


@dataclass
class X86Instruction:
    """表示x86-64指令。"""

    addr: int  # 指令地址
    mnemonic: str  # 指令助记符（例如，"mov"、"add"、"adc"）
    op_str: str  # 操作数字符串
    bytes: bytes  # 指令字节
    size: int  # 指令大小（字节）
    # 原始Capstone指令对象（用于访问操作数结构）
    _cs_insn: Optional[Any] = field(default=None, repr=False)

    def __post_init__(self):
        """如果未提供则设置大小。"""
        if self.size == 0:
            self.size = len(self.bytes)
    
    def to_z3(self, state: 'SMTState') -> 'SMTState':
        """将此指令转换为Z3公式，更新状态。
        
        这是Alive2风格的直接公式构建方法。
        委托给语义模块进行实际实现。
        
        Args:
            state: 当前SMT状态（将被修改）
            
        Returns:
            更新后的SMT状态
        """
        # 在此处导入以避免循环依赖
        from x86_64.semantics import x86_instruction_to_z3
        return x86_instruction_to_z3(self, state)


@dataclass
class X86Block:
    """表示x86-64基本块。"""
    
    start_addr: int  # 块起始地址
    end_addr: int  # 块结束地址
    instructions: List[X86Instruction] = field(default_factory=list)  # 块中的指令
    tag_marker: Optional[int] = None  # 标签标记地址（如果有）
    is_jump_target: bool = False  # 此块是否为跳转目标
    corresponding_evm_block: Optional[int] = None  # 对应的EVM块PC
    
    def __repr__(self):
        return (f"X86Block(start=0x{self.start_addr:x}, end=0x{self.end_addr:x}, "
                f"instructions={len(self.instructions)})")

