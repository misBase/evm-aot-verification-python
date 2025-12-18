"""
用于SMT状态建模的状态管理模块。

本模块为EVM IR和x86-64程序提供统一的状态管理，
将栈、内存和寄存器建模为符号变量。
"""

from .smt_state import (
    SMTState,
    EVMStackState,
    EVMMemoryState,
    X86MemoryState,
    X86RegisterState,
)

__all__ = [
    'SMTState',
    'EVMStackState',
    'EVMMemoryState',
    'X86MemoryState',
    'X86RegisterState',
]

