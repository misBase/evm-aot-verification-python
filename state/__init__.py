"""
State management module for SMT state modeling.

This module provides unified state management for EVM IR and x86-64 programs,
modeling stack, memory, and registers as symbolic variables.
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

