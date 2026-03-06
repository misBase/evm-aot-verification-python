"""
x86 AOT profile definitions.

Current project scope is go-hpc-evm only.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet


@dataclass(frozen=True)
class X86AOTProfile:
    """AOT runtime constants for x86 symbolic modeling."""

    offsets: Dict[str, int]
    status_codes: Dict[str, int]
    resumable_statuses: FrozenSet[int]


GO_HPC_EVM_PROFILE = X86AOTProfile(
    offsets={
        "status_code": 0xE0,
        "builtin_function_index": 0xE4,
        "go_function_index": 0xE8,
        "return_address": 0xF0,
        "stack_pointer": 0x28,
    },
    status_codes={
        "returned": 0,
        "reverted": 1,
        "stopped": 2,
        "invalid": 3,
        "call_go_host_function": 4,
        "call_builtin_function": 5,
        "write_protection": 6,
        "return_data_out_of_bounds": 7,
        "invalid_jump": 8,
        "invalid_retsub": 9,
        "return_stack_exceeded": 10,
        "invalid_subroutine_entry": 11,
        "out_of_gas": 12,
        "gas_uint_overflow": 13,
        "stack_underflow": 14,
        "stack_reached_limit": 15,
        "max_init_code_size_exceeded": 16,
        "debug": 17,
    },
    resumable_statuses=frozenset({4, 5, 17}),
)
