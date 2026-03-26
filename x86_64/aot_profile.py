"""
x86 AOT profile definitions.

Current project scope is go-hpc-evm only.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, FrozenSet


@dataclass(frozen=True)
class X86AOTProfile:
    """AOT runtime constants for x86 symbolic modeling."""

    offsets: Dict[str, int]
    status_codes: Dict[str, int]
    resumable_statuses: FrozenSet[int]
    builtin_functions: Dict[int, str] = field(default_factory=dict)
    host_functions: Dict[int, str] = field(default_factory=dict)
    # Stack bias: added to Go's sp (in limbs) before computing address
    # Formula: addr = R14 + (sp + stack_sp_bias_limbs) * 8
    # 默认情况下真实 amd64 AOT 的物理栈从 R14+0 开始，
    # 仅在某些验证适配场景下才需要额外 bias。
    stack_sp_bias_limbs: int = 0


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
    builtin_functions={
        0: "memory_grow",
        1: "stack_grow",       # no-op in Go runtime
        2: "calldatacopy",     # no-op in Go runtime
        3: "returndatacopy",   # no-op in Go runtime
        4: "div",
        5: "mod",
        6: "addmod",
        7: "mulmod",
        8: "exp",
        9: "gas_cost",
    },
    host_functions={},  # Runtime-dependent; configure per contract
)
