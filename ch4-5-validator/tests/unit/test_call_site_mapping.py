"""Tests for host call-site identity mapping."""

import pytest

from evm_ir.json_parser import CompilerEVMResult
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from verification.call_site_mapping import build_call_site_mapping
from x86_64.aot_profile import AOT_COMPILER_PROFILE, X86AOTProfile
from x86_64.program import X86Program


def _make_evm_program(
    host_kind: str,
    pc: int = 0x20,
    immediate: int | None = None,
) -> EVMProgram:
    block = EVMBlock(
        pc=pc,
        stack_depth=0,
        min_depth=0,
        max_depth=0,
        static_gas=0,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=False,
        operations=[EvmOperator(kind=host_kind, pc=pc, immediate=immediate)],
    )
    return EVMProgram(CompilerEVMResult(blocks=[block]))


def _make_profile(host_functions) -> X86AOTProfile:
    return X86AOTProfile(
        offsets=AOT_COMPILER_PROFILE.offsets,
        status_codes=AOT_COMPILER_PROFILE.status_codes,
        resumable_statuses=AOT_COMPILER_PROFILE.resumable_statuses,
        builtin_functions=AOT_COMPILER_PROFILE.builtin_functions,
        host_functions=host_functions,
    )


def _host_bridge_hex(go_func_index: int) -> str:
    # mov rax, 0x1017
    # mov [r13+0xf0], rax
    # mov byte ptr [r13+0xe0], 4
    # mov dword ptr [r13+0xe8], <go_func_index>
    # ret
    return (
        "48c7c017100000"
        "498985f0000000"
        "41c685e000000004"
        "41c785e8000000"
        f"{go_func_index.to_bytes(4, byteorder='little').hex()}"
        "c3"
    )


def test_build_call_site_mapping_validates_matching_host_kind():
    evm_program = _make_evm_program("BALANCE", pc=0x20)
    profile = _make_profile({11: "balance"})
    x86_program = X86Program.from_hex(_host_bridge_hex(11), base_addr=0x1000, aot_profile=profile)

    mapping = build_call_site_mapping(evm_program, x86_program)

    assert len(mapping) == 1
    assert mapping.get_evm_pc(0x1000) == 0x20


def test_build_call_site_mapping_preserves_evm_host_immediate():
    evm_program = _make_evm_program("LOG", pc=0x20, immediate=3)
    profile = _make_profile({17: "log"})
    x86_program = X86Program.from_hex(
        _host_bridge_hex(17),
        base_addr=0x1000,
        aot_profile=profile,
    )

    mapping = build_call_site_mapping(evm_program, x86_program)

    site = mapping.get_evm_site(0x1000)
    assert site.pc == 0x20
    assert site.kind == "LOG"
    assert site.immediate == 3


def test_build_call_site_mapping_rejects_host_kind_mismatch():
    evm_program = _make_evm_program("BALANCE", pc=0x20)
    profile = _make_profile({11: "staticCall"})
    x86_program = X86Program.from_hex(_host_bridge_hex(11), base_addr=0x1000, aot_profile=profile)

    with pytest.raises(ValueError, match="host call-site kind mismatch"):
        build_call_site_mapping(evm_program, x86_program)
