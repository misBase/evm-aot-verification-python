#!/usr/bin/env python3
"""muti_block x64 指令与回归测试。"""

from pathlib import Path

import pytest
from z3 import BitVecVal, is_true, simplify

from state.smt_state import SMTState
from x86_64.disassembler import disassemble_hex
from x86_64.execution_state import ExecutionState
from x86_64.inst_executor import InstructionExecutor
from x86_64.models import Register


def _exec_single(hex_code: str, state: SMTState, base_addr: int = 0x1000) -> SMTState:
    insn = disassemble_hex(hex_code, base_addr=base_addr)[0]
    return insn.to_z3(state)


def test_movabs_semantics_writes_imm64():
    state = SMTState()
    # movabs rbx, 0x800000000000000
    out = _exec_single("48bb0000000000000008", state, base_addr=0x10F)
    assert is_true(
        simplify(out.x86_registers.get_register(Register.RBX) == BitVecVal(0x0800000000000000, 64))
    )


def test_lea_rip_relative_semantics():
    state = SMTState()
    # 0x1f3: lea r8, [rip + 0x18]  -> r8 = 0x1f3 + 7 + 0x18 = 0x212
    out = _exec_single("4c8d0518000000", state, base_addr=0x1F3)
    assert is_true(simplify(out.x86_registers.get_register(Register.R8) == BitVecVal(0x212, 64)))


def test_add_memory_destination_with_register_updates_flags():
    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(0x1000, 64))
    state.x86_registers.set_register(Register.RAX, BitVecVal(2, 64))
    state.x86_memory = state.x86_memory.store_64bit(BitVecVal(0x1030, 64), BitVecVal(1, 64))

    # add qword ptr [r13 + 0x30], rax
    out = _exec_single("49014530", state, base_addr=0x2D8)

    assert is_true(simplify(out.x86_memory.load_64bit(BitVecVal(0x1030, 64)) == BitVecVal(3, 64)))
    assert is_true(simplify(out.x86_registers.get_flag("CF") == BitVecVal(0, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("OF") == BitVecVal(0, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("ZF") == BitVecVal(0, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("SF") == BitVecVal(0, 1)))


def test_add_memory_destination_with_immediate_updates_flags():
    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(0x1000, 64))
    state.x86_memory = state.x86_memory.store_64bit(
        BitVecVal(0x1030, 64), BitVecVal((1 << 64) - 1, 64)
    )

    # add qword ptr [r13 + 0x30], 1
    out = _exec_single("4983453001", state, base_addr=0x2D8)

    assert is_true(simplify(out.x86_memory.load_64bit(BitVecVal(0x1030, 64)) == BitVecVal(0, 64)))
    assert is_true(simplify(out.x86_registers.get_flag("CF") == BitVecVal(1, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("OF") == BitVecVal(0, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("ZF") == BitVecVal(1, 1)))
    assert is_true(simplify(out.x86_registers.get_flag("SF") == BitVecVal(0, 1)))


def test_inst_executor_supports_movabs_lea_and_add_mem_dest():
    executor = InstructionExecutor()
    state = ExecutionState(initial_memory={0x30: BitVecVal(2, 64)})
    state.set_register(Register.R13, BitVecVal(0x1000, 64))
    state.set_register(Register.RAX, BitVecVal(1, 64))

    # movabs rbx, imm64; lea r8, [rip+0x18]; add qword ptr [r13+0x30], rax
    insns = disassemble_hex("48bb00000000000000084c8d051800000049014530", base_addr=0x10F)
    for insn in insns:
        executor.execute_instruction(state, insn)

    assert is_true(simplify(state.get_register(Register.RBX) == BitVecVal(0x0800000000000000, 64)))
    assert is_true(simplify(state.get_register(Register.R8) == BitVecVal(0x138, 64)))
    assert is_true(simplify(state.load_memory(0x30) == BitVecVal(3, 64)))


@pytest.mark.parametrize(
    "hex_path,prefix_idx",
    [
        ("tests/data/muti_block.hex", 155),
        ("tests/data/muti_block_08.hex", 155),
    ],
)
def test_muti_block_prefix_exec_covers_new_instructions_without_unsupported(hex_path: str, prefix_idx: int):
    """回归：覆盖首个 movabs/lea/add [mem],* 出现区间，确保不再抛未支持异常。"""
    hex_data = Path(hex_path).read_text().strip()
    instructions = disassemble_hex(hex_data, base_addr=0x0)
    assert len(instructions) > prefix_idx

    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(0x1000, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(0x2000, 64))
    state.x86_registers.set_register(Register.R15, BitVecVal(0x3000, 64))

    for insn in instructions[: prefix_idx + 1]:
        state = insn.to_z3(state)
