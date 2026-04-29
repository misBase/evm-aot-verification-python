"""x86_memory 三 domain 路由的回归测试。

防御 mstore_return bug：之前 callEngine（R13）/ stack（R14）/ EVM mem（R15）
共用单一 Z3 Array，求解器把 R13/R14/R15 选成相邻数值时，写入 [R13+0x28] 会
污染从 [R14] 读出的栈数据。拆三个独立 Array 后此别名应消失。
"""

from pathlib import Path

import pytest
from z3 import BitVec, BitVecVal, Solver, sat, unsat, simplify, Store

from state.smt_state import (
    MemoryDomain,
    MemoryDomainError,
    PointerTag,
    SMTState,
    X86MemoryState,
)
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register


def test_three_domains_default_to_zero():
    mem = X86MemoryState()
    for domain in (MemoryDomain.CALLENGINE, MemoryDomain.STACK, MemoryDomain.EVM):
        assert simplify(mem.load_byte(BitVecVal(0, 64), domain=domain)) == BitVecVal(0, 8)
        assert simplify(mem.load_byte(BitVecVal(0xDEAD, 64), domain=domain)) == BitVecVal(0, 8)


def test_writes_in_one_domain_do_not_leak_into_others():
    mem = X86MemoryState()
    mem = mem.store_byte(BitVecVal(0x10, 64), BitVecVal(0xAB, 8), domain=MemoryDomain.STACK)
    # stack 域看到 0xAB，其它两域仍为 0
    assert simplify(mem.load_byte(BitVecVal(0x10, 64), domain=MemoryDomain.STACK)) == BitVecVal(0xAB, 8)
    assert simplify(mem.load_byte(BitVecVal(0x10, 64), domain=MemoryDomain.CALLENGINE)) == BitVecVal(0, 8)
    assert simplify(mem.load_byte(BitVecVal(0x10, 64), domain=MemoryDomain.EVM)) == BitVecVal(0, 8)


def test_unknown_domain_string_raises():
    mem = X86MemoryState()
    with pytest.raises(MemoryDomainError):
        mem.load_byte(BitVecVal(0, 64), domain="oops")


def test_unrouted_base_register_raises_in_production():
    """base_reg ∉ {R13,R14,R15} 时，生产路径（无 unrouted_memory_domain 兜底）应抛错。"""
    state = SMTState()
    # 不设 unrouted_memory_domain；用 [rax] 写
    state.x86_registers.set_register(Register.RAX, BitVecVal(0x100, 64))
    # mov byte ptr [rax], 0xAB （hex: c6 00 ab）
    insns = disassemble_hex("c600ab", base_addr=0)
    with pytest.raises(MemoryDomainError) as exc_info:
        insns[0].to_z3(state)
    assert exc_info.value.base_reg == Register.RAX


def test_callengine_and_stack_writes_do_not_alias_at_overlapping_bases():
    """直接复现 mstore_return bug 的 ground truth。

    旧模型（共享 Array）：求解器把 R13/R14 选成相距 22 字节，[R13+0x28]=8
    会污染 [R14]=9 的读取。新模型按 domain 路由后，此别名永远不可能成立。
    """
    mem = X86MemoryState()
    R13 = BitVec('R13', 64)
    R14 = BitVec('R14', 64)

    mem = mem.store_64bit(R13 + BitVecVal(0x28, 64), BitVecVal(8, 64),
                          domain=MemoryDomain.CALLENGINE)
    mem = mem.store_64bit(R14, BitVecVal(9, 64), domain=MemoryDomain.STACK)

    solver = Solver()
    solver.set("timeout", 10000)
    # 旧模型反例参数：R13 ≈ R14 + 22（mstore_return dump 里的具体 model）
    solver.add(R13 == R14 + BitVecVal(22, 64))
    # 在 STACK 域读 R14，应严格等于 9，与 R13/R14 取值无关
    read_back = mem.load_64bit(R14, domain=MemoryDomain.STACK)
    solver.add(read_back != BitVecVal(9, 64))
    assert solver.check() == unsat, "STACK 域的读不应被 CALLENGINE 域的写污染"


def test_separate_arrays_keep_pure_alu_unit_tests_working():
    """指令机制单测（[rax] 等非三域 base）通过 unrouted_memory_domain 兜底到 STACK。"""
    state = SMTState()
    state.unrouted_memory_domain = MemoryDomain.STACK
    state.x86_registers.set_register(Register.RAX, BitVecVal(0x100, 64))
    # mov byte ptr [rax], 0xAB
    insns = disassemble_hex("c600ab", base_addr=0)
    out = insns[0].to_z3(state)
    # 应能通过 STACK 域读出
    val = simplify(out.x86_memory.load_byte(BitVecVal(0x100, 64), domain=MemoryDomain.STACK))
    assert val == BitVecVal(0xAB, 8)


def test_create_initial_state_does_not_enable_unrouted_fallback():
    """生产路径（create_initial_state）默认 unrouted_memory_domain=None，保持严格检查。"""
    state = SMTState.create_initial_state(num_inputs=0)
    assert state.unrouted_memory_domain is None


def test_mov_loads_calldata_pointer_tag_from_callengine():
    state = SMTState.create_initial_state(num_inputs=0)
    insn = disassemble_hex("498bb590000000", base_addr=0)[0]

    state = insn.to_z3(state)

    assert state.x86_registers.get_pointer_tag(Register.RSI) == PointerTag.CALLDATA_PTR
    solver = Solver()
    solver.add(state.x86_registers.get_register(Register.RSI) != state.callengine_input_pointer)
    assert solver.check() == unsat


def test_mov_loads_writable_base_pointer_tags_from_callengine():
    state = SMTState.create_initial_state(num_inputs=0)

    for hex_code, reg, expected_tag, side_channel_attr in (
        ("498b7510", Register.RSI, PointerTag.EVM_PTR, "callengine_memory_base"),
        ("498b7d38", Register.RDI, PointerTag.STACK_PTR, "callengine_stack_base"),
    ):
        out = disassemble_hex(hex_code, base_addr=0)[0].to_z3(state.copy())
        assert out.x86_registers.get_pointer_tag(reg) == expected_tag
        solver = Solver()
        solver.add(
            out.x86_registers.get_register(reg) != getattr(out, side_channel_attr)
        )
        assert solver.check() == unsat


def test_tagged_calldata_pointer_derived_access_reads_readonly_source_and_clears_loaded_tag():
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.RBX, BitVecVal(0, 64))
    for i, byte in enumerate([0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]):
        state.calldata = Store(state.calldata, BitVecVal(0x18 + i, 64), BitVecVal(byte, 8))

    for insn in disassemble_hex("498bb5900000004801de488b4e18", base_addr=0):
        state = insn.to_z3(state)

    assert state.x86_registers.get_pointer_tag(Register.RSI) == PointerTag.CALLDATA_PTR
    assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.NONE
    solver = Solver()
    solver.add(state.x86_registers.get_register(Register.RCX) != BitVecVal(0x8877665544332211, 64))
    assert solver.check() == unsat


def test_derived_evm_pointer_routes_writable_domain_from_src_tag():
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.RBX, BitVecVal(0, 64))
    state.x86_memory = state.x86_memory.store_64bit(
        state.callengine_memory_base + BitVecVal(0x18, 64),
        BitVecVal(0x8877665544332211, 64),
        domain=MemoryDomain.EVM,
    )

    for insn in disassemble_hex("498b75104889d94801f1488b4118", base_addr=0):
        state = insn.to_z3(state)

    assert state.x86_registers.get_pointer_tag(Register.RSI) == PointerTag.EVM_PTR
    assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.EVM_PTR
    solver = Solver()
    solver.add(state.x86_registers.get_register(Register.RAX) != BitVecVal(0x8877665544332211, 64))
    assert solver.check() == unsat


def test_derived_stack_pointer_routes_writable_domain_for_write_and_read():
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.RBX, BitVecVal(0x10, 64))
    state.x86_registers.set_register(Register.RAX, BitVecVal(0x1122334455667788, 64))

    for insn in disassemble_hex("498b7d384889d94801f9488901488b01", base_addr=0):
        state = insn.to_z3(state)

    assert state.x86_registers.get_pointer_tag(Register.RDI) == PointerTag.STACK_PTR
    assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.STACK_PTR
    solver = Solver()
    solver.add(state.x86_registers.get_register(Register.RAX) != BitVecVal(0x1122334455667788, 64))
    assert solver.check() == unsat


def test_code_and_returndata_pointer_tags_route_readonly_sources():
    for pointer_hex, expected_tag, source_attr, payload in (
        ("498bb5a0000000", PointerTag.CODE_PTR, "code", [0xAA] * 8),
        ("498bb5b0000000", PointerTag.RETURNDATA_PTR, "return_data", [0xBB] * 8),
    ):
        state = SMTState.create_initial_state(num_inputs=0)
        array = getattr(state, source_attr)
        for i, byte in enumerate(payload):
            array = Store(array, BitVecVal(i, 64), BitVecVal(byte, 8))
        setattr(state, source_attr, array)

        for insn in disassemble_hex(pointer_hex + "488b0e", base_addr=0):
            state = insn.to_z3(state)

        assert state.x86_registers.get_pointer_tag(Register.RSI) == expected_tag
        assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.NONE
        solver = Solver()
        solver.add(state.x86_registers.get_register(Register.RCX) != BitVecVal(int.from_bytes(bytes(payload), "little"), 64))
        assert solver.check() == unsat


def test_store_through_tagged_readonly_pointer_raises():
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.RSI, state.callengine_input_pointer)
    state.x86_registers.set_pointer_tag(Register.RSI, PointerTag.CALLDATA_PTR)
    state.x86_registers.set_register(Register.RCX, BitVecVal(0x1234, 64))

    insn = disassemble_hex("48890e", base_addr=0)[0]
    with pytest.raises(MemoryDomainError):
        insn.to_z3(state)


def test_double_tag_arithmetic_clears_provenance_and_derived_deref_becomes_unrouted():
    state = SMTState.create_initial_state(num_inputs=0)

    insns = disassemble_hex("498b7510498b7d384889f14801f9488b4118", base_addr=0)
    for insn in insns[:-1]:
        state = insn.to_z3(state)

    assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.NONE
    with pytest.raises(MemoryDomainError):
        insns[-1].to_z3(state)


def test_muti_block_08_fixture_no_longer_fails_on_derived_evm_pointer_load():
    hex_data = Path("tests/data/muti_block_08.hex").read_text().strip()
    insns = disassemble_hex(hex_data, base_addr=0)

    state = SMTState.create_initial_state(num_inputs=1)
    state.x86_memory = state.x86_memory.store_64bit(
        state.x86_registers.get_register(Register.R14),
        BitVecVal(0, 64),
        domain=MemoryDomain.STACK,
    )

    for insn in insns:
        if insn.addr > 0x150A:
            break
        try:
            state = insn.to_z3(state)
        except MemoryDomainError as exc:
            pytest.fail(
                f"unexpected unrouted access before/at 0x150a: {insn.mnemonic} {insn.op_str}: {exc}"
            )

    assert state.x86_registers.get_pointer_tag(Register.RCX) == PointerTag.EVM_PTR
