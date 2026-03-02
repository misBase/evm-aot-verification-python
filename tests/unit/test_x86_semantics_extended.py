#!/usr/bin/env python3
"""x86-64 扩展指令语义测试。"""

import pytest
from z3 import BitVecVal, simplify, is_true

from state.smt_state import SMTState
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register


def _exec_single(hex_code: str, state: SMTState) -> SMTState:
    insn = disassemble_hex(hex_code, base_addr=0x1000)[0]
    return insn.to_z3(state)


def _set_flags(state: SMTState, cf: int = 0, zf: int = 0, sf: int = 0, of: int = 0, pf: int = 0) -> None:
    state.x86_registers.set_flag("CF", BitVecVal(cf, 1))
    state.x86_registers.set_flag("ZF", BitVecVal(zf, 1))
    state.x86_registers.set_flag("SF", BitVecVal(sf, 1))
    state.x86_registers.set_flag("OF", BitVecVal(of, 1))
    state.x86_registers.set_flag("PF", BitVecVal(pf, 1))


def test_movzx_byte_ptr():
    state = SMTState()
    state.x86_registers.set_register(Register.RAX, BitVecVal(0x100, 64))
    state.x86_memory = state.x86_memory.store_byte(0x100, BitVecVal(0xAB, 8))

    # movzx rcx, byte ptr [rax]
    out = _exec_single("480fb608", state)
    assert is_true(simplify(out.x86_registers.get_register(Register.RCX) == BitVecVal(0xAB, 64)))


def test_movzx_word_ptr_and_reg_source():
    st_mem = SMTState()
    st_mem.x86_registers.set_register(Register.RAX, BitVecVal(0x180, 64))
    st_mem.x86_memory = st_mem.x86_memory.store_byte(0x180, BitVecVal(0x34, 8))
    st_mem.x86_memory = st_mem.x86_memory.store_byte(0x181, BitVecVal(0x12, 8))
    out_mem = _exec_single("0fb708", st_mem)  # movzx ecx, word ptr [rax]
    assert is_true(simplify(out_mem.x86_registers.get_register(Register.RCX) == BitVecVal(0x1234, 64)))

    st_reg = SMTState()
    st_reg.x86_registers.set_register(Register.RAX, BitVecVal(0xAB, 64))
    st_reg.x86_registers.set_register(Register.RCX, BitVecVal((1 << 64) - 1, 64))
    out_reg = _exec_single("0fb6c8", st_reg)  # movzx ecx, al
    assert is_true(simplify(out_reg.x86_registers.get_register(Register.RCX) == BitVecVal(0xAB, 64)))


def test_div_rcx_updates_rax_rdx():
    state = SMTState()
    state.x86_registers.set_register(Register.RAX, BitVecVal(10, 64))
    state.x86_registers.set_register(Register.RDX, BitVecVal(0, 64))
    state.x86_registers.set_register(Register.RCX, BitVecVal(3, 64))

    # div rcx
    out = _exec_single("48f7f1", state)
    assert is_true(simplify(out.x86_registers.get_register(Register.RAX) == BitVecVal(3, 64)))
    assert is_true(simplify(out.x86_registers.get_register(Register.RDX) == BitVecVal(1, 64)))


def test_div_memory_and_guard_paths():
    st_ok = SMTState()
    st_ok.x86_registers.set_register(Register.RAX, BitVecVal(10, 64))
    st_ok.x86_registers.set_register(Register.RDX, BitVecVal(0, 64))
    st_ok.x86_registers.set_register(Register.RBX, BitVecVal(0x400, 64))
    st_ok.x86_memory = st_ok.x86_memory.store_limb(0x400, BitVecVal(3, 64))
    out_ok = _exec_single("48f733", st_ok)  # div qword ptr [rbx]
    assert is_true(simplify(out_ok.x86_registers.get_register(Register.RAX) == BitVecVal(3, 64)))
    assert is_true(simplify(out_ok.x86_registers.get_register(Register.RDX) == BitVecVal(1, 64)))

    st_div0 = SMTState()
    st_div0.x86_registers.set_register(Register.RAX, BitVecVal(0x123, 64))
    st_div0.x86_registers.set_register(Register.RDX, BitVecVal(0x456, 64))
    st_div0.x86_registers.set_register(Register.RBX, BitVecVal(0x410, 64))
    st_div0.x86_memory = st_div0.x86_memory.store_limb(0x410, BitVecVal(0, 64))
    out_div0 = _exec_single("48f733", st_div0)
    assert is_true(simplify(out_div0.x86_registers.get_register(Register.RAX) == BitVecVal(0x123, 64)))
    assert is_true(simplify(out_div0.x86_registers.get_register(Register.RDX) == BitVecVal(0x456, 64)))

    st_over = SMTState()
    st_over.x86_registers.set_register(Register.RAX, BitVecVal(0, 64))
    st_over.x86_registers.set_register(Register.RDX, BitVecVal(1, 64))  # dividend = 2^64
    st_over.x86_registers.set_register(Register.RBX, BitVecVal(0x420, 64))
    st_over.x86_memory = st_over.x86_memory.store_limb(0x420, BitVecVal(1, 64))
    out_over = _exec_single("48f733", st_over)
    assert is_true(simplify(out_over.x86_registers.get_register(Register.RAX) == BitVecVal(0, 64)))
    assert is_true(simplify(out_over.x86_registers.get_register(Register.RDX) == BitVecVal(1, 64)))


def test_sbb_with_carry_flag():
    state = SMTState()
    state.x86_registers.set_register(Register.RAX, BitVecVal(5, 64))
    state.x86_registers.set_register(Register.RCX, BitVecVal(3, 64))
    state.x86_registers.set_flag("CF", BitVecVal(1, 1))

    # sbb rax, rcx
    out = _exec_single("4819c8", state)
    assert is_true(simplify(out.x86_registers.get_register(Register.RAX) == BitVecVal(1, 64)))
    assert is_true(simplify(out.x86_registers.get_flag("CF") == BitVecVal(0, 1)))


def test_adc_sbb_variants_reg_mem_imm():
    st_adc_mem = SMTState()
    st_adc_mem.x86_registers.set_register(Register.RAX, BitVecVal(10, 64))
    st_adc_mem.x86_registers.set_register(Register.RBX, BitVecVal(0x230, 64))
    st_adc_mem.x86_memory = st_adc_mem.x86_memory.store_limb(0x230, BitVecVal(4, 64))
    _set_flags(st_adc_mem, cf=1)
    out_adc_mem = _exec_single("481303", st_adc_mem)  # adc rax, qword ptr [rbx]
    assert is_true(simplify(out_adc_mem.x86_registers.get_register(Register.RAX) == BitVecVal(15, 64)))

    st_adc_reg = SMTState()
    st_adc_reg.x86_registers.set_register(Register.RAX, BitVecVal(10, 64))
    st_adc_reg.x86_registers.set_register(Register.RCX, BitVecVal(20, 64))
    _set_flags(st_adc_reg, cf=1)
    out_adc_reg = _exec_single("4811c8", st_adc_reg)  # adc rax, rcx
    assert is_true(simplify(out_adc_reg.x86_registers.get_register(Register.RAX) == BitVecVal(31, 64)))

    st_adc_imm = SMTState()
    st_adc_imm.x86_registers.set_register(Register.RAX, BitVecVal((1 << 64) - 1, 64))
    _set_flags(st_adc_imm, cf=1)
    out_adc_imm = _exec_single("4883d001", st_adc_imm)  # adc rax, 1
    assert is_true(simplify(out_adc_imm.x86_registers.get_register(Register.RAX) == BitVecVal(1, 64)))
    assert is_true(simplify(out_adc_imm.x86_registers.get_flag("CF") == BitVecVal(1, 1)))

    st_sbb_mem = SMTState()
    st_sbb_mem.x86_registers.set_register(Register.RAX, BitVecVal(10, 64))
    st_sbb_mem.x86_registers.set_register(Register.RBX, BitVecVal(0x240, 64))
    st_sbb_mem.x86_memory = st_sbb_mem.x86_memory.store_limb(0x240, BitVecVal(4, 64))
    _set_flags(st_sbb_mem, cf=1)
    out_sbb_mem = _exec_single("481b03", st_sbb_mem)  # sbb rax, qword ptr [rbx]
    assert is_true(simplify(out_sbb_mem.x86_registers.get_register(Register.RAX) == BitVecVal(5, 64)))

    st_sbb_imm = SMTState()
    st_sbb_imm.x86_registers.set_register(Register.RAX, BitVecVal(0, 64))
    _set_flags(st_sbb_imm, cf=1)
    out_sbb_imm = _exec_single("4883d800", st_sbb_imm)  # sbb rax, 0
    assert is_true(simplify(out_sbb_imm.x86_registers.get_register(Register.RAX) == BitVecVal((1 << 64) - 1, 64)))
    assert is_true(simplify(out_sbb_imm.x86_registers.get_flag("CF") == BitVecVal(1, 1)))


def test_shift_by_cl():
    # shl rbx, cl
    st1 = SMTState()
    st1.x86_registers.set_register(Register.RBX, BitVecVal(1, 64))
    st1.x86_registers.set_register(Register.RCX, BitVecVal(1, 64))
    out1 = _exec_single("48d3e3", st1)
    assert is_true(simplify(out1.x86_registers.get_register(Register.RBX) == BitVecVal(2, 64)))

    # shr rbx, cl
    st2 = SMTState()
    st2.x86_registers.set_register(Register.RBX, BitVecVal(8, 64))
    st2.x86_registers.set_register(Register.RCX, BitVecVal(1, 64))
    out2 = _exec_single("48d3eb", st2)
    assert is_true(simplify(out2.x86_registers.get_register(Register.RBX) == BitVecVal(4, 64)))


def test_shift_memory_and_count_zero_flags_unchanged():
    st_mem_l = SMTState()
    st_mem_l.x86_registers.set_register(Register.RAX, BitVecVal(0x260, 64))
    st_mem_l.x86_memory = st_mem_l.x86_memory.store_limb(0x260, BitVecVal(2, 64))
    out_mem_l = _exec_single("48d120", st_mem_l)  # shl qword ptr [rax], 1
    assert is_true(simplify(out_mem_l.x86_memory.load_limb(BitVecVal(0x260, 64)) == BitVecVal(4, 64)))

    st_mem_r = SMTState()
    st_mem_r.x86_registers.set_register(Register.RAX, BitVecVal(0x270, 64))
    st_mem_r.x86_memory = st_mem_r.x86_memory.store_limb(0x270, BitVecVal(8, 64))
    out_mem_r = _exec_single("48d128", st_mem_r)  # shr qword ptr [rax], 1
    assert is_true(simplify(out_mem_r.x86_memory.load_limb(BitVecVal(0x270, 64)) == BitVecVal(4, 64)))

    st_zero = SMTState()
    st_zero.x86_registers.set_register(Register.RAX, BitVecVal(5, 64))
    _set_flags(st_zero, cf=1, zf=0, sf=1, of=1)
    out_zero = _exec_single("48c1e000", st_zero)  # shl rax, 0
    assert is_true(simplify(out_zero.x86_registers.get_register(Register.RAX) == BitVecVal(5, 64)))
    assert is_true(simplify(out_zero.x86_registers.get_flag("CF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_zero.x86_registers.get_flag("OF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_zero.x86_registers.get_flag("ZF") == BitVecVal(0, 1)))
    assert is_true(simplify(out_zero.x86_registers.get_flag("SF") == BitVecVal(1, 1)))


def test_not_register_and_memory():
    st_reg = SMTState()
    st_reg.x86_registers.set_register(Register.RAX, BitVecVal(0, 64))
    out_reg = _exec_single("48f7d0", st_reg)  # not rax
    assert is_true(simplify(out_reg.x86_registers.get_register(Register.RAX) == BitVecVal((1 << 64) - 1, 64)))

    st_mem = SMTState()
    st_mem.x86_registers.set_register(Register.RAX, BitVecVal(0x200, 64))
    st_mem.x86_memory = st_mem.x86_memory.store_limb(0x200, BitVecVal(0x0F0F0F0F0F0F0F0F, 64))
    out_mem = _exec_single("48f710", st_mem)  # not qword ptr [rax]
    assert is_true(
        simplify(out_mem.x86_memory.load_limb(BitVecVal(0x200, 64)) == BitVecVal(0xF0F0F0F0F0F0F0F0, 64))
    )


def test_bswap_rax():
    state = SMTState()
    state.x86_registers.set_register(Register.RAX, BitVecVal(0x1122334455667788, 64))

    # bswap rax
    out = _exec_single("480fc8", state)
    assert is_true(simplify(out.x86_registers.get_register(Register.RAX) == BitVecVal(0x8877665544332211, 64)))


def test_mul_memory_and_flags():
    st_small = SMTState()
    st_small.x86_registers.set_register(Register.RAX, BitVecVal(3, 64))
    st_small.x86_registers.set_register(Register.RBX, BitVecVal(0x280, 64))
    st_small.x86_memory = st_small.x86_memory.store_limb(0x280, BitVecVal(5, 64))
    out_small = _exec_single("48f723", st_small)  # mul qword ptr [rbx]
    assert is_true(simplify(out_small.x86_registers.get_register(Register.RAX) == BitVecVal(15, 64)))
    assert is_true(simplify(out_small.x86_registers.get_register(Register.RDX) == BitVecVal(0, 64)))
    assert is_true(simplify(out_small.x86_registers.get_flag("CF") == BitVecVal(0, 1)))
    assert is_true(simplify(out_small.x86_registers.get_flag("OF") == BitVecVal(0, 1)))

    st_big = SMTState()
    st_big.x86_registers.set_register(Register.RAX, BitVecVal(1 << 63, 64))
    st_big.x86_registers.set_register(Register.RBX, BitVecVal(0x290, 64))
    st_big.x86_memory = st_big.x86_memory.store_limb(0x290, BitVecVal(2, 64))
    out_big = _exec_single("48f723", st_big)
    assert is_true(simplify(out_big.x86_registers.get_register(Register.RAX) == BitVecVal(0, 64)))
    assert is_true(simplify(out_big.x86_registers.get_register(Register.RDX) == BitVecVal(1, 64)))
    assert is_true(simplify(out_big.x86_registers.get_flag("CF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_big.x86_registers.get_flag("OF") == BitVecVal(1, 1)))


def test_adc_sub_cmp_and_immediate_or_register():
    st_adc = SMTState()
    st_adc.x86_registers.set_register(Register.RAX, BitVecVal((1 << 64) - 1, 64))
    st_adc.x86_registers.set_flag("CF", BitVecVal(1, 1))
    out_adc = _exec_single("4883d000", st_adc)  # adc rax, 0
    assert is_true(simplify(out_adc.x86_registers.get_register(Register.RAX) == BitVecVal(0, 64)))
    assert is_true(simplify(out_adc.x86_registers.get_flag("CF") == BitVecVal(1, 1)))

    st_sub = SMTState()
    st_sub.x86_registers.set_register(Register.RAX, BitVecVal(5, 64))
    st_sub.x86_registers.set_register(Register.RCX, BitVecVal(3, 64))
    out_sub = _exec_single("4829c8", st_sub)  # sub rax, rcx
    assert is_true(simplify(out_sub.x86_registers.get_register(Register.RAX) == BitVecVal(2, 64)))

    st_cmp = SMTState()
    st_cmp.x86_registers.set_register(Register.RAX, BitVecVal(3, 64))
    st_cmp.x86_registers.set_register(Register.RCX, BitVecVal(5, 64))
    out_cmp = _exec_single("4839c8", st_cmp)  # cmp rax, rcx
    assert is_true(simplify(out_cmp.x86_registers.get_flag("CF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_cmp.x86_registers.get_flag("ZF") == BitVecVal(0, 1)))

    st_and = SMTState()
    st_and.x86_registers.set_register(Register.RAX, BitVecVal(3, 64))
    out_and = _exec_single("4883e001", st_and)  # and rax, 1
    assert is_true(simplify(out_and.x86_registers.get_register(Register.RAX) == BitVecVal(1, 64)))


def test_sub_cmp_or_xor_memory_and_immediate_variants():
    st_sub_mem = SMTState()
    st_sub_mem.x86_registers.set_register(Register.RAX, BitVecVal(9, 64))
    st_sub_mem.x86_registers.set_register(Register.RBX, BitVecVal(0x2A0, 64))
    st_sub_mem.x86_memory = st_sub_mem.x86_memory.store_limb(0x2A0, BitVecVal(4, 64))
    out_sub_mem = _exec_single("482b03", st_sub_mem)  # sub rax, qword ptr [rbx]
    assert is_true(simplify(out_sub_mem.x86_registers.get_register(Register.RAX) == BitVecVal(5, 64)))

    st_sub_imm = SMTState()
    st_sub_imm.x86_registers.set_register(Register.RAX, BitVecVal(9, 64))
    out_sub_imm = _exec_single("4883e802", st_sub_imm)  # sub rax, 2
    assert is_true(simplify(out_sub_imm.x86_registers.get_register(Register.RAX) == BitVecVal(7, 64)))

    st_cmp_mem = SMTState()
    st_cmp_mem.x86_registers.set_register(Register.RAX, BitVecVal(5, 64))
    st_cmp_mem.x86_registers.set_register(Register.RBX, BitVecVal(0x2B0, 64))
    st_cmp_mem.x86_memory = st_cmp_mem.x86_memory.store_limb(0x2B0, BitVecVal(5, 64))
    out_cmp_mem = _exec_single("483b03", st_cmp_mem)  # cmp rax, qword ptr [rbx]
    assert is_true(simplify(out_cmp_mem.x86_registers.get_flag("ZF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_cmp_mem.x86_registers.get_flag("CF") == BitVecVal(0, 1)))

    st_cmp_imm = SMTState()
    st_cmp_imm.x86_registers.set_register(Register.RAX, BitVecVal(3, 64))
    out_cmp_imm = _exec_single("4883f805", st_cmp_imm)  # cmp rax, 5
    assert is_true(simplify(out_cmp_imm.x86_registers.get_flag("CF") == BitVecVal(1, 1)))
    assert is_true(simplify(out_cmp_imm.x86_registers.get_flag("ZF") == BitVecVal(0, 1)))

    st_or = SMTState()
    st_or.x86_registers.set_register(Register.RAX, BitVecVal(0, 64))
    out_or = _exec_single("4883c802", st_or)  # or rax, 2
    assert is_true(simplify(out_or.x86_registers.get_register(Register.RAX) == BitVecVal(2, 64)))
    assert is_true(simplify(out_or.x86_registers.get_flag("ZF") == BitVecVal(0, 1)))

    st_xor = SMTState()
    st_xor.x86_registers.set_register(Register.RAX, BitVecVal(3, 64))
    out_xor = _exec_single("4883f003", st_xor)  # xor rax, 3
    assert is_true(simplify(out_xor.x86_registers.get_register(Register.RAX) == BitVecVal(0, 64)))
    assert is_true(simplify(out_xor.x86_registers.get_flag("ZF") == BitVecVal(1, 1)))


def test_setcc_register_and_memory():
    st_reg = SMTState()
    st_reg.x86_registers.set_register(Register.RAX, BitVecVal(0x12340000000000FF, 64))
    st_reg.x86_registers.set_flag("ZF", BitVecVal(1, 1))
    out_reg = _exec_single("0f94c0", st_reg)  # sete al
    assert is_true(simplify(out_reg.x86_registers.get_register(Register.RAX) == BitVecVal(0x1234000000000001, 64)))

    st_ae = SMTState()
    st_ae.x86_registers.set_register(Register.RAX, BitVecVal(0xABCD0000000000FF, 64))
    st_ae.x86_registers.set_flag("CF", BitVecVal(0, 1))
    out_ae = _exec_single("0f93c0", st_ae)  # setae al
    assert is_true(simplify(out_ae.x86_registers.get_register(Register.RAX) == BitVecVal(0xABCD000000000001, 64)))

    st_mem = SMTState()
    st_mem.x86_registers.set_register(Register.RAX, BitVecVal(0x300, 64))
    st_mem.x86_registers.set_flag("ZF", BitVecVal(1, 1))
    out_mem = _exec_single("0f9400", st_mem)  # sete byte ptr [rax]
    assert is_true(simplify(out_mem.x86_memory.load_byte(BitVecVal(0x300, 64)) == BitVecVal(1, 8)))


@pytest.mark.parametrize(
    "hex_code,true_flags,false_flags",
    [
        ("0f92c0", {"cf": 1}, {"cf": 0}),                 # setb
        ("0f93c0", {"cf": 0}, {"cf": 1}),                 # setae
        ("0f97c0", {"cf": 0, "zf": 0}, {"cf": 1, "zf": 0}),  # seta
        ("0f96c0", {"cf": 1, "zf": 0}, {"cf": 0, "zf": 0}),  # setbe
        ("0f94c0", {"zf": 1}, {"zf": 0}),                 # sete
        ("0f95c0", {"zf": 0}, {"zf": 1}),                 # setne
        ("0f9cc0", {"sf": 1, "of": 0}, {"sf": 0, "of": 0}),  # setl
        ("0f9dc0", {"sf": 0, "of": 0}, {"sf": 1, "of": 0}),  # setge
        ("0f9ec0", {"zf": 1, "sf": 0, "of": 0}, {"zf": 0, "sf": 0, "of": 0}),  # setle
        ("0f9fc0", {"zf": 0, "sf": 0, "of": 0}, {"zf": 1, "sf": 0, "of": 0}),  # setg
        ("0f98c0", {"sf": 1}, {"sf": 0}),                 # sets
        ("0f99c0", {"sf": 0}, {"sf": 1}),                 # setns
    ],
)
def test_setcc_condition_matrix(hex_code: str, true_flags: dict, false_flags: dict):
    st_true = SMTState()
    st_true.x86_registers.set_register(Register.RAX, BitVecVal(0xDEAD0000000000FF, 64))
    _set_flags(st_true)
    _set_flags(st_true, **true_flags)
    out_true = _exec_single(hex_code, st_true)
    assert is_true(simplify(out_true.x86_registers.get_register(Register.RAX) == BitVecVal(0xDEAD000000000001, 64)))

    st_false = SMTState()
    st_false.x86_registers.set_register(Register.RAX, BitVecVal(0xBEEF0000000000FF, 64))
    _set_flags(st_false)
    _set_flags(st_false, **false_flags)
    out_false = _exec_single(hex_code, st_false)
    assert is_true(simplify(out_false.x86_registers.get_register(Register.RAX) == BitVecVal(0xBEEF000000000000, 64)))


def test_setcc_memory_only_writes_one_byte():
    st = SMTState()
    st.x86_registers.set_register(Register.RAX, BitVecVal(0x350, 64))
    st.x86_memory = st.x86_memory.store_byte(0x350, BitVecVal(0xAA, 8))
    st.x86_memory = st.x86_memory.store_byte(0x351, BitVecVal(0xBB, 8))
    _set_flags(st, zf=1)
    out = _exec_single("0f9500", st)  # setne byte ptr [rax], ZF=1 => 0
    assert is_true(simplify(out.x86_memory.load_byte(BitVecVal(0x350, 64)) == BitVecVal(0, 8)))
    assert is_true(simplify(out.x86_memory.load_byte(BitVecVal(0x351, 64)) == BitVecVal(0xBB, 8)))
