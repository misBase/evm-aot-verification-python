"""Compact private details preserve every field consumed by x86 semantics/matchers."""
from dataclasses import FrozenInstanceError, fields, is_dataclass
from types import SimpleNamespace

import capstone
import pytest

from x86_64.disassembler import _InstructionDetails, disassemble_hex


def snapshot(details):
    operands = tuple((op.type, op.reg, op.size, op.imm, op.mem.segment,
                      op.mem.base, op.mem.index, op.mem.scale, op.mem.disp)
                     for op in details.operands)
    return operands, bytes(details.prefix), details.regs_access()


@pytest.mark.parametrize("hex_code", [
    "488b46c0", "488b44cbf8", "488d05f0ffffff", "b801000000", "66b80100", "b001",
    "65488b042528000000", "64488b00", "f348a5", "4899", "48f7f1", "48f7e1",
    "50", "c3", "ebfe", "49ffcf", "f30f1efa", "f048830001", "41ffe6",
    "48b8ffffffffffffffff", "0fbe00", "67488b00", "66f7f1",
])
def test_compact_details_match_capstone_fields_and_implicit_registers(hex_code):
    decoder = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    decoder.detail = True
    raw = list(decoder.disasm(bytes.fromhex(hex_code), 0x1000))
    compact = disassemble_hex(hex_code, base_addr=0x1000)
    assert len(raw) == len(compact) == 1
    assert snapshot(compact[0]._cs_insn) == snapshot(raw[0])


def test_compact_details_are_immutable_and_contain_no_capstone_objects():
    instruction = disassemble_hex("488b44cbf8")[0]
    details = instruction._cs_insn
    for obj, name in ((details, "operands"), (details.operands[0], "size"),
                      (details.operands[1].mem, "disp")):
        assert not hasattr(obj, "__dict__")
        with pytest.raises(FrozenInstanceError):
            setattr(obj, name, 99)
    pending = [details]
    while pending:
        value = pending.pop()
        if is_dataclass(value):
            pending.extend(getattr(value, field.name) for field in fields(value))
        elif isinstance(value, tuple):
            pending.extend(value)
        else:
            assert value is None or type(value) in (int, bytes)
    # Preserve identity equality of X86Instruction's former private CsInsn field.
    assert instruction != disassemble_hex("488b44cbf8")[0]


def test_regs_access_returns_independent_lists():
    details = disassemble_hex("48f7f1")[0]._cs_insn
    before = details.regs_access()
    changed = details.regs_access()
    assert all(isinstance(group, list) for group in changed)
    changed[0].clear(); changed[1].append(-1)
    assert details.regs_access() == before


def test_unsupported_regs_access_is_preserved_at_use_without_retaining_exception():
    def unavailable():
        raise capstone.CsError(capstone.CS_ERR_DETAIL)
    details = _InstructionDetails.from_capstone(SimpleNamespace(
        operands=(), prefix=[0, 0, 0, 0], regs_access=unavailable))
    with pytest.raises(capstone.CsError) as error:
        details.regs_access()
    assert error.value.errno == capstone.CS_ERR_DETAIL


@pytest.mark.parametrize("code,accepted", [
    ("498b46c0c3", True), ("65498b46c0c3", True), ("66418b46c0c3", True),
    ("4983c600c3", False),  # writing r14 must still reject the generalized slice
])
def test_shifted_slice_consumer_preserves_prefix_segment_and_register_access(code, accepted):
    from verification.block_summaries import shifted_slice
    from x86_64.cfg import identify_basic_blocks
    from x86_64.models import X86Instruction
    decoder = capstone.Cs(capstone.CS_ARCH_X86, capstone.CS_MODE_64)
    decoder.detail = True
    raw = list(decoder.disasm(bytes.fromhex(code), 0))
    original = [X86Instruction(i.address, i.mnemonic, i.op_str, bytes(i.bytes), i.size, i) for i in raw]
    compact = disassemble_hex(code)
    results = [shifted_slice(identify_basic_blocks(insns), {0}, 0, raw[0].size, -64)
               for insns in (original, compact)]
    assert (results[0] is not None) == (results[1] is not None) == accepted
    if accepted:
        assert results[0][0] == results[1][0]
