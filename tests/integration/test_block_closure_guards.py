"""Actual edge mutations, not merely candidate/table integrity tests."""
import pytest
from z3 import BitVecVal, Store

from tests.integration.test_block_program import load
from verification.block_program import BlockProgramVerifier
from verification.cutpoint_relation import write_evm_word
from state.x86_state import MemoryDomain
from x86_64.models import Register


@pytest.fixture(scope="module")
def baseline():
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load())
    assert r.verified, r.message
    candidates = {}
    for s in r.certificate.specializations:
        candidates.setdefault(s.pc, []).append(s)
    return candidates


@pytest.mark.parametrize("change", ["msize", "fmp", "mirror", "domain", "running"])
def test_actual_successor_relation_is_checked(baseline, monkeypatch, change):
    import verification.block_equivalence as be
    from z3 import Lambda, Select, BitVec
    real_e, real_x = be.run_evm_segment, be.run_x86_segment
    def corrupt(state, side):
        if change == "msize":
            if side == "evm": state.evm_memory.MSize += 32
            else: state.callengine_memory_size_bytes += 32
        if change == "fmp":
            if side == "evm": state.evm_memory.Memory = write_evm_word(state.evm_memory.Memory, 0x40, 0xdead)
            else:
                r15 = state.x86_registers.get_register(Register.R15)
                # EVM words are big endian in the byte memory domain.
                for index in range(32):
                    byte = (0xdead >> (8 * (31-index))) & 255
                    state.x86_memory = state.x86_memory.store_byte(r15 + 0x40 + index, BitVecVal(byte, 8), domain=MemoryDomain.EVM)
        if change == "mirror" and side == "x86":
            address = state.x86_registers.get_register(Register.R13) + 0x30
            state.x86_memory = state.x86_memory.store_limb(address, state.callengine_stack_byte_offset + 32, domain=MemoryDomain.CALLENGINE)
        if change == "domain":
            if side == "evm": state.evm_memory.MSize = BitVecVal(1, 64)
            else: state.callengine_memory_size_bytes = BitVecVal(1, 64)
        if change == "running" and side == "x86": state.callengine_status_code = BitVecVal(255, 8)
    def evm(*args, **kwargs):
        paths, defects = real_e(*args, **kwargs)
        for p in paths:
            if p.kind != "terminal": corrupt(p.state, "evm")
        return paths, defects
    def x86(*args, **kwargs):
        paths, defects, notes = real_x(*args, **kwargs)
        for p in paths:
            if p.kind != "terminal": corrupt(p.state, "x86")
        return paths, defects, notes
    monkeypatch.setattr(be, "run_evm_segment", evm)
    monkeypatch.setattr(be, "run_x86_segment", x86)
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load(), candidates=baseline)
    assert not r.verified, r.message
    assert "H2" in r.message, r.message


def test_body_and_configuration_changes_invalidate_consumption():
    r = BlockProgramVerifier(timeout_ms=3000).verify_program_pair(*load())
    assert r.verified
    original = r._prover.compare_gas
    r._prover.compare_gas = not original
    assert not r.verified
    r._prover.compare_gas = original
    assert r.verified
    instruction = r._prover.x86_blocks[-1].instructions[-1]
    instruction.op_str += " changed"
    assert not r.verified
