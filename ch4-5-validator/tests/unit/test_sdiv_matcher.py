"""Signed DIV candidates preserve opcode boundaries and model every memory effect."""
from dataclasses import replace

import pytest
from z3 import BitVecVal, Bool, BoolVal, If, simplify, substitute

from state.smt_state import MemoryDomain, SMTState
from state.x86_state import PointerTag
from tests.integration.test_single_ins_equivalence import X86_SDIV_CORE_HEX_SEQUENCE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries.base import SummaryPreconditionError
from x86_64.summaries.sdiv import SDivSummarySpec, apply_sdiv_summary, discover_sdiv_summaries


def _candidate(code=X86_SDIV_CORE_HEX_SEQUENCE, base=0):
    blocks = identify_basic_blocks(disassemble_hex(code, base))
    [summary] = discover_sdiv_summaries(blocks, strict=True)
    return summary


def _value(expr, took=None, choice=False):
    if took is not None:
        expr = substitute(expr, (took, BoolVal(choice)))
    return simplify(expr).as_long()


def test_complete_signed_div_matcher_stops_before_epilogue():
    summary = _candidate()
    p = summary.payload
    assert (summary.entry_addr, p.continuation_addr) == (0, 0x56B)
    assert p.dividend_offsets == (-32, -24, -16, -8)
    assert p.divisor_offsets == (-64, -56, -48, -40)
    assert tuple(d.entry_addr for d in p.divs) == (0x65, 0x18A, 0x329, 0x44E)
    assert len({d.resume_addr for d in p.divs}) == 4


def test_relocated_padded_signed_div_is_not_address_specific():
    summary = _candidate("90" + X86_SDIV_CORE_HEX_SEQUENCE, 0x10000)
    assert summary.entry_addr == 0x10001
    assert summary.payload.continuation_addr == 0x1056C
    assert tuple(d.entry_addr for d in summary.payload.divs) == (0x10066, 0x1018B, 0x1032A, 0x1044F)


def test_mismatched_outer_sign_target_is_not_a_candidate():
    broken = X86_SDIV_CORE_HEX_SEQUENCE.replace("0f8548020000", "0f8549020000", 1)
    assert broken != X86_SDIV_CORE_HEX_SEQUENCE
    assert discover_sdiv_summaries(identify_basic_blocks(disassemble_hex(broken))) == []


@pytest.mark.parametrize("x,y,quotient", [
    (17, 5, 3), (17, -5, -3), (-17, -5, 3), (-17, 5, -3),
    (-17, 0, 0), (0, -5, 0),
])
def test_signed_apply_reads_original_inputs_and_updates_both_slots(x, y, quotient):
    p = _candidate().payload
    state = SMTState()
    r13, r14 = BitVecVal(0x2000, 64), BitVecVal(0x1000, 64)
    state.x86_registers.set_register(Register.R13, r13)
    state.x86_registers.set_register(Register.R14, r14)
    state.x86_memory = state.x86_memory.store_256bit(r14 - 32, BitVecVal(x, 256), domain=MemoryDomain.STACK)
    state.x86_memory = state.x86_memory.store_256bit(r14 - 64, BitVecVal(y, 256), domain=MemoryDomain.STACK)
    state.x86_memory = state.x86_memory.store_64bit(r14 + 32, BitVecVal(0xCAFE, 64), domain=MemoryDomain.STACK)
    state.x86_memory = state.x86_memory.store_64bit(r13 + 0x100, BitVecVal(0x55, 64), domain=MemoryDomain.CALLENGINE)
    new, took = apply_sdiv_summary(p, state, fresh_prefix="test_sdiv")
    assert _value(new.x86_memory.load_256bit(r14 - 32, domain=MemoryDomain.STACK)) == abs(x)
    assert _value(new.x86_memory.load_256bit(r14 - 64, domain=MemoryDomain.STACK)) == quotient % (1 << 256)
    assert _value(new.x86_memory.load_64bit(r14 + 32, domain=MemoryDomain.STACK)) == 0xCAFE
    assert _value(new.x86_memory.load_64bit(r13 + 0x100, domain=MemoryDomain.CALLENGINE)) == 0x55
    assert new.x86_memory.evm_mem.eq(state.x86_memory.evm_mem)
    branch = 2 if x < 0 and y < 0 else 3 if x < 0 else 1 if y < 0 else 0
    assert _value(new.callengine_return_address, took, True) == p.divs[branch].resume_addr
    assert _value(new.x86_memory.load_64bit(r13 + 0xF0, domain=MemoryDomain.CALLENGINE), took, True) == p.divs[branch].resume_addr
    assert _value(new.callengine_return_address, took, False) == _value(state.callengine_return_address)
    assert _value(new.callengine_stack_pointer_limbs, took, True) == (p.divs[branch].builtin_stack_pointer - 4) % (1 << 64)


def test_wrong_pointer_provenance_is_rejected_before_proof(monkeypatch):
    summary = _candidate()
    state = SMTState()
    state.x86_registers.set_pointer_tag(Register.R11, PointerTag.EVM_PTR)
    spec = SDivSummarySpec()
    monkeypatch.setattr(spec, "lemma", lambda summary: pytest.fail("pointer gate must run first"))
    with pytest.raises(SummaryPreconditionError, match="r11 pointer tag"):
        spec.apply(summary, state, fresh_prefix="invalid")


def test_candidate_preserves_the_four_independent_bridge_payloads():
    p = _candidate().payload
    divs = tuple(replace(d, builtin_stack_pointer=8 * k) for k, d in enumerate(p.divs))
    changed = replace(p, divs=divs)
    state = SMTState()
    r14 = BitVecVal(0, 64)
    state.x86_registers.set_register(Register.R14, r14)
    state.x86_memory = state.x86_memory.store_256bit(r14 - 32, BitVecVal(-17, 256), domain=MemoryDomain.STACK)
    state.x86_memory = state.x86_memory.store_256bit(r14 - 64, BitVecVal(5, 256), domain=MemoryDomain.STACK)
    new, took = apply_sdiv_summary(changed, state, fresh_prefix="branch")
    assert _value(new.callengine_stack_pointer_limbs, took, True) == 20


def test_builtin_choice_does_not_alias_an_existing_input_name():
    state = SMTState()
    occupied = Bool("collision_0_builtin")
    state.x86_registers.set_register(Register.R11, If(occupied, BitVecVal(1, 64), BitVecVal(0, 64)))
    _, took = apply_sdiv_summary(_candidate().payload, state, fresh_prefix="collision")
    assert not took.eq(occupied)


def test_builtin_choice_skips_a_fresh_name_occupied_only_in_the_premise(monkeypatch):
    import common.fresh_symbols as fresh
    original = fresh.FreshConst
    occupied = Bool("premise_only!123")
    attempted = []

    def collision_first(sort, prefix):
        attempted.append(prefix)
        return occupied if len(attempted) == 1 else original(sort, prefix)

    monkeypatch.setattr(fresh, "FreshConst", collision_first)
    _, took = apply_sdiv_summary(_candidate().payload, SMTState(), fresh_prefix="collision",
                                 path_condition=occupied)
    assert len(attempted) >= 2
    assert not took.eq(occupied)


def test_inconclusive_slice_proof_is_a_rejected_precondition(monkeypatch):
    from x86_64.summaries.signed_proof import SignedProofError

    summary = _candidate()
    spec = SDivSummarySpec()

    def inconclusive(summary):
        raise SignedProofError(summary.entry_addr, "effect_4", "solver=unknown")

    monkeypatch.setattr(spec, "lemma", inconclusive)
    with pytest.raises(SummaryPreconditionError, match="solver=unknown") as error:
        spec.apply(summary, SMTState(), fresh_prefix="rejected")
    assert error.value.result == "inconclusive"
    assert isinstance(error.value.__cause__, SignedProofError)


def test_slice_budget_exhaustion_is_not_caught_as_a_precondition(monkeypatch):
    from verification.block_equivalence import ProofBudgetExceeded

    spec = SDivSummarySpec()

    def exhausted(summary):
        raise ProofBudgetExceeded("test budget")

    monkeypatch.setattr(spec, "lemma", exhausted)
    with pytest.raises(ProofBudgetExceeded, match="test budget"):
        spec.apply(_candidate(), SMTState(), fresh_prefix="budget")
