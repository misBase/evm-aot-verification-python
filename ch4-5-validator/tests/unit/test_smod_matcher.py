"""SMOD candidates retain whole-state effects and never assume an initial sign flag."""
from dataclasses import replace

import pytest
from z3 import BitVec, BitVecVal, Bool, BoolSort, FreshConst, Not, Solver, is_true, simplify, unsat

from common.arithmetic import _abs256, smod_semantics
from common.uint256 import Uint256
from state.smt_state import MemoryDomain, SMTState
from state.x86_state import PointerTag
from tests.integration.test_single_ins_equivalence import X86_SMOD_CORE_HEX_SEQUENCE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries.base import SummaryMatchError, SummaryPreconditionError
from x86_64.summaries.smod import (
    SMOD_SIGN_OFFSET, SModSummarySpec, apply_smod_summary,
    builtin_taken_condition, discover_smod_summaries,
)

RESET = '49c7850001000000000000'
CODE = RESET + X86_SMOD_CORE_HEX_SEQUENCE


def blocks(code=CODE):
    return identify_basic_blocks(disassemble_hex(code, 0))


def summary():
    [result] = discover_smod_summaries(blocks(), strict=True)
    return result


def configured(x, y, old_sign=7):
    s = summary();state = SMTState()
    regs = state.x86_registers
    regs.set_register(Register.R14, state.callengine_stack_base + state.callengine_stack_byte_offset)
    regs.set_register(Register.R15, state.callengine_memory_base)
    r14, r13 = regs.get_register(Register.R14), regs.get_register(Register.R13)
    for offsets, value in ((s.payload.dividend_offsets,x),(s.payload.divisor_offsets,y)):
        state.x86_memory = state.x86_memory.store_256bit(r14 + BitVecVal(offsets[0],64),BitVecVal(value % (1<<256),256),domain=MemoryDomain.STACK)
    state.x86_memory = state.x86_memory.store_limb(r13+BitVecVal(SMOD_SIGN_OFFSET,64),BitVecVal(old_sign,64),domain=MemoryDomain.CALLENGINE)
    return s,state


def word(state, offsets):
    r14 = state.x86_registers.get_register(Register.R14)
    return simplify(Uint256(*(state.x86_memory.load_limb(r14+BitVecVal(o,64),domain=MemoryDomain.STACK) for o in offsets)).to_bv256())


def test_reset_smod_matcher_recovers_complete_operand_and_builtin_layout():
    s = summary();p = s.payload
    assert s.kind == 'smod' and p.entry_addr == 0 and p.start_instruction_index == 0
    assert p.dividend_offsets == (-32,-24,-16,-8) and p.divisor_offsets == (-64,-56,-48,-40)
    assert p.inner_mod.builtin_index == 5 and p.inner_mod.builtin_stack_pointer == 0
    assert p.inner_mod.entry_addr < p.inner_mod.resume_addr < p.continuation_addr
    assert set(p.clobber_registers) == {Register.RAX,Register.RBX,Register.RCX,Register.RDX,Register.RDI}


def test_old_smod_without_reset_and_reset_to_one_are_rejected():
    assert discover_smod_summaries(blocks(X86_SMOD_CORE_HEX_SEQUENCE),strict=True) == []
    assert discover_smod_summaries(blocks((RESET[:-8]+'01000000')+X86_SMOD_CORE_HEX_SEQUENCE)) == []


@pytest.mark.parametrize('old,new',[
    ('41c785e400000005000000','41c785e400000004000000'),
    ('498956c0','498946c0'),
])
def test_wrong_mod_builtin_or_wrong_remainder_register_is_not_a_match(old,new):
    altered=CODE.replace(old,new,1)
    assert altered != CODE
    with pytest.raises(SummaryMatchError):discover_smod_summaries(blocks(altered),strict=True)


def test_external_entry_into_inner_mod_is_rejected():
    original=blocks();s=summary();target=s.payload.inner_mod.resume_addr
    source=0x4000;code='e9'+(target-source-5).to_bytes(4,'little',signed=True).hex()
    combined=original+identify_basic_blocks(disassemble_hex(code,source))
    with pytest.raises(SummaryMatchError):discover_smod_summaries(combined,strict=True)


@pytest.mark.parametrize('x,y',[(17,5),(-17,5),(17,-5),(-17,-5),(0,5),(17,0),(-(1<<255),-1)])
@pytest.mark.parametrize('old_sign',[0,1])
def test_apply_matches_shared_smod_semantics_and_writes_abs_popped_slot(x,y,old_sign):
    s,state=configured(x,y,old_sign)
    new,took=apply_smod_summary(s.payload,state,fresh_prefix='smod_apply')
    vx,vy=BitVecVal(x%(1<<256),256),BitVecVal(y%(1<<256),256)
    solver=Solver();solver.add(word(new,s.payload.divisor_offsets)!=smod_semantics(vx,vy));assert solver.check()==unsat
    solver=Solver();solver.add(word(new,s.payload.dividend_offsets)!=_abs256(vx));assert solver.check()==unsat
    r13=state.x86_registers.get_register(Register.R13)
    sign=simplify(new.x86_memory.load_limb(r13+BitVecVal(SMOD_SIGN_OFFSET,64),domain=MemoryDomain.CALLENGINE))
    assert sign.as_long()==int(x<0)
    assert state.assumptions == new.assumptions
    # The original state is not mutated by the proposal.
    assert word(state,s.payload.dividend_offsets).eq(vx)


@pytest.mark.parametrize('x,y,expected',[(17,5,False),(0,5,False),(5,5,False),(5,17,False),((1<<200),5,True),((1<<200),0,False)])
def test_unsigned_mod_builtin_witness_matches_all_shortcuts(x,y,expected):
    assert is_true(simplify(builtin_taken_condition(Uint256.from_int(x),Uint256.from_int(y))))==expected


def test_took_symbol_is_disjoint_from_a_name_occurring_only_in_the_path():
    s,state=configured(17,5)
    prefix=f'fresh_path_{s.payload.entry_addr:x}_builtin'
    probe=FreshConst(BoolSort(),prefix);serial=int(str(probe.decl().name()).rsplit('!',1)[1])+1
    foreign=Bool(prefix+'!'+str(serial))
    _,took=apply_smod_summary(s.payload,state,fresh_prefix='fresh_path',path_condition=foreign)
    assert not took.eq(foreign)


@pytest.mark.parametrize('field',['assumptions','summary_assumed_premises'])
def test_took_symbol_is_disjoint_from_names_only_in_state_premises(field):
    s,state=configured(17,5)
    prefix=f'fresh_state_{s.payload.entry_addr:x}_builtin'
    probe=FreshConst(BoolSort(),prefix);serial=int(str(probe.decl().name()).rsplit('!',1)[1])+1
    foreign=Bool(prefix+'!'+str(serial))
    setattr(state,field,[foreign])
    _,took=apply_smod_summary(s.payload,state,fresh_prefix='fresh_state',path_condition=None)
    assert not took.eq(foreign)
    assert getattr(state,field)[0].eq(foreign)


def test_spec_rejects_pointer_tags_and_propagates_raw_proof_failure(monkeypatch):
    s,state=configured(17,5);spec=SModSummarySpec()
    def refuse(*args):raise RuntimeError('raw signed proof refused')
    monkeypatch.setattr(spec,'lemma',refuse)
    with pytest.raises(RuntimeError,match='raw signed proof refused'):
        spec.apply(s,state,fresh_prefix='not_certified')
    state.x86_registers.set_pointer_tag(Register.RAX,PointerTag.EVM_PTR)
    with pytest.raises(SummaryPreconditionError,match='pointer tag'):
        spec.apply(s,state,fresh_prefix='not_certified')


# Exact bytes from authoritative frozen r5 PoolManager, including the preceding block prefix.
R5_SMOD = (
    '498b8ea0000000498bbea80000004d8b86b00000004d8b8eb80000004989c24989d34989dc498986a00000004889f0498996a80000004c89d249899e'
    'b00000004c89db4989b6b80000004c89e649898ec00000004889c14989bec8000000498bbec00000004d8986d00000004d8b86c80000004d898ed800'
    '00004d8b8ed00000004d8996e00000004d8b96d80000004d899ee80000004d89a6f0000000498986f800000049c786000100000000000049c7860801'
    '00000000000049c786100100000000000049c78618010000000000004989962001000049899e280100004989b63001000049898e380100004989be40'
    '0100004d8986480100004d898e500100004d89965801000049c785000100000000000048c7c000000000490b8640010000490b8648010000490b8650'
    '010000490b86580100004885c07471498b865801000048c1e83f66904885c0745f49c785000100000100000048c7c000000000492b86400100004989'
    '864001000048c7c000000000491b86480100004989864801000048c7c000000000491b86500100004989865001000048c7c000000000491b86580100'
    '004989865801000048c7c000000000490b8620010000490b8628010000490b8630010000490b86380100004885c07464498b863801000048c1e83f48'
    '85c0745448c7c000000000492b86200100004989862001000048c7c000000000491b86280100004989862801000048c7c000000000491b8630010000'
    '4989863001000048c7c000000000491b8638010000498986380100004889c148c7c300000000490b9e40010000490b9e48010000490b9e5001000049'
    '0b9e580100004885db0f84b601000048c7c300000000490b9e20010000490b9e28010000490b9e30010000490b9e380100004885db0f848a01000049'
    '8b9e40010000492b9e20010000498b9e48010000491b9e28010000498b9e50010000491b9e30010000498b9e580100000f1f4000491b9e3801000073'
    '3d498b9e4001000049899e20010000498b9e4801000049899e28010000498b9e5001000049899e30010000498b9e5801000049899e38010000e93b01'
    '0000498b9e20010000492b9e40010000498b9e28010000491b9e48010000498b9e30010000491b9e50010000498b9e38010000660f1f840000000000'
    '491b9e58010000723149c786200100000000000049c786280100000000000049c786300100000000000049c7863801000000000000e9c700000048c7'
    'c300000000490b9e48010000490b9e50010000490b9e580100004885db754248c7c200000000498b8640010000498b9e2001000048f7f34989962001'
    '000049c786280100000000000049c786300100000000000049c7863801000000000000eb6441c785e400000005000000488d3d180000004989bdf000'
    '000041c685e00000000549c745282c000000c34d8b75384d0375304d8b7d10eb2c49c786200100000000000049c786280100000000000049c7863001'
    '00000000000049c78638010000000000004889c8498b85000100004885c0745448c7c000000000492b86200100004989862001000048c7c000000000'
    '491b86280100004989862801000048c7c000000000491b86300100004989863001000048c7c000000000491b863801000049898638010000498b8638'
    '010000'
)


def test_authoritative_r5_smod_matches_at_its_mid_block_reset():
    [found] = discover_smod_summaries(identify_basic_blocks(disassemble_hex(R5_SMOD,0xc5dd8)),strict=True)
    p=found.payload
    assert (p.entry_addr,p.start_block_addr,p.start_instruction_index,p.continuation_addr)==(0xc5ee0,0xc5dd8,40,0xc6284)
    assert p.dividend_offsets==(0x140,0x148,0x150,0x158)
    assert p.divisor_offsets==(0x120,0x128,0x130,0x138)
    assert p.inner_mod.builtin_stack_pointer==44


def test_signed_proof_refusal_becomes_a_raw_fallback_signal(monkeypatch):
    from x86_64.summaries.signed_proof import SignedProofError
    s,state=configured(17,5);spec=SModSummarySpec()
    def refuse(*args):raise SignedProofError(s.entry_addr,'effect_0','solver=unknown')
    monkeypatch.setattr(spec,'lemma',refuse)
    with pytest.raises(SummaryPreconditionError) as rejected:
        spec.apply(s,state,fresh_prefix='refused')
    assert rejected.value.kind=='smod' and rejected.value.result=='rejected'
    assert rejected.value.location==s.start_key and isinstance(rejected.value.__cause__,SignedProofError)


def test_budget_abort_is_not_a_summary_fallback(monkeypatch):
    from verification.block_equivalence import ProofBudgetExceeded
    s,state=configured(17,5);spec=SModSummarySpec()
    def expired(*args):raise ProofBudgetExceeded('node budget exhausted')
    monkeypatch.setattr(spec,'lemma',expired)
    with pytest.raises(ProofBudgetExceeded):spec.apply(s,state,fresh_prefix='expired')
