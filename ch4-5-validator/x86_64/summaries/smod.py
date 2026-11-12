"""Candidate whole-opcode SMOD slices; every application needs signed_proof's raw theorem."""
from __future__ import annotations

from dataclasses import dataclass

from z3 import And, BitVecVal, BoolSort, If, Not, Or, is_expr

from common.arithmetic import _abs256, _is_negative, _is_uint64, smod_semantics
from common.fresh_symbols import FreshSymbols
from common.uint256 import Uint256
from state.smt_state import MemoryDomain
from state.x86_state import PointerTag
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.disassembler import parse_operands
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import Register
from .base import (SummaryContinuation, SummaryMatchError, SummaryPreconditionError,
                   X86Summary, require_single_entry)
from .div import (CALLER_SAVED, DIV_FLAGS, _Parser, _callengine_effects,
                  _forwarded_limb, require_stack_geometry)

SMOD_SUMMARY_KIND = "smod"
SMOD_SIGN_OFFSET = 0x100  # the AOT compiler amd64 callEngine.archContext.evmTempValueForSMod.
_CONTROL = {Register.R13, Register.R14, Register.R15}


@dataclass(frozen=True)
class UnsignedModSummary:
    entry_addr: int
    continuation_addr: int
    dividend_offsets: tuple
    divisor_offsets: tuple
    builtin_index: int
    builtin_stack_pointer: int
    resume_addr: int
    clobber_registers: tuple

    @property
    def entry(self): return self.entry_addr
    @property
    def end(self): return self.continuation_addr
    @property
    def index(self): return self.builtin_index
    @property
    def sp(self): return self.builtin_stack_pointer
    @property
    def resume(self): return self.resume_addr


@dataclass(frozen=True)
class SModSummary:
    entry_addr: int
    start_block_addr: int
    start_instruction_index: int
    continuation_addr: int
    covered_block_addrs: tuple
    dividend_offsets: tuple
    divisor_offsets: tuple
    inner_mod: UnsignedModSummary
    clobber_registers: tuple


class SModSummaryMatchError(SummaryMatchError):
    pass


class _SModParser(_Parser):
    def fail(self, why):
        raise SModSummaryMatchError(f"0x{self.addr:x}: {why}")

    def zero(self, reg):
        self.expect("mov", dest_reg=reg, immediate=0, src_reg=None, is_memory=False)

    def iszero(self, reg=None):
        _, ops = self.expect("mov", immediate=0, src_reg=None, is_memory=False)
        temp = ops.get("dest_reg")
        if temp is None or temp in _CONTROL or (reg is not None and temp != reg):
            self.fail("bad zero-test register")
        offsets = tuple(self.stack("or", dest_reg=temp) for _ in range(4))
        self.expect("test", dest_reg=temp, src_reg=temp, is_memory=False)
        return offsets, temp, self.jump("je")

    def sign(self, offsets, reg):
        if self.stack("mov", dest_reg=reg) != offsets[3]:
            self.fail("sign check does not read the high operand limb")
        self.expect("shr", dest_reg=reg, immediate=63, is_memory=False)
        self.expect("test", dest_reg=reg, src_reg=reg, is_memory=False)
        return self.jump("je")

    def negate(self, offsets, reg):
        for k, offset in enumerate(offsets):
            self.zero(reg)
            if self.stack("sub" if k == 0 else "sbb", dest_reg=reg) != offset:
                self.fail("negation reads the wrong limb")
            if self.stack("mov", src_reg=reg) != offset:
                self.fail("negation writes the wrong limb")

    def compare(self, left, right, reg):
        for k in range(4):
            if self.stack("mov", dest_reg=reg) != left[k]:
                self.fail("comparison minuend is not the operand")
            if self.stack("sub" if k == 0 else "sbb", dest_reg=reg) != right[k]:
                self.fail("comparison subtrahend is not the operand")

    def clear(self, offsets):
        for offset in offsets:
            if self.stack("mov", immediate=0, src_reg=None) != offset:
                self.fail("zero result writes the wrong slot")

    def mod(self, x, y):
        entry, saved = self.addr, None
        first = self.insn_at.get(self.addr)
        if first is not None and first.mnemonic.lower() == "mov":
            ops = parse_operands(first)
            if not ops.get("is_memory") and ops.get("src_reg") == Register.RAX:
                saved = ops.get("dest_reg")
                if saved is None or saved in _CONTROL or saved in (Register.RAX, Register.RDX):
                    self.fail("bad RAX save register")
                self.expect("mov", dest_reg=saved, src_reg=Register.RAX, is_memory=False)
        mx, reg, zero = self.iszero()
        my, _, zero_y = self.iszero(reg)
        if mx != x or my != y or zero != zero_y or reg in (Register.RAX, Register.RDX, saved):
            self.fail("unsigned MOD zero tests do not match the outer operands")
        self.compare(x, y, reg)
        not_less = self.jump("jae")
        for k in range(4):
            if self.stack("mov", dest_reg=reg) != x[k] or self.stack("mov", src_reg=reg) != y[k]:
                self.fail("x<y remainder copy is not x -> y")
        end = self.jump("jmp")
        self.at("x>=y", not_less)
        self.compare(y, x, reg)
        greater = self.jump("jb")
        self.clear(y)
        if self.jump("jmp") != end:
            self.fail("equal operands do not join")
        self.at("x>y", greater)
        self.zero(reg)
        if tuple(self.stack("or", dest_reg=reg) for _ in range(3)) != x[1:]:
            self.fail("IsUint64 does not read x2..x4")
        self.expect("test", dest_reg=reg, src_reg=reg, is_memory=False)
        builtin = self.jump("jne")
        self.zero(Register.RDX)
        if self.stack("mov", dest_reg=Register.RAX) != x[0] or self.stack("mov", dest_reg=reg) != y[0]:
            self.fail("remainder DIV operands are not x1/y1")
        self.expect("div", dest_reg=reg, is_memory=False)
        if self.stack("mov", src_reg=Register.RDX) != y[0]:
            self.fail("remainder is not read from RDX")
        self.clear(y[1:])
        if self.jump("jmp") != end:
            self.fail("small remainder does not join")
        self.at("MOD builtin", builtin)
        _, ops = self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=4,
                             offset=self.offsets["builtin_function_index"], src_reg=None)
        index = ops.get("immediate") or 0
        if self.profile.builtin_functions.get(index) != "mod":
            self.fail("unsigned MOD builtin index is not mod")
        lea, ops = self.expect("lea")
        ret_reg = ops.get("dest_reg")
        if ret_reg is None or ret_reg in _CONTROL or ret_reg in (Register.RAX, Register.RDX, reg, saved) or "rip" not in lea.op_str:
            self.fail("bad MOD return-address register")
        resume = lea.addr + lea.size + ops.get("offset", 0)
        self.callengine("mov", "return_address", 8, src_reg=ret_reg)
        self.callengine("mov", "status_code", 1, immediate=self.profile.status_codes["call_builtin_function"])
        _, ops = self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=8,
                             offset=self.offsets["stack_pointer"], src_reg=None)
        sp = ops.get("immediate") or 0
        self.expect("ret")
        self.at("MOD resume", resume)
        self.expect("mov", dest_reg=Register.R14, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["stack_base"])
        self.expect("add", dest_reg=Register.R14, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["stack_byte_offset"])
        self.expect("mov", dest_reg=Register.R15, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["memory_base"])
        if self.jump("jmp") != end:
            self.fail("builtin remainder does not join")
        self.at("MOD zero tail", zero)
        self.clear(y)
        self.at("MOD join", end)
        if saved is not None:
            self.expect("mov", dest_reg=Register.RAX, src_reg=saved, is_memory=False)
        clobbers = {reg, Register.RAX, Register.RDX, ret_reg}
        if saved is not None: clobbers.add(saved)
        return UnsignedModSummary(entry, end, x, y, index, sp, resume,
                                  tuple(sorted(clobbers, key=lambda r: r.value)))

    def parse(self):
        entry = self.addr
        # Missing/reset-to-one versions are rejected, never granted a flag==0 premise.
        self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=8,
                    offset=SMOD_SIGN_OFFSET, immediate=0, src_reg=None, dest_reg=None)
        x, reg, after_x = self.iszero()
        if self.sign(x, reg) != after_x:
            self.fail("x sign/zero paths have different joins")
        self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=8,
                    offset=SMOD_SIGN_OFFSET, immediate=1, src_reg=None, dest_reg=None)
        self.negate(x, reg)
        self.at("abs(x) join", after_x)
        y, _, after_y = self.iszero(reg)
        if self.sign(y, reg) != after_y:
            self.fail("y sign/zero paths have different joins")
        self.negate(y, reg)
        self.at("abs(y) join", after_y)
        if (x != tuple(x[0]+8*k for k in range(4)) or y != tuple(y[0]+8*k for k in range(4))
                or x[0] != y[0]+32):
            self.fail("SMOD stack operands are not adjacent contiguous words")
        inner = self.mod(x, y)
        self.expect("mov", dest_reg=reg, is_memory=True, base_reg=Register.R13,
                    memory_size=8, offset=SMOD_SIGN_OFFSET)
        self.expect("test", dest_reg=reg, src_reg=reg, is_memory=False)
        end = self.jump("je")
        self.negate(y, reg)
        self.at("SMOD join", end)
        return entry, end, x, y, inner, tuple(sorted(set(inner.clobber_registers)|{reg}, key=lambda r:r.value))


def _looks_like_entry(insn):
    if insn.mnemonic.lower() != "mov": return False
    o = parse_operands(insn)
    return (o.get("is_memory") and o.get("base_reg")==Register.R13 and o.get("index_reg") is None
            and o.get("memory_size")==8 and o.get("offset")==SMOD_SIGN_OFFSET
            and o.get("src_reg") is None and o.get("dest_reg") is None and (o.get("immediate") or 0)==0)


def discover_smod_summaries(blocks, *, strict=False, profile=AOT_COMPILER_PROFILE):
    at={i.addr:i for b in blocks for i in b.instructions};owners={i.addr:(b,k) for b in blocks for k,i in enumerate(b.instructions)}
    block_at={b.start_addr:b for b in blocks};found=[];failures=[];cfg=None
    for insn in at.values():
        if not _looks_like_entry(insn):continue
        try:
            entry,end,x,y,inner,clobbers=_SModParser(at,insn.addr,profile).parse()
            if end not in block_at:raise SModSummaryMatchError("SMOD join is not a block start")
            block,index=owners[entry]
            covered=tuple(sorted({block.start_addr}|{b.start_addr for b in blocks if entry<b.start_addr<end}))
            if any(block_at[k].end_addr>end for k in covered):raise SModSummaryMatchError("SMOD covered block extends past join")
            payload=SModSummary(entry,block.start_addr,index,end,covered,x,y,inner,clobbers)
            summary=X86Summary(SMOD_SUMMARY_KIND,entry,block.start_addr,index,SummaryContinuation(end),covered,clobbers,DIV_FLAGS,payload)
            if cfg is None:cfg=build_x86_cfg(blocks)
            require_single_entry(summary,*cfg)
            found.append(summary)
        except SummaryMatchError as exc:
            if strict:failures.append(str(exc))
    if failures:raise SModSummaryMatchError("unmatched reset-SMOD slice(s): "+"; ".join(failures))
    return found


def builtin_taken_condition(x: Uint256, y: Uint256):
    """Guard on the already-absolute operands used by unsigned MOD."""
    return And(Not(y.iszero_semantics()),Not(x.eq_semantics(y)),Not(x.lt_semantics(y)),
               Not(_is_uint64(x.to_bv256())))


def apply_smod_summary(summary, state, *, fresh_prefix, profile=AOT_COMPILER_PROFILE, path_condition=None):
    from verification.block_summaries import _leaves
    from common.store_forwarding import shared_forward_scope
    roots=[v for v in _leaves(state).values() if is_expr(v)]
    roots.extend(state.assumptions or [])
    roots.extend(getattr(state,'summary_assumed_premises',[]))
    if path_condition is not None:roots.append(path_condition)
    fresh=FreshSymbols(*roots);new=state.copy();r14=state.x86_registers.get_register(Register.R14)
    shared_forward_scope()
    def word(offsets):
        return Uint256(*(_forwarded_limb(state.x86_memory.load_limb(r14+BitVecVal(k,64),domain=MemoryDomain.STACK)) for k in offsets)).to_bv256()
    x,y=word(summary.dividend_offsets),word(summary.divisor_offsets)
    new.x86_memory=new.x86_memory.store_256bit(r14+BitVecVal(summary.dividend_offsets[0],64),_abs256(x),domain=MemoryDomain.STACK)
    new.x86_memory=new.x86_memory.store_256bit(r14+BitVecVal(summary.divisor_offsets[0],64),smod_semantics(x,y),domain=MemoryDomain.STACK)
    tag=f'{fresh_prefix}_{summary.entry_addr:x}';took=fresh.const(BoolSort(ctx=r14.ctx),tag+'_builtin')
    r13=state.x86_registers.get_register(Register.R13)
    new.x86_memory=new.x86_memory.store_limb(r13+BitVecVal(SMOD_SIGN_OFFSET,64),If(_is_negative(x),BitVecVal(1,64),BitVecVal(0,64)),domain=MemoryDomain.CALLENGINE)
    for field,size,attr,value in _callengine_effects(summary.inner_mod,profile):
        address=r13+BitVecVal(profile.offsets[field],64)
        for i in range(size):
            old=new.x86_memory.load_byte(address+BitVecVal(i,64),domain=MemoryDomain.CALLENGINE)
            new.x86_memory=new.x86_memory.store_byte(address+BitVecVal(i,64),If(took,BitVecVal((value>>(8*i))&255,8),old),domain=MemoryDomain.CALLENGINE)
        old=getattr(state,attr);setattr(new,attr,If(took,BitVecVal(value%(1<<old.size()),old.size()),old))
    for attr in ('return_offset','return_length'):
        old=getattr(state,attr);setattr(new,attr,If(took,BitVecVal(0,old.size()),old))
    for reg in summary.clobber_registers:
        new.x86_registers.set_register(reg,fresh.const(state.x86_registers.get_register(reg).sort(),tag+'_'+reg.value))
    for reg in CALLER_SAVED:new.x86_registers.clear_pointer_tag(reg)
    for flag in DIV_FLAGS:new.x86_registers.set_flag(flag,fresh.const(state.x86_registers.get_flag(flag).sort(),tag+'_'+flag))
    return new,took


class SModSummarySpec:
    kind=SMOD_SUMMARY_KIND
    def __init__(self, *, proof_timeout_ms=30000, profile=AOT_COMPILER_PROFILE):
        self.proof_timeout_ms=proof_timeout_ms;self.profile=profile;self.proof_stats={'proven':0,'cache_hits':0};self._blocks=()
    def discover(self,ctx,*,strict=False):
        self._blocks=ctx.blocks
        return discover_smod_summaries(ctx.blocks,strict=strict,profile=self.profile)
    def lemma(self,summary):
        from .signed_proof import prove_signed_slice_cached
        lemma,status=prove_signed_slice_cached(summary,self._blocks,profile=self.profile,timeout_ms=self.proof_timeout_ms)
        self.proof_stats[status]+=1
        return lemma
    def apply(self,summary,state,*,fresh_prefix,path_condition=None,precondition_timeout_ms=5000):
        if not isinstance(summary.payload,SModSummary):raise TypeError('SMOD summary payload must be SModSummary')
        for reg in set(summary.clobber_registers)|set(CALLER_SAVED):
            if state.x86_registers.get_pointer_tag(reg)!=PointerTag.NONE:
                raise SummaryPreconditionError(kind=self.kind,label=f'{reg.value} pointer tag',premise=str(state.x86_registers.get_pointer_tag(reg)),result='rejected',location=summary.start_key)
        from .signed_proof import SignedProofError
        try:
            self.lemma(summary)
        except SignedProofError as exc:
            raise SummaryPreconditionError(kind=self.kind, label=f"slice lemma {exc.label}",
                premise=str(exc), result="rejected", location=summary.start_key) from exc
        require_stack_geometry(summary,state,path_condition,precondition_timeout_ms)
        return apply_smod_summary(summary.payload,state,fresh_prefix=fresh_prefix,profile=self.profile,path_condition=path_condition)[0]
