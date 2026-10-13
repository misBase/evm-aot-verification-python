"""go-hpc-evm amd64 output summary for compileEVMDivWithReg slices.

The slice (after ``compileResetAllLocationsToStack`` every operand limb is a
stack slot ``[r14+off]``)::

    mov T1,0; or T1,[y1..y4]; test T1,T1; je ZERO          ; y == 0
    mov T2,[x1]; sub T2,[y1]; (mov T2,[xk]; sbb T2,[yk])*3; jae NB
  ZERO: mov qword [y1..y4],0; jmp END                     ; y > x
  NB: mov T1,0; or T1,[x2..x4]; test T1,T1; jne BUILTIN
      mov rdx,0; mov rax,[x1]; mov T2,[y1]; div T2         ; x.IsUint64
      mov [y1],rax; mov qword [y2..y4],0; jmp END
  BUILTIN: mov dword [r13+idx],DIV; lea R,[rip+RESUME]; mov [r13+ret],R
      mov byte [r13+status],5; mov qword [r13+sp],SP; ret  ; Go holiman Div
  RESUME: mov r14,[r13+base]; add r14,[r13+off]; mov r15,[r13+mem]
  END:

The summary replaces the whole slice (all four paths, builtin bridge
included) by ``div_semantics(x, y)`` written to the y slot -- the SAME function
and argument order the EVM side uses. Its soundness is not trusted: every
distinct slice is proved against raw execution on free inputs in
``div_proof.py`` before the first application (fail-closed).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Sequence, Tuple

from z3 import And, BitVec, BitVecVal, Bool, BoolVal, If, Not, Or, simplify

from common.arithmetic import _is_uint64, div_semantics
from common.uint256 import Uint256
from state.smt_state import MemoryDomain, SMTState
from x86_64.aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from x86_64.disassembler import parse_operands
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import Register, X86Block, X86Instruction

from .base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    SummaryMatchError,
    SummaryPreconditionError,
    X86Summary,
    require_single_entry,
)


DIV_SUMMARY_KIND = "div"
DIV_FLAGS = ("CF", "ZF", "SF", "OF", "PF", "AF")
# Go semantics clears these tags on the builtin path (_clear_caller_saved_pointer_tags).
CALLER_SAVED = (
    Register.RAX, Register.RCX, Register.RDX, Register.RSI, Register.RDI,
    Register.R8, Register.R9, Register.R10, Register.R11,
)
_RESERVED = {Register.RAX, Register.RDX, Register.R13, Register.R14, Register.R15}


@dataclass(frozen=True)
class DivSummary:
    entry_addr: int
    start_block_addr: int
    start_instruction_index: int
    continuation_addr: int
    covered_block_addrs: Tuple[int, ...]
    dividend_offsets: Tuple[int, int, int, int]   # x (stack top), little-endian limbs
    divisor_offsets: Tuple[int, int, int, int]    # y; the quotient is written here
    builtin_index: int
    builtin_stack_pointer: int                   # imm written to [r13+sp] before ret
    resume_addr: int
    clobber_registers: Tuple[Register, ...]


class DivSummaryMatchError(SummaryMatchError):
    pass


class _Parser:
    def __init__(self, insn_at: Dict[int, X86Instruction], addr: int, profile: X86AOTProfile):
        self.insn_at, self.addr, self.profile = insn_at, addr, profile
        self.offsets = profile.offsets

    def fail(self, why):
        raise DivSummaryMatchError(f"0x{self.addr:x}: {why}")

    def next(self) -> Tuple[X86Instruction, dict]:
        while True:
            insn = self.insn_at.get(self.addr)
            if insn is None:
                self.fail("slice leaves the decoded code")
            self.addr = insn.addr + insn.size
            if insn.mnemonic.lower() != "nop":
                return insn, parse_operands(insn)

    def at(self, label, addr):
        while self.insn_at.get(self.addr) is not None and self.insn_at[self.addr].mnemonic.lower() == "nop" \
                and self.addr != addr:
            self.addr += self.insn_at[self.addr].size
        if self.addr != addr:
            self.fail(f"{label} expected at 0x{addr:x}")

    def expect(self, mnemonic, **want):
        insn, ops = self.next()
        if insn.mnemonic.lower() != mnemonic:
            self.fail(f"expected {mnemonic}, got {insn.mnemonic} {insn.op_str}")
        for key, value in want.items():
            got = ops.get(key)
            got = (got or 0) if key == "immediate" else bool(got) if key == "is_memory" else got
            if got != value:
                self.fail(f"{insn.mnemonic} {insn.op_str}: {key} != {value!r}")
        return insn, ops

    def stack(self, mnemonic, **want):
        insn, ops = self.expect(mnemonic, is_memory=True, base_reg=Register.R14, memory_size=8, **want)
        if ops.get("index_reg") is not None:
            self.fail(f"indexed stack operand: {insn.op_str}")
        return ops["offset"]

    def jump(self, mnemonic):
        target = self.expect(mnemonic)[1].get("jump_target")
        if target is None:
            self.fail(f"{mnemonic} without static target")
        return target

    def callengine(self, mnemonic, field, size, **want):
        self.expect(mnemonic, is_memory=True, base_reg=Register.R13, memory_size=size,
                    offset=self.offsets[field], **want)

    def parse(self) -> dict:
        entry = self.addr
        _, ops = self.expect("mov", immediate=0, is_memory=False)
        t1 = ops.get("dest_reg")
        if t1 is None or t1 in _RESERVED:
            self.fail("bad IsZero temp register")
        y = [self.stack("or", dest_reg=t1) for _ in range(4)]
        self.expect("test", dest_reg=t1, src_reg=t1)
        zero = self.jump("je")
        x, t2 = [], None
        for k in range(4):
            _, ops = self.expect("mov", is_memory=True, base_reg=Register.R14, memory_size=8)
            t2 = t2 or ops.get("dest_reg")
            if ops.get("dest_reg") != t2 or t2 in _RESERVED or t2 == t1:
                self.fail("bad compare temp register")
            x.append(ops["offset"])
            if self.stack("sub" if k == 0 else "sbb", dest_reg=t2) != y[k]:
                self.fail("compare subtrahend is not y")
        nb = self.jump("jae")
        self.at("ZERO", zero)
        for k in range(4):
            if self.stack("mov", immediate=0, src_reg=None) != y[k]:
                self.fail("zero store is not y")
        end = self.jump("jmp")
        self.at("NB", nb)
        self.expect("mov", dest_reg=t1, immediate=0, is_memory=False)
        if [self.stack("or", dest_reg=t1) for _ in range(3)] != x[1:]:
            self.fail("IsUint64 does not test x2..x4")
        self.expect("test", dest_reg=t1, src_reg=t1)
        builtin = self.jump("jne")
        self.expect("mov", dest_reg=Register.RDX, immediate=0, is_memory=False)
        if self.stack("mov", dest_reg=Register.RAX) != x[0] or self.stack("mov", dest_reg=t2) != y[0]:
            self.fail("div operands are not x1/y1")
        self.expect("div", dest_reg=t2, is_memory=False)
        if self.stack("mov", src_reg=Register.RAX) != y[0]:
            self.fail("quotient not stored to y1")
        for k in range(1, 4):
            if self.stack("mov", immediate=0, src_reg=None) != y[k]:
                self.fail("high quotient limbs not cleared")
        if self.jump("jmp") != end:
            self.fail("fast path does not join")
        self.at("BUILTIN", builtin)
        _, ops = self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=4,
                             offset=self.offsets["builtin_function_index"])
        index = ops.get("immediate") or 0
        if self.profile.builtin_functions.get(index) != "div":
            self.fail(f"builtin index {index} is not div")
        lea, ops = self.expect("lea")
        ret_reg = ops.get("dest_reg")
        if ret_reg is None or ret_reg in _RESERVED or "rip" not in lea.op_str:
            self.fail("bad return-address lea")
        resume = lea.addr + lea.size + ops.get("offset", 0)
        self.callengine("mov", "return_address", 8, src_reg=ret_reg)
        self.callengine("mov", "status_code", 1,
                        immediate=self.profile.status_codes["call_builtin_function"])
        _, ops = self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=8,
                             offset=self.offsets["stack_pointer"], src_reg=None)
        sp = ops.get("immediate") or 0
        self.expect("ret")
        self.at("RESUME", resume)
        self.expect("mov", dest_reg=Register.R14, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["stack_base"])
        self.expect("add", dest_reg=Register.R14, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["stack_byte_offset"])
        self.expect("mov", dest_reg=Register.R15, is_memory=True, base_reg=Register.R13,
                    offset=self.offsets["memory_base"])
        self.at("END", end)
        if x != [x[0] + 8 * k for k in range(4)] or y != [y[0] + 8 * k for k in range(4)]:
            self.fail("operand limbs are not contiguous")
        return dict(entry=entry, end=end, x=tuple(x), y=tuple(y), index=index, sp=sp,
                    resume=resume, clobbers=tuple(sorted({t1, t2, Register.RAX, Register.RDX, ret_reg},
                                                         key=lambda r: r.value)))


def _looks_like_entry(insn_at: Dict[int, X86Instruction], addr: int) -> bool:
    """mov T,0; or T,[r14+..] x4; test; je; mov T2,[r14+..]; sub. Other IsZero
    uses (IsUint64 has three ors, SDIV sign checks shr) do not follow with sub."""
    window = []
    while len(window) < 9 and addr in insn_at:
        insn = insn_at[addr]
        addr += insn.size
        if insn.mnemonic.lower() != "nop":
            window.append(insn)
    if [i.mnemonic.lower() for i in window] != ["mov", "or", "or", "or", "or", "test", "je", "mov", "sub"]:
        return False
    a = parse_operands(window[0])
    return (a.get("dest_reg") is not None and not a.get("is_memory") and not a.get("immediate")
            and all(parse_operands(i).get("dest_reg") == a["dest_reg"]
                    and parse_operands(i).get("base_reg") == Register.R14 for i in window[1:5]))


def discover_div_summaries(
    blocks: Sequence[X86Block],
    *,
    strict: bool = False,
    profile: X86AOTProfile = GO_HPC_EVM_PROFILE,
) -> List[X86Summary]:
    blocks_by_addr = {b.start_addr: b for b in blocks}
    insn_at = {i.addr: i for b in blocks for i in b.instructions}
    succs = unresolved = None
    found, failures = [], []
    for block in blocks:
        for index in range(len(block.instructions)):
            if not _looks_like_entry(insn_at, block.instructions[index].addr):
                continue
            try:
                parsed = _Parser(insn_at, block.instructions[index].addr, profile).parse()
                entry, end = parsed["entry"], parsed["end"]
                if end not in blocks_by_addr:
                    raise DivSummaryMatchError(f"join 0x{end:x} is not a block start")
                covered = tuple(sorted({block.start_addr} | {
                    a for a in blocks_by_addr if entry < a < end}))
                if any(blocks_by_addr[a].end_addr > end for a in covered):
                    raise DivSummaryMatchError("a covered block runs past the join")
                payload = DivSummary(
                    entry_addr=entry, start_block_addr=block.start_addr,
                    start_instruction_index=index, continuation_addr=end,
                    covered_block_addrs=covered, dividend_offsets=parsed["x"],
                    divisor_offsets=parsed["y"], builtin_index=parsed["index"],
                    builtin_stack_pointer=parsed["sp"], resume_addr=parsed["resume"],
                    clobber_registers=parsed["clobbers"])
                summary = X86Summary(
                    kind=DIV_SUMMARY_KIND, entry_addr=entry, start_block_addr=block.start_addr,
                    start_instruction_index=index, continuation=SummaryContinuation(end, 0),
                    covered_block_addrs=covered, clobber_registers=parsed["clobbers"],
                    clobber_flags=DIV_FLAGS, payload=payload)
                if succs is None:
                    succs, unresolved = build_x86_cfg(blocks)
                require_single_entry(summary, succs, unresolved)
            except SummaryMatchError as exc:
                if strict:
                    failures.append(str(exc))
                continue
            found.append(summary)
    if failures:
        raise DivSummaryMatchError("unmatched DIV-like x86 slice(s): " + "; ".join(failures))
    return found


def builtin_taken_condition(x, y):
    """The builtin path's guard in div_semantics' own terms: y != 0, y <= x, x >= 2^64."""
    return And(Not(Or(y.iszero_semantics(), y.gt_semantics(x))), Not(_is_uint64(x.to_bv256())))


def _callengine_effects(summary: DivSummary, profile: X86AOTProfile):
    """(field offset name, byte size, side-channel attr, value) the builtin path leaves behind."""
    return (
        ("builtin_function_index", 4, "callengine_builtin_func_index", summary.builtin_index),
        ("return_address", 8, "callengine_return_address", summary.resume_addr),
        ("status_code", 1, "callengine_status_code", profile.status_codes["call_builtin_function"]),
        # Go pops x, y and pushes the quotient: sp - 4 limbs (go_function_semantics._update_sp_in_memory).
        ("stack_pointer", 8, "callengine_stack_pointer_limbs", summary.builtin_stack_pointer - 4),
    )


def stack_geometry(state: SMTState):
    """What the RESUME block re-establishes; the summary leaves R14/R15 alone, so it must hold."""
    regs = state.x86_registers
    return And(regs.get_register(Register.R14) == state.callengine_stack_base + state.callengine_stack_byte_offset,
               regs.get_register(Register.R15) == state.callengine_memory_base)


def _forwarded_limb(load):
    """Identity rewrite of an 8-byte stack load: forward the byte Selects over
    the Store chain and, if they are the 8 bytes of one stored limb L, return L.

    Without it the operand stays byte-split and z3's simplify pushes the low
    Extract into the (MUL-product) limb's arithmetic, so the x86 operand of
    div_semantics no longer matches the EVM operand syntactically."""
    from z3 import is_app_of, Z3_OP_CONCAT, Z3_OP_EXTRACT

    from common.store_forwarding import forward_selects

    def bytes_of(term):  # the 64-bit L with term == Concat(L[63:56], ..., L[7:0]), else None
        parts, work = [], [term]
        while work:  # z3 builds Concat(b7, ..., b0) as nested binary concats
            node = work.pop()
            if is_app_of(node, Z3_OP_CONCAT):
                work.extend(reversed(node.children()))
            else:
                parts.append(node)
        if len(parts) != 8 or not all(is_app_of(p, Z3_OP_EXTRACT) for p in parts):
            return None
        source = parts[0].arg(0)
        if source.size() != 64 or any(p.params() != [8 * i + 7, 8 * i] or not p.arg(0).eq(source)
                                      for i, p in enumerate(reversed(parts))):
            return None
        return source

    term, source = forward_selects(load), None
    while (inner := bytes_of(term)) is not None:  # a reload of a spilled reload, ...
        term = source = inner
    return load if source is None else source


def apply_div_summary(
    summary: DivSummary,
    state: SMTState,
    *,
    fresh_prefix: str,
    profile: X86AOTProfile = GO_HPC_EVM_PROFILE,
) -> Tuple[SMTState, object]:
    """Returns (state, builtin choice bit). The bit is a fresh Bool: callEngine
    exit-context fields are written iff it is true. Leaving it free
    over-approximates (every proof must hold for both values); the lemma proves
    the raw slice is the instance bit := builtin_taken_condition."""
    new = state.copy()
    r14 = state.x86_registers.get_register(Register.R14)
    mem = state.x86_memory

    def limbs(offsets):
        return Uint256(*(_forwarded_limb(mem.load_limb(r14 + BitVecVal(o, 64), domain=MemoryDomain.STACK))
                         for o in offsets))

    x, y = limbs(summary.dividend_offsets), limbs(summary.divisor_offsets)
    quotient = div_semantics(x.to_bv256(), y.to_bv256())
    new.x86_memory = new.x86_memory.store_256bit(
        r14 + BitVecVal(summary.divisor_offsets[0], 64), quotient, domain=MemoryDomain.STACK)

    tag = f"{fresh_prefix}_{summary.entry_addr:x}"
    took = Bool(f"{tag}_builtin")
    r13 = state.x86_registers.get_register(Register.R13)
    for field, size, attr, value in _callengine_effects(summary, profile):
        addr = r13 + BitVecVal(profile.offsets[field], 64)
        for i in range(size):
            byte = BitVecVal((value >> (8 * i)) & 0xFF, 8)
            old = new.x86_memory.load_byte(addr + BitVecVal(i, 64), domain=MemoryDomain.CALLENGINE)
            new.x86_memory = new.x86_memory.store_byte(
                addr + BitVecVal(i, 64), If(took, byte, old), domain=MemoryDomain.CALLENGINE)
        old = getattr(state, attr)
        setattr(new, attr, If(took, BitVecVal(value % (1 << old.size()), old.size()), old))
    # The bridge `ret` runs the RETURN-metadata semantics with status 5: no return data.
    for attr in ("return_offset", "return_length"):
        old = getattr(state, attr)
        setattr(new, attr, If(took, BitVecVal(0, old.size()), old))

    for reg in summary.clobber_registers:
        new.x86_registers.set_register(reg, BitVec(f"{tag}_{reg.value}", 64))  # also clears its tag
    for reg in CALLER_SAVED:
        new.x86_registers.clear_pointer_tag(reg)
    for flag in DIV_FLAGS:
        new.x86_registers.set_flag(flag, BitVec(f"{tag}_{flag}", 1))
    return new, took


class DivSummarySpec:
    kind = DIV_SUMMARY_KIND

    def __init__(self, *, prove_hits: bool = True, proof_timeout_ms: int = 30_000,
                 profile: X86AOTProfile = GO_HPC_EVM_PROFILE):
        self.prove_hits = prove_hits
        self.proof_timeout_ms = proof_timeout_ms
        self.profile = profile
        self.proof_stats = {"proven": 0, "cache_hits": 0}
        self._blocks: Sequence[X86Block] = ()

    def discover(self, ctx: SummaryDiscoveryContext, *, strict: bool = False) -> Iterable[X86Summary]:
        # Proofs run lazily at the first application of each slice shape
        # (a contract has hundreds of DIV slices; most are never reached).
        self._blocks = ctx.blocks
        return discover_div_summaries(ctx.blocks, strict=strict, profile=self.profile)

    def lemma(self, summary: X86Summary):
        """The fail-closed per-slice proof (cached); raises DivProofError."""
        from .div_proof import prove_div_slice_cached
        lemma, status = prove_div_slice_cached(summary, self._blocks, profile=self.profile,
                                               timeout_ms=self.proof_timeout_ms)
        self.proof_stats[status] += 1
        return lemma

    def apply(self, summary: X86Summary, state: SMTState, *, fresh_prefix: str,
              path_condition=None, precondition_timeout_ms: int = 5000) -> SMTState:
        if not isinstance(summary.payload, DivSummary):
            raise TypeError(f"DIV summary payload must be DivSummary, got {type(summary.payload)!r}")
        if self.prove_hits:
            self.lemma(summary)
        require_stack_geometry(summary, state, path_condition, precondition_timeout_ms)
        return apply_div_summary(summary.payload, state, fresh_prefix=fresh_prefix, profile=self.profile)[0]


def require_stack_geometry(summary: X86Summary, state: SMTState, path_condition, timeout_ms: int) -> None:
    """prove-or-reject: R14/R15 must already equal what RESUME reloads."""
    from z3 import SolverFor, unsat

    from state.x86_state import PointerTag

    # The lemma state tags R14/R15 as the RESUME reload does; the summary keeps
    # the hit's tags, so they must be those (all raw paths agree) or NONE (less
    # provenance: a later access through a copy can only fail, never misroute).
    for reg, tag in ((Register.R14, PointerTag.STACK_PTR), (Register.R15, PointerTag.EVM_PTR)):
        if state.x86_registers.get_pointer_tag(reg) not in (tag, PointerTag.NONE):
            raise SummaryPreconditionError(kind=DIV_SUMMARY_KIND, label=f"{reg.value} pointer tag",
                                           premise=str(state.x86_registers.get_pointer_tag(reg)),
                                           result="rejected", location=summary.start_key)
    goal = stack_geometry(state)
    if simplify(goal).eq(BoolVal(True)):
        return
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=timeout_ms)
    solver.add(*(state.assumptions or []))
    if path_condition is not None:
        solver.add(path_condition)
    solver.add(Not(goal))
    result = solver.check()
    if result != unsat:
        raise SummaryPreconditionError(kind=DIV_SUMMARY_KIND, label="stack geometry", premise=goal,
                                       result=str(result), location=summary.start_key)
