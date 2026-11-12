"""the AOT compiler amd64 summary for the ``memoryGasCost`` template (gas_dynamic_amd64.go).

Every memory-touching opcode's gas prologue inlines it with its own registers
S=memSizeReg (already rounded by the caller's SafeMul(toWordSize(r), 32)),
T=tmpReg (the result), T2=tmpReg2, RAX::

    test S,S; je ZERO
    movabs T,0x1FFFFFFFE0; cmp T,S; jb OOG                 ; s > cap -> OutOfGas exit
    mov T,-1; shl T,5; cmp T,S; jb BU64; add S,31; shr S,5; jmp OTHERS
  BU64: movabs S,MaxUint64/32+1
  OTHERS: mov T,S; shl S,5; mov T2,[r13+MemLen]; cmp T2,S; jae ZERO
    mov rax,T; mul rax; mov S,rax; mov T2,3; mov rax,T; mul T2; mov T,rax
    mov rax,S; mov S,0x200; mov rdx,0; div S; add T,rax; mov rax,T
    mov T2,[r13+LastGasCost]; sub T,T2; mov [r13+LastGasCost],rax; jmp END
  OOG: mov byte [r13+status],OutOfGas; mov qword [r13+sp],SP; ret
  ZERO: mov T,0
  END:

The summary covers TESTQ..END. It declares an exit guard G = (s != 0 and
s > cap): the executor runs the raw slice under G (it leaves through OOG) and
applies ``memory_fee_for_size(MemLen, LastGasCost, s)`` -- the same function
the EVM side uses -- under not G. The per-shape lemma in memgas_proof.py
proves raw == summary under not G before the first application (fail-closed).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple

from z3 import And, BitVec, BitVecVal, BoolVal, Not, UGT, simplify

from state.evm_gas_state import memory_fee_for_size
from state.smt_state import MemoryDomain, SMTState
from x86_64.aot_profile import AOT_COMPILER_PROFILE, X86AOTProfile
from x86_64.disassembler import parse_operands
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import Register, X86Block

from .base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    SummaryMatchError,
    SummaryPreconditionError,
    X86Summary,
    refuted_by_complement,
    require_single_entry,
)
from .div import _Parser


MEMGAS_SUMMARY_KIND = "memgas"
MEMGAS_FLAGS = ("CF", "ZF", "SF", "OF", "PF", "AF")
MEMGAS_CAP = 0x1FFFFFFFE0
_MASK = (1 << 64) - 1
_RESERVED = {Register.RAX, Register.RDX, Register.R13, Register.R14, Register.R15}


@dataclass(frozen=True)
class MemGasSummary:
    entry_addr: int
    start_block_addr: int
    start_instruction_index: int
    continuation_addr: int
    covered_block_addrs: Tuple[int, ...]
    size_reg: Register        # S: rounded requested size in, clobbered
    fee_reg: Register         # T: the fee out
    tmp_reg: Register         # T2: clobbered
    oog_addr: int
    zero_addr: int
    oog_stack_pointer: int
    clobber_registers: Tuple[Register, ...]   # all but fee_reg: freshened


class MemGasSummaryMatchError(SummaryMatchError):
    pass


class _MemGasParser(_Parser):
    def fail(self, why):
        raise MemGasSummaryMatchError(f"0x{self.addr:x}: {why}")

    def reg(self, mnemonic, dest, src):
        self.expect(mnemonic, dest_reg=dest, src_reg=src, is_memory=False, dest_size=8)

    def imm(self, mnemonic, dest, value):
        insn, ops = self.next()
        if insn.mnemonic.lower() not in ((mnemonic, "movabs") if mnemonic == "mov" else (mnemonic,)):
            self.fail(f"expected {mnemonic} imm, got {insn.mnemonic} {insn.op_str}")
        got = ops.get("immediate")
        if (ops.get("is_memory") or ops.get("src_reg") is not None or ops.get("dest_size") != 8
                or got is None or got & _MASK != value & _MASK or (dest is not None and ops.get("dest_reg") != dest)):
            self.fail(f"{insn.mnemonic} {insn.op_str}: expected immediate 0x{value & _MASK:x}")
        return ops.get("dest_reg")

    def field(self, mnemonic, field, **want):
        return self.expect(mnemonic, is_memory=True, base_reg=Register.R13, memory_size=8,
                           offset=self.offsets[field], index_reg=None, **want)[1]

    def parse(self) -> dict:
        entry, rax = self.addr, Register.RAX
        _, ops = self.expect("test", is_memory=False, dest_size=8)
        s = ops.get("dest_reg")
        if s is None or s in _RESERVED or ops.get("src_reg") != s:
            self.fail("bad size register")
        zero = self.jump("je")
        t = self.imm("mov", None, MEMGAS_CAP)
        if t is None or t in _RESERVED or t == s:
            self.fail("bad fee register")
        self.reg("cmp", t, s)
        oog = self.jump("jb")
        self.imm("mov", t, -1)
        self.imm("shl", t, 5)
        self.reg("cmp", t, s)
        bu64 = self.jump("jb")
        self.imm("add", s, 31)
        self.imm("shr", s, 5)
        others = self.jump("jmp")
        self.at("BU64", bu64)
        self.imm("mov", s, (1 << 64) // 32)
        self.at("OTHERS", others)
        self.reg("mov", t, s)
        self.imm("shl", s, 5)
        t2 = self.field("mov", "memory_size", src_reg=None).get("dest_reg")
        if t2 is None or t2 in _RESERVED or t2 in (s, t):
            self.fail("bad tmp register")
        self.reg("cmp", t2, s)
        if self.jump("jae") != zero:
            self.fail("no-expansion branch does not reach ZERO")
        self.reg("mov", rax, t)
        self.expect("mul", dest_reg=rax, is_memory=False, dest_size=8)
        self.reg("mov", s, rax)
        self.imm("mov", t2, 3)
        self.reg("mov", rax, t)
        self.expect("mul", dest_reg=t2, is_memory=False, dest_size=8)
        self.reg("mov", t, rax)
        self.reg("mov", rax, s)
        self.imm("mov", s, 512)
        self.imm("mov", Register.RDX, 0)
        self.expect("div", dest_reg=s, is_memory=False, dest_size=8)
        self.reg("add", t, rax)
        self.reg("mov", rax, t)
        self.field("mov", "last_gas_cost", dest_reg=t2, src_reg=None)
        self.reg("sub", t, t2)
        self.field("mov", "last_gas_cost", dest_reg=None, src_reg=rax)
        end = self.jump("jmp")
        self.at("OOG", oog)
        self.expect("mov", is_memory=True, base_reg=Register.R13, memory_size=1, index_reg=None,
                    offset=self.offsets["status_code"], src_reg=None,
                    immediate=self.profile.status_codes["out_of_gas"])
        sp = self.field("mov", "stack_pointer", src_reg=None).get("immediate") or 0
        self.expect("ret")
        self.at("ZERO", zero)
        self.imm("mov", t, 0)
        self.at("END", end)
        if not entry < oog < zero < end:
            self.fail("unexpected label order")
        return dict(entry=entry, end=end, s=s, t=t, t2=t2, oog=oog, zero=zero, sp=sp)


def _looks_like_entry(insn_at, addr) -> bool:
    """test S,S; je; movabs T,0x1FFFFFFFE0 (inner nops skipped; the entry is the test itself)."""
    if addr not in insn_at or insn_at[addr].mnemonic.lower() != "test":
        return False
    window = []
    while len(window) < 3 and addr in insn_at:
        insn = insn_at[addr]
        addr += insn.size
        if insn.mnemonic.lower() != "nop":
            window.append(insn)
    return ([i.mnemonic.lower() for i in window[:2]] == ["test", "je"] and len(window) == 3
            and window[2].mnemonic.lower() in ("mov", "movabs")
            and parse_operands(window[2]).get("immediate") == MEMGAS_CAP)


def discover_memgas_summaries(
    blocks: Sequence[X86Block],
    *,
    strict: bool = False,
    profile: X86AOTProfile = AOT_COMPILER_PROFILE,
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
                p = _MemGasParser(insn_at, block.instructions[index].addr, profile).parse()
                entry, end = p["entry"], p["end"]
                if end not in blocks_by_addr:
                    raise MemGasSummaryMatchError(f"END 0x{end:x} is not a block start")
                covered = tuple(sorted({block.start_addr} | {a for a in blocks_by_addr if entry < a < end}))
                if any(blocks_by_addr[a].end_addr > end for a in covered):
                    raise MemGasSummaryMatchError("a covered block runs past END")
                clobbers = tuple(sorted({p["s"], p["t2"], Register.RAX, Register.RDX}, key=lambda r: r.value))
                payload = MemGasSummary(
                    entry_addr=entry, start_block_addr=block.start_addr, start_instruction_index=index,
                    continuation_addr=end, covered_block_addrs=covered, size_reg=p["s"], fee_reg=p["t"],
                    tmp_reg=p["t2"], oog_addr=p["oog"], zero_addr=p["zero"], oog_stack_pointer=p["sp"],
                    clobber_registers=clobbers)
                summary = X86Summary(
                    kind=MEMGAS_SUMMARY_KIND, entry_addr=entry, start_block_addr=block.start_addr,
                    start_instruction_index=index, continuation=SummaryContinuation(end, 0),
                    covered_block_addrs=covered, clobber_registers=(*clobbers, p["t"]),
                    clobber_flags=MEMGAS_FLAGS, payload=payload)
                if succs is None:
                    succs, unresolved = build_x86_cfg(blocks)
                # ZERO has two in-region predecessors; TESTQ must be the only way in.
                require_single_entry(summary, succs, unresolved)
            except SummaryMatchError as exc:
                if strict:
                    failures.append(str(exc))
                continue
            found.append(summary)
    if failures:
        raise MemGasSummaryMatchError("unmatched memoryGasCost-like x86 slice(s): " + "; ".join(failures))
    return found


def exit_guard(summary: MemGasSummary, state: SMTState):
    """Where the raw slice leaves through OOG instead of reaching END."""
    s = state.x86_registers.get_register(summary.size_reg)
    return And(s != 0, UGT(s, BitVecVal(MEMGAS_CAP, 64)))


def apply_memgas_summary(summary: MemGasSummary, state: SMTState, *, fresh_prefix: str,
                         profile: X86AOTProfile = AOT_COMPILER_PROFILE) -> SMTState:
    """fee -> T; LastGasCost written back in BOTH representations the raw
    `mov [r13+0x20], rax` writes (side-channel field and callEngine bytes);
    MemLen untouched; S/T2/RAX/RDX and flags fresh."""
    new = state.copy()
    regs = state.x86_registers
    s = regs.get_register(summary.size_reg)
    fee, _, new_last = memory_fee_for_size(state.callengine_memory_size_bytes,
                                           state.callengine_memory_gas_used, s)
    addr = regs.get_register(Register.R13) + BitVecVal(profile.offsets["last_gas_cost"], 64)
    # Same formula with the in-memory limb as the old value: If(expands, total, limb).
    old_limb = state.x86_memory.load_limb(addr, domain=MemoryDomain.CALLENGINE)
    new_limb = memory_fee_for_size(state.callengine_memory_size_bytes, old_limb, s)[2]
    new.x86_memory = new.x86_memory.store_limb(addr, new_limb, domain=MemoryDomain.CALLENGINE)
    new.callengine_memory_gas_used = new_last
    tag = f"{fresh_prefix}_{summary.entry_addr:x}"
    new.x86_registers.set_register(summary.fee_reg, fee)   # also clears its tag
    for reg in summary.clobber_registers:
        new.x86_registers.set_register(reg, BitVec(f"{tag}_{reg.value}", 64))
    for flag in MEMGAS_FLAGS:
        new.x86_registers.set_flag(flag, BitVec(f"{tag}_{flag}", 1))
    return new


def _require_implied(summary: X86Summary, state: SMTState, path_condition, goal, label, timeout_ms):
    from z3 import SolverFor, unsat

    if simplify(goal).eq(BoolVal(True)):
        return
    # The executor's exit-guard split put Not(guard) into this very path
    # condition: refuting path ∧ ¬goal syntactically refutes the full query
    # (which only adds the state assumptions).
    if path_condition is not None and refuted_by_complement(path_condition, Not(goal)):
        return
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=timeout_ms)
    solver.add(*(state.assumptions or []))
    if path_condition is not None:
        solver.add(path_condition)
    solver.add(Not(goal))
    result = solver.check()
    if result != unsat:
        raise SummaryPreconditionError(kind=MEMGAS_SUMMARY_KIND, label=label, premise=goal,
                                       result=str(result), location=summary.start_key)


def require_untagged(summary: X86Summary, state: SMTState) -> None:
    """The lemma state has untagged template registers; the summary leaves them
    untagged. Tagged inputs fall back to raw execution."""
    from state.x86_state import PointerTag

    p: MemGasSummary = summary.payload
    for reg in (p.fee_reg, *p.clobber_registers):
        if state.x86_registers.get_pointer_tag(reg) != PointerTag.NONE:
            raise SummaryPreconditionError(kind=MEMGAS_SUMMARY_KIND, label=f"{reg.value} pointer tag",
                                           premise=str(state.x86_registers.get_pointer_tag(reg)),
                                           result="rejected", location=summary.start_key)


class MemGasSummarySpec:
    kind = MEMGAS_SUMMARY_KIND

    def __init__(self, *, prove_hits: bool = True, proof_timeout_ms: int = 30_000,
                 profile: X86AOTProfile = AOT_COMPILER_PROFILE):
        self.prove_hits = prove_hits
        self.proof_timeout_ms = proof_timeout_ms
        self.profile = profile
        self.proof_stats = {"proven": 0, "cache_hits": 0}
        self._blocks: Sequence[X86Block] = ()

    def discover(self, ctx: SummaryDiscoveryContext, *, strict: bool = False) -> Iterable[X86Summary]:
        self._blocks = ctx.blocks
        return discover_memgas_summaries(ctx.blocks, strict=strict, profile=self.profile)

    def exit_guard(self, summary: X86Summary, state: SMTState):
        return exit_guard(summary.payload, state)

    def lemma(self, summary: X86Summary):
        """The fail-closed per-shape proof (cached); raises MemGasProofError."""
        from .memgas_proof import prove_memgas_slice_cached
        lemma, status = prove_memgas_slice_cached(summary, self._blocks, profile=self.profile,
                                                  timeout_ms=self.proof_timeout_ms)
        self.proof_stats[status] += 1
        return lemma

    def apply(self, summary: X86Summary, state: SMTState, *, fresh_prefix: str,
              path_condition=None, precondition_timeout_ms: int = 5000) -> SMTState:
        if not isinstance(summary.payload, MemGasSummary):
            raise TypeError(f"memgas summary payload must be MemGasSummary, got {type(summary.payload)!r}")
        if self.prove_hits:
            self.lemma(summary)
        require_untagged(summary, state)
        _require_implied(summary, state, path_condition, Not(exit_guard(summary.payload, state)),
                         "exit guard excluded", precondition_timeout_ms)
        return apply_memgas_summary(summary.payload, state, fresh_prefix=fresh_prefix, profile=self.profile)
