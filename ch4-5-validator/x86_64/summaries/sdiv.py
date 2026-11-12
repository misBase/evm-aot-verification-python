"""Checked candidates for the complete amd64 signed-division dispatch."""
from __future__ import annotations

from dataclasses import dataclass

from z3 import BitVecSort, BitVecVal, BoolSort, If, is_expr

from common.arithmetic import _abs256, _is_negative, sdiv_semantics
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
from .div import (CALLER_SAVED, DIV_FLAGS, DivSummary, _Parser, _callengine_effects,
                  _forwarded_limb, _looks_like_entry as _div_entry, require_stack_geometry)


SDIV_SUMMARY_KIND = "sdiv"
_BASES = {Register.R13, Register.R14, Register.R15}


@dataclass(frozen=True)
class SDivSummary:
    entry_addr: int
    start_block_addr: int
    start_instruction_index: int
    continuation_addr: int
    covered_block_addrs: tuple[int, ...]
    dividend_offsets: tuple[int, int, int, int]
    divisor_offsets: tuple[int, int, int, int]
    divs: tuple[DivSummary, DivSummary, DivSummary, DivSummary]  # ++, +-, --, -+
    clobber_registers: tuple[Register, ...]


class SDivSummaryMatchError(SummaryMatchError):
    pass


class _SignedParser(_Parser):
    def fail(self, why):
        raise SDivSummaryMatchError(f"0x{self.addr:x}: {why}")

    def positive(self, sign_jump):
        _, ops = self.expect("mov", immediate=0, is_memory=False, dest_size=8)
        zero_reg = ops.get("dest_reg")
        if zero_reg is None or zero_reg in _BASES:
            self.fail("bad zero-test register")
        offsets = tuple(self.stack("or", dest_reg=zero_reg) for _ in range(4))
        if offsets != tuple(offsets[0] + 8 * k for k in range(4)):
            self.fail("operand limbs are not contiguous")
        self.expect("test", dest_reg=zero_reg, src_reg=zero_reg)
        target = self.jump("je")
        _, ops = self.expect("mov", is_memory=True, base_reg=Register.R14,
                             memory_size=8, offset=offsets[3], index_reg=None)
        sign_reg = ops.get("dest_reg")
        if sign_reg is None or sign_reg in _BASES:
            self.fail("bad sign-test register")
        self.expect("shr", dest_reg=sign_reg, immediate=63, is_memory=False)
        self.expect("test", dest_reg=sign_reg, src_reg=sign_reg)
        if self.jump(sign_jump) != target:
            self.fail("zero and sign tests have different targets")
        return offsets, target

    def negate(self, offsets):
        temp = None
        for k, offset in enumerate(offsets):
            _, ops = self.expect("mov", immediate=0, is_memory=False, dest_size=8)
            temp = temp or ops.get("dest_reg")
            if temp is None or temp in _BASES or ops.get("dest_reg") != temp:
                self.fail("bad negation register")
            if self.stack("sub" if k == 0 else "sbb", dest_reg=temp) != offset:
                self.fail("negation reads the wrong limb")
            if self.stack("mov", src_reg=temp, dest_reg=None) != offset:
                self.fail("negation writes the wrong limb")

    def unsigned(self, x, y):
        saved = []
        while not _div_entry(self.insn_at, self.addr):
            if len(saved) == 2:
                self.fail("unsigned DIV entry missing")
            _, ops = self.expect("mov", is_memory=False, dest_size=8, src_size=8)
            dest, src = ops.get("dest_reg"), ops.get("src_reg")
            if (src not in (Register.RAX, Register.RDX) or dest is None
                    or dest in _BASES | {Register.RAX, Register.RDX}
                    or src in {source for _, source in saved}
                    or dest in {target for target, _ in saved}):
                self.fail("bad RAX/RDX save")
            saved.append((dest, src))
        while self.insn_at[self.addr].mnemonic.lower() == "nop":
            self.addr += self.insn_at[self.addr].size
        inner = _Parser(self.insn_at, self.addr, self.profile).parse()
        if inner["x"] != x or inner["y"] != y:
            self.fail("unsigned DIV uses different operands")
        self.addr = inner["end"]
        for dest, src in saved:
            self.expect("mov", dest_reg=src, src_reg=dest, is_memory=False, dest_size=8)
        return inner

    def parse_signed(self):
        x, nonpositive_x = self.positive("jne")
        y, nonpositive_y = self.positive("jne")
        if x[0] != y[0] + 32:
            self.fail("operand stack slots are not adjacent")
        divs = [self.unsigned(x, y)]
        end = self.jump("jmp")
        self.at("NONPOSITIVE_Y", nonpositive_y)
        self.negate(y)
        divs.append(self.unsigned(x, y))
        negate_result = self.jump("jmp")
        self.at("NONPOSITIVE_X", nonpositive_x)
        other_y, nonnegative_y = self.positive("je")
        if other_y != y:
            self.fail("second divisor sign check uses different operands")
        self.negate(x)
        self.negate(y)
        divs.append(self.unsigned(x, y))
        if self.jump("jmp") != end:
            self.fail("same-sign arms do not join")
        self.at("NONNEGATIVE_Y", nonnegative_y)
        self.negate(x)
        divs.append(self.unsigned(x, y))
        self.at("NEGATE_RESULT", negate_result)
        self.negate(y)
        self.at("END", end)
        return x, y, end, divs


def _looks_like_signed_entry(insn_at, addr):
    window = []
    while len(window) < 11 and addr in insn_at:
        instruction = insn_at[addr]
        addr += instruction.size
        if instruction.mnemonic.lower() != "nop":
            window.append(instruction)
    if [i.mnemonic.lower() for i in window] != [
            "mov", "or", "or", "or", "or", "test", "je", "mov", "shr", "test", "jne"]:
        return False
    return parse_operands(window[6]).get("jump_target") == parse_operands(window[10]).get("jump_target")


def discover_sdiv_summaries(blocks, *, strict=False, profile=AOT_COMPILER_PROFILE):
    block_at = {b.start_addr: b for b in blocks}
    owner = {i.addr: (b, n) for b in blocks for n, i in enumerate(b.instructions)}
    insn_at = {i.addr: i for b in blocks for i in b.instructions}
    found, failures = [], []
    succs = unresolved = None
    covered_until = -1
    for entry in sorted(insn_at):
        if (insn_at[entry].mnemonic.lower() == "nop"
                or entry < covered_until
                or not _looks_like_signed_entry(insn_at, entry)):
            continue
        try:
            x, y, end, parsed_divs = _SignedParser(insn_at, entry, profile).parse_signed()
            if end not in block_at:
                raise SDivSummaryMatchError(f"join 0x{end:x} is not a block start")
            block, index = owner[entry]
            covered = tuple(sorted({block.start_addr} | {a for a in block_at if entry < a < end}))
            if any(block_at[a].end_addr > end for a in covered):
                raise SDivSummaryMatchError("a covered block runs past the join")
            divs = []
            for p in parsed_divs:
                start, offset = owner[p["entry"]]
                inner_covered = tuple(sorted({start.start_addr} | {
                    a for a in block_at if p["entry"] < a < p["end"]}))
                divs.append(DivSummary(p["entry"], start.start_addr, offset, p["end"], inner_covered,
                                       p["x"], p["y"], p["index"], p["sp"], p["resume"], p["clobbers"]))
            clobbers = {parse_operands(i).get("dest_reg") for a, i in insn_at.items()
                        if entry <= a < end and i.mnemonic.lower() not in ("cmp", "test", "nop")}
            clobbers.discard(None)
            clobbers -= _BASES  # the only base writes are the parsed builtin RESUME reloads
            clobbers = tuple(sorted(clobbers, key=lambda r: r.value))
            payload = SDivSummary(entry, block.start_addr, index, end, covered, x, y,
                                  tuple(divs), clobbers)
            summary = X86Summary(SDIV_SUMMARY_KIND, entry, block.start_addr, index,
                                 SummaryContinuation(end), covered, clobbers, DIV_FLAGS, payload)
            if succs is None:
                succs, unresolved = build_x86_cfg(blocks)
            require_single_entry(summary, succs, unresolved)
        except SummaryMatchError as exc:
            if strict:
                failures.append(str(exc))
            continue
        found.append(summary)
        covered_until = end
    if failures:
        raise SDivSummaryMatchError("unmatched SDIV-like x86 slice(s): " + "; ".join(failures))
    return found


def apply_sdiv_summary(summary, state, *, fresh_prefix, profile=AOT_COMPILER_PROFILE,
                       path_condition=None):
    new = state.copy()
    r14 = state.x86_registers.get_register(Register.R14)
    from common.store_forwarding import shared_forward_scope
    shared_forward_scope()

    def operand(offsets):
        return Uint256(*(_forwarded_limb(state.x86_memory.load_limb(
            r14 + BitVecVal(offset, 64), domain=MemoryDomain.STACK)) for offset in offsets)).to_bv256()

    x, y = operand(summary.dividend_offsets), operand(summary.divisor_offsets)
    new.x86_memory = new.x86_memory.store_256bit(
        r14 + BitVecVal(summary.dividend_offsets[0], 64), _abs256(x), domain=MemoryDomain.STACK)
    new.x86_memory = new.x86_memory.store_256bit(
        r14 + BitVecVal(summary.divisor_offsets[0], 64), sdiv_semantics(x, y), domain=MemoryDomain.STACK)
    tag = f"{fresh_prefix}_{summary.entry_addr:x}"
    from verification.block_summaries import _leaves
    inputs = [value for value in _leaves(state).values() if is_expr(value)]
    inputs.extend(state.assumptions or [])
    inputs.extend(getattr(state, "summary_assumed_premises", []))
    if path_condition is not None:
        inputs.append(path_condition)
    symbols = FreshSymbols(*inputs)
    took = symbols.const(BoolSort(), f"{tag}_builtin")
    effects = [_callengine_effects(div, profile) for div in summary.divs]

    def selected(values, size):
        values = [BitVecVal(value % (1 << size), size) for value in values]
        return If(_is_negative(x), If(_is_negative(y), values[2], values[3]),
                  If(_is_negative(y), values[1], values[0]))

    r13 = state.x86_registers.get_register(Register.R13)
    for k, (field, size, attr, _) in enumerate(effects[0]):
        values = [effect[k][3] for effect in effects]
        for i in range(size):
            addr = r13 + BitVecVal(profile.offsets[field] + i, 64)
            old = new.x86_memory.load_byte(addr, domain=MemoryDomain.CALLENGINE)
            byte = selected([(value >> (8 * i)) & 0xff for value in values], 8)
            new.x86_memory = new.x86_memory.store_byte(addr, If(took, byte, old),
                                                      domain=MemoryDomain.CALLENGINE)
        old = getattr(state, attr)
        setattr(new, attr, If(took, selected(values, old.size()), old))
    for attr in ("return_offset", "return_length"):
        old = getattr(state, attr)
        setattr(new, attr, If(took, BitVecVal(0, old.size()), old))
    for reg in summary.clobber_registers:
        new.x86_registers.set_register(reg, symbols.const(BitVecSort(64), f"{tag}_{reg.value}"))
    for reg in CALLER_SAVED:
        new.x86_registers.clear_pointer_tag(reg)
    for flag in DIV_FLAGS:
        new.x86_registers.set_flag(flag, symbols.const(BitVecSort(1), f"{tag}_{flag}"))
    return new, took


class SDivSummarySpec:
    kind = SDIV_SUMMARY_KIND

    def __init__(self, *, proof_timeout_ms=30_000, profile=AOT_COMPILER_PROFILE):
        self.proof_timeout_ms, self.profile = proof_timeout_ms, profile
        self.proof_stats = {"proven": 0, "cache_hits": 0}
        self._blocks = ()

    def discover(self, ctx, *, strict=False):
        self._blocks = ctx.blocks
        return discover_sdiv_summaries(ctx.blocks, strict=strict, profile=self.profile)

    def lemma(self, summary):
        from .signed_proof import prove_signed_slice_cached
        lemma, status = prove_signed_slice_cached(summary, self._blocks, profile=self.profile,
                                                 timeout_ms=self.proof_timeout_ms)
        self.proof_stats[status] += 1
        return lemma

    def apply(self, summary, state, *, fresh_prefix, path_condition=None, precondition_timeout_ms=5000):
        from .signed_proof import SignedProofError

        for reg in set(summary.clobber_registers) | set(CALLER_SAVED):
            if state.x86_registers.get_pointer_tag(reg) != PointerTag.NONE:
                raise SummaryPreconditionError(kind=self.kind, label=f"{reg.value} pointer tag",
                    premise=str(state.x86_registers.get_pointer_tag(reg)), result="rejected",
                    location=summary.start_key)
        try:
            self.lemma(summary)
        except SignedProofError as exc:
            raise SummaryPreconditionError(kind=self.kind, label=f"raw slice proof: {exc}",
                premise=path_condition, result="inconclusive", location=summary.start_key) from exc
        require_stack_geometry(summary, state, path_condition, precondition_timeout_ms)
        return apply_sdiv_summary(summary.payload, state, fresh_prefix=fresh_prefix,
                                  profile=self.profile, path_condition=path_condition)[0]
