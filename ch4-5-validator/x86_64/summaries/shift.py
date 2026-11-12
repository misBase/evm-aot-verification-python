"""Proved summaries for the amd64 256-bit shift dispatch.

Discovery proposes a slice from the high-limb TEST to the common join. The
per-slice lemma, not the template match, establishes coverage and all effects.
The negative SAR arm fills with ones; its outer sign branch remains raw.
"""
from __future__ import annotations

from dataclasses import dataclass

from z3 import BitVec, BitVecVal, If, LShR, ZeroExt

from common.uint256 import Uint256
from state.smt_state import MemoryDomain
from state.x86_state import PointerTag
from x86_64.disassembler import parse_operands
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import Register

from .base import (SummaryContinuation, SummaryMatchError, SummaryPreconditionError,
                   X86Summary, require_single_entry)
from .calldataload import (LimbLocation, _limb_location_expr,
                          _second_operand_location)
from .div import DIV_FLAGS, _forwarded_limb, require_stack_geometry


SHIFT_SUMMARY_KIND = "shift"


@dataclass(frozen=True)
class ShiftSummary:
    entry_addr: int
    continuation_addr: int
    high_reg: Register
    count: LimbLocation
    value_offsets: tuple[int, int, int, int]
    direction: str
    clobber_registers: tuple[Register, ...]


def discover_shift_summaries(blocks, *, strict=False):
    """Recognize the common SHR/SHL dispatch and either arm of SAR."""
    insns = sorted((i for b in blocks for i in b.instructions), key=lambda i: i.addr)
    meaningful = [i for i in insns if i.mnemonic.lower() != "nop"]
    by_addr = {i.addr: n for n, i in enumerate(meaningful)}
    owner = {i.addr: (b, n) for b in blocks for n, i in enumerate(b.instructions)}
    block_at = {b.start_addr: b for b in blocks}
    succs = unresolved = None
    found = []
    for pos, first in enumerate(meaningful):
        window = meaningful[pos:pos + 13]
        if len(window) != 13 or [i.mnemonic.lower() for i in window[:8]] != [
                "test", "jne", "mov", "cmp", "jae", "mov", "and", "jne"]:
            continue
        p = [parse_operands(i) for i in window]
        high = p[0].get("dest_reg")
        if (high is None or p[0].get("src_reg") != high or p[0].get("is_memory")
                or p[2].get("dest_reg") != Register.RCX or p[2].get("dest_size") != 8
                or p[3].get("dest_reg") != Register.RCX or p[3].get("immediate") != 256
                or p[4].get("jump_target") != p[1].get("jump_target")
                or p[5].get("src_reg") != Register.RCX
                or p[6].get("dest_reg") != Register.RCX or p[6].get("immediate") != 63):
            continue
        count = _second_operand_location(window[2])
        if count is None or p[2].get("index_reg") is not None:
            continue
        loads = p[8:12]
        if any(i.mnemonic.lower() != "mov" for i in window[8:12]) or any(
                not o.get("is_memory") or o.get("base_reg") != Register.R14
                or o.get("memory_size") != 8 or o.get("index_reg") is not None
                or o.get("dest_reg") is None for o in loads):
            continue
        offsets = tuple(o["offset"] for o in loads)
        if offsets != tuple(offsets[0] + 8 * k for k in range(4)):
            continue
        # The zero-count edge names the common join, independent of padding.
        if (window[12].mnemonic.lower() != "cmp" or p[12].get("immediate") != 0
                or p[12].get("dest_reg") != p[5].get("dest_reg")):
            continue
        if pos + 13 >= len(meaningful) or meaningful[pos + 13].mnemonic.lower() != "je":
            continue
        join = parse_operands(meaningful[pos + 13]).get("jump_target")
        overflow = p[1].get("jump_target")
        if join not in block_at or overflow not in by_addr or not first.addr < overflow < join:
            continue
        tail = [i for i in meaningful[by_addr[overflow]:] if i.addr < join]
        if not tail:
            continue
        stores = [parse_operands(i) for i in tail]
        if any(i.mnemonic.lower() != "mov" for i in tail) or any(
                not o.get("is_memory") or o.get("base_reg") != Register.R14
                or o.get("src_reg") is not None or o.get("index_reg") is not None
                or o.get("immediate") not in (0, -1, 0xffffffff, 0xffffffffffffffff)
                for o in stores):
            continue
        fill = stores[0]["immediate"] != 0
        if any((o["immediate"] != 0) != fill for o in stores):
            continue
        written = sorted(a for o in stores for a in range(o["offset"], o["offset"] + o["memory_size"]))
        if written != list(range(offsets[0], offsets[0] + 32)):
            continue
        code = [i for i in insns if first.addr <= i.addr < join]
        shifts = [i.mnemonic.lower() for i in code if i.mnemonic.lower() in ("shr", "shl")
                  and parse_operands(i).get("src_reg") == Register.RCX]
        if fill:
            direction = "ones-right"
        elif shifts.count("shr") == 4 and shifts.count("shl") == 3:
            direction = "right"
        elif shifts.count("shl") == 4 and shifts.count("shr") == 3:
            direction = "left"
        else:
            continue
        # Any extra side effect is rejected by the full-state replay theorem.
        clobbers = {parse_operands(i).get("dest_reg") for i in code
                    if i.mnemonic.lower() not in ("cmp", "test", "nop")}
        clobbers.discard(None)
        if clobbers & {Register.R13, Register.R14, Register.R15}:
            continue
        clobbers = tuple(sorted(clobbers, key=lambda r: r.value))
        block, index = owner[first.addr]
        covered = tuple(sorted({block.start_addr} | {b.start_addr for b in blocks
                                                    if first.addr < b.start_addr < join}))
        if any(block_at[a].end_addr > join for a in covered):
            continue
        payload = ShiftSummary(first.addr, join, high, count, offsets, direction, clobbers)
        summary = X86Summary(SHIFT_SUMMARY_KIND, first.addr, block.start_addr, index,
                             SummaryContinuation(join), covered, clobbers, DIV_FLAGS, payload)
        if succs is None:
            succs, unresolved = build_x86_cfg(blocks)
        try:
            require_single_entry(summary, succs, unresolved)
        except SummaryMatchError:
            if strict:
                raise
            continue
        found.append(summary)
    return found


def apply_shift_summary(summary, state, *, fresh_prefix):
    new = state.copy()
    r14 = state.x86_registers.get_register(Register.R14)
    from common.store_forwarding import shared_forward_scope
    shared_forward_scope()
    value = Uint256(*(_forwarded_limb(state.x86_memory.load_limb(
        r14 + BitVecVal(o, 64), domain=MemoryDomain.STACK)) for o in summary.value_offsets)).to_bv256()
    low = _forwarded_limb(_limb_location_expr(summary.count, state))
    count = ZeroExt(192, low)
    if summary.direction == "left":
        shifted, overflow = value << count, BitVecVal(0, 256)
    elif summary.direction == "ones-right":
        shifted, overflow = ~LShR(~value, count), BitVecVal((1 << 256) - 1, 256)
    else:
        shifted, overflow = LShR(value, count), BitVecVal(0, 256)
    result = If(state.x86_registers.get_register(summary.high_reg) == 0, shifted, overflow)
    new.x86_memory = new.x86_memory.store_256bit(
        r14 + BitVecVal(summary.value_offsets[0], 64), result, domain=MemoryDomain.STACK)
    tag = f"{fresh_prefix}_{summary.entry_addr:x}"
    for reg in summary.clobber_registers:
        new.x86_registers.set_register(reg, BitVec(f"{tag}_{reg.value}", 64))
    for flag in DIV_FLAGS:
        new.x86_registers.set_flag(flag, BitVec(f"{tag}_{flag}", 1))
    return new


class ShiftSummarySpec:
    kind = SHIFT_SUMMARY_KIND

    def __init__(self, *, proof_timeout_ms=30_000):
        self.proof_timeout_ms = proof_timeout_ms
        self.proof_stats = {"proven": 0, "cache_hits": 0}

    def discover(self, ctx, *, strict=False):
        self._blocks = ctx.blocks
        return discover_shift_summaries(ctx.blocks, strict=strict)

    def lemma(self, summary):
        from .shift_proof import prove_shift_slice_cached
        lemma, status = prove_shift_slice_cached(summary, self._blocks, timeout_ms=self.proof_timeout_ms)
        self.proof_stats[status] += 1
        return lemma

    def apply(self, summary, state, *, fresh_prefix, path_condition=None, precondition_timeout_ms=5000):
        # The generic proof's metadata must also instantiate, including untouched overflow arms.
        for reg in summary.clobber_registers:
            if state.x86_registers.get_pointer_tag(reg) != PointerTag.NONE:
                raise SummaryPreconditionError(kind=self.kind, label=f"{reg.value} pointer tag",
                    premise=str(state.x86_registers.get_pointer_tag(reg)), result="rejected",
                    location=summary.start_key)
        self.lemma(summary)
        require_stack_geometry(summary, state, path_condition, precondition_timeout_ms)
        return apply_shift_summary(summary.payload, state, fresh_prefix=fresh_prefix)
