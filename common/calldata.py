"""Shared calldata word semantics for EVM IR and x86 summaries."""

from typing import Optional

from z3 import (
    BitVecRef,
    BitVecVal,
    BoolRef,
    BoolVal,
    Concat,
    Extract,
    If,
    Select,
    ULT,
)


def _offset64_and_overflow(offset_bv: BitVecRef) -> tuple[BitVecRef, BoolRef]:
    if offset_bv.size() == 64:
        return offset_bv, BoolVal(False)
    if offset_bv.size() == 256:
        return (
            Extract(63, 0, offset_bv),
            Extract(255, 64, offset_bv) != BitVecVal(0, 192),
        )
    raise ValueError(f"Offset must be 64 or 256 bits, got {offset_bv.size()}")


def calldataload_no_overflow_assumption(offset_bv: BitVecRef) -> Optional[BoolRef]:
    """Return the no-overflow assumption used by the optimized IR semantics."""
    if offset_bv.size() == 64:
        return None
    if offset_bv.size() == 256:
        return Extract(255, 64, offset_bv) == BitVecVal(0, 192)
    raise ValueError(f"Offset must be 64 or 256 bits, got {offset_bv.size()}")


def calldataload_word(
    calldata,
    calldatasize_64: BitVecRef,
    offset_bv: BitVecRef,
    *,
    omit_overflow_guard: bool = False,
) -> BitVecRef:
    """Model EVM CALLDATALOAD / Go getData(input, offset, 32).

    The returned word is big-endian: byte at ``offset`` becomes bits 255..248.
    If the 256-bit offset does not fit in uint64, the guarded semantics returns
    zero.  Callers that add the no-overflow precondition may set
    ``omit_overflow_guard=True`` to avoid carrying the dead branch.
    """
    if calldatasize_64.size() != 64:
        raise ValueError(
            f"calldatasize context must be 64 bits, got {calldatasize_64.size()}"
        )

    offset_64, offset_overflow = _offset64_and_overflow(offset_bv)
    effective_start = If(ULT(calldatasize_64, offset_64), calldatasize_64, offset_64)
    remaining = calldatasize_64 - effective_start
    bytes_list = [
        If(
            ULT(BitVecVal(i, 64), remaining),
            Select(calldata, effective_start + BitVecVal(i, 64)),
            BitVecVal(0, 8),
        )
        for i in range(32)
    ]
    loaded_data = Concat(*bytes_list)
    if omit_overflow_guard or offset_bv.size() == 64:
        return loaded_data
    return If(offset_overflow, BitVecVal(0, 256), loaded_data)
