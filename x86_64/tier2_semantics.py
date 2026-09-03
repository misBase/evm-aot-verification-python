"""Shared closed-form Z3 semantics for proven Tier-2 copy loops."""

from __future__ import annotations

from z3 import (
    And,
    BitVecVal,
    Concat,
    Extract,
    If,
    LShR,
    Select,
    ULE,
    ULT,
)


def byte_of(qword, k):
    """Return byte ``k`` from a little-endian 64-bit word."""

    return Extract(7, 0, LShR(qword, BitVecVal(8, 64) * k))


def qword_le(mem_offset_space, off):
    """Read a little-endian qword from an offset-space byte array."""

    bytes_ = [Select(mem_offset_space, off + BitVecVal(k, 64)) for k in range(8)]
    return Concat(*reversed(bytes_))


def overlay_byte(tmp0, m1, dt0, count, w):
    """Overlay ``count`` low bytes of ``tmp0`` at ``dt0`` over byte array ``m1``."""

    return If(
        And(ULE(dt0, w), ULT(w, dt0 + count)),
        byte_of(tmp0, w - dt0),
        Select(m1, w),
    )


def copy_region_byte(m0, d0, s0, copied, w):
    """MCOPY closed form for ``copied`` bytes from ``s0`` to ``d0``."""

    return If(
        And(ULE(d0, w), ULT(w, d0 + copied)),
        Select(m0, w - d0 + s0),
        Select(m0, w),
    )


def high_region_byte(m0, d0, s0, size0, remaining, w):
    """FromHigh closed form: top region already copied, ``remaining`` left."""

    return If(
        And(ULE(d0 + remaining, w), ULT(w, d0 + size0)),
        Select(m0, w - d0 + s0),
        Select(m0, w),
    )


def mcopy_no_wrap_premises(d0, s0, size0):
    return [
        ULT(size0, BitVecVal(1 << 63, 64)),
        ULE(d0, d0 + size0),
        ULE(s0, s0 + size0),
    ]


def getdata_byte(source, off, length, k):
    """EVM getData byte semantics: out-of-range source bytes are zero."""

    return If(ULT(off + k, length), Select(source, off + k), BitVecVal(0, 8))


def byte_copy_region(source, m0, dst, off, size, remaining, w, *, length=None):
    """Closed form for backwards byte-copy loops.

    ``remaining`` is the loop counter at the current cutpoint.  Bytes in
    ``[dst + remaining, dst + size)`` have already been written.
    """

    def source_byte(k):
        if length is None:
            return Select(source, off + k)
        return getdata_byte(source, off, length, k)

    return If(
        And(ULE(dst + remaining, w), ULT(w, dst + size)),
        source_byte(w - dst),
        Select(m0, w),
    )
