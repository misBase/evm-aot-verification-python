"""Relational abstractions for proven deterministic memory-copy effects."""

from z3 import ArraySort, BitVecSort, Function, If, ULT, simplify


_BV64 = BitVecSort(64)
_BV8 = BitVecSort(8)
_MEMORY = ArraySort(_BV64, _BV8)

# This UF is not an axiom that the concrete machine loop implements MCOPY.
# The x86 side may use it only after the exact Tier-2 template and premises
# have selected a separately proved MCOPY summary.  Once both sides are known
# to implement the same deterministic transformation, replacing its result by
# an arbitrary shared function of all semantic inputs is a conservative
# relational abstraction: later proof obligations must hold for every output
# Array the UF can denote.
_RELATIONAL_MCOPY_MEMORY = Function(
    "relational_mcopy_memory",
    _MEMORY,
    _BV64,
    _BV64,
    _BV64,
    _MEMORY,
)

_RELATIONAL_GETDATA_COPY_MEMORY = Function(
    "relational_getdata_copy_memory",
    _MEMORY,
    _MEMORY,
    _BV64,
    _BV64,
    _BV64,
    _BV64,
    _MEMORY,
)


def relational_mcopy_memory(memory, dst, src, size):
    """Return the shared abstract result of one proven MCOPY transformation."""

    return _RELATIONAL_MCOPY_MEMORY(
        memory,
        simplify(dst),
        simplify(src),
        simplify(size),
    )


def relational_getdata_copy_memory(
    memory,
    source,
    dst,
    offset,
    size,
    source_length,
):
    """Return the shared abstract result of one proven getData copy.

    This is the CALLDATACOPY/CODECOPY analogue of
    :func:`relational_mcopy_memory`.  It may be used only by certificate
    execution where the x86 Tier-2 template/lemma has already established the
    exact getData transformation.  Keeping every semantic input explicit means
    an offset, length, source, or destination mismatch still produces
    unrelated results.
    """

    normalized_offset = If(
        ULT(source_length, offset),
        source_length,
        offset,
    )
    return _RELATIONAL_GETDATA_COPY_MEMORY(
        memory,
        source,
        simplify(dst),
        simplify(normalized_offset),
        simplify(size),
        simplify(source_length),
    )


__all__ = [
    "relational_getdata_copy_memory",
    "relational_mcopy_memory",
]
