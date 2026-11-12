"""MUL summary per-hit glue proof（mul_proof.py）的单元测试。"""

import dataclasses

import pytest
from z3 import BitVec, BitVecVal, unknown

from tests.integration.test_single_ins_equivalence import X86_MUL_CORE_HEX_SEQUENCE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries import mul_proof
from x86_64.summaries.base import SummaryDiscoveryContext
from x86_64.summaries.mul import (
    MulSummarySpec,
    StackLimbLocation,
    discover_mul_summaries,
)
from x86_64.summaries.mul_proof import (
    MulProofError,
    _MulSliceProof,
    clear_proof_cache,
    prove_mul_slice_cached,
    prove_mul_slice_refines_summary,
)


@pytest.fixture(autouse=True)
def _isolated_proof_cache():
    clear_proof_cache()
    yield
    clear_proof_cache()


def _blocks(hex_code: str = X86_MUL_CORE_HEX_SEQUENCE):
    return identify_basic_blocks(disassemble_hex(hex_code, 0))


def _ctx(blocks) -> SummaryDiscoveryContext:
    return SummaryDiscoveryContext(
        blocks=blocks,
        blocks_by_addr={block.start_addr: block for block in blocks},
        block_index={block.start_addr: i for i, block in enumerate(blocks)},
    )


def _summary_and_slice(hex_code: str = X86_MUL_CORE_HEX_SEQUENCE):
    blocks = _blocks(hex_code)
    summaries = discover_mul_summaries(blocks, strict=True)
    assert len(summaries) == 1
    summary = next(iter(summaries.values()))
    block = next(b for b in blocks if b.start_addr == summary.start_block_addr)
    slice_insns = block.instructions[
        summary.start_instruction_index:summary.continuation_instruction_index
    ]
    return summary, slice_insns


def test_canonical_slice_proof_passes():
    summary, slice_insns = _summary_and_slice()
    prove_mul_slice_refines_summary(summary, slice_insns)


def test_spec_discover_proves_hits_and_counts_stats():
    blocks = _blocks()
    spec = MulSummarySpec(prove_hits=True)
    summaries = list(spec.discover(_ctx(blocks), strict=True))
    assert len(summaries) == 1
    assert spec.proof_stats == {
        "proven": 1,
        "cache_hits": 0,
        "failed_cache_hits": 0,
    }


def test_spec_discover_reuses_proof_cache():
    blocks = _blocks()
    spec = MulSummarySpec(prove_hits=True)
    list(spec.discover(_ctx(blocks), strict=True))
    list(spec.discover(_ctx(blocks), strict=True))
    assert spec.proof_stats["proven"] == 1
    assert spec.proof_stats["cache_hits"] == 1


def test_spec_discover_skips_proof_when_disabled(monkeypatch):
    def _boom(*_args, **_kwargs):
        raise AssertionError("proof must not run when prove_hits=False")

    monkeypatch.setattr(mul_proof, "prove_mul_slice_refines_summary", _boom)
    blocks = _blocks()
    spec = MulSummarySpec(prove_hits=False)
    summaries = list(spec.discover(_ctx(blocks), strict=True))
    assert len(summaries) == 1
    assert spec.proof_stats["proven"] == 0


def test_tampered_location_fails_closed():
    summary, slice_insns = _summary_and_slice()
    # p2 的 stack offset 改错：matcher 的 location 与 slice 真实数据流不再一致。
    bad_locs = (
        summary.p_limb_locs[0],
        StackLimbLocation(summary.p_limb_locs[1].offset + 8),
        summary.p_limb_locs[2],
        summary.p_limb_locs[3],
    )
    bad_summary = dataclasses.replace(summary, p_limb_locs=bad_locs)
    with pytest.raises(MulProofError, match=r"entry=0x.*solver_result=sat"):
        prove_mul_slice_refines_summary(bad_summary, slice_insns)


def test_truncated_tail_fails_closed():
    summary, slice_insns = _summary_and_slice()
    with pytest.raises(MulProofError, match=r"tail.*expected exactly 4 result stores"):
        prove_mul_slice_refines_summary(summary, slice_insns[:-1])


def test_solver_unknown_fails_closed(monkeypatch):
    class _UnknownSolver:
        def __init__(self, *_args, **_kwargs):
            pass

        def set(self, **_kwargs):
            pass

        def add(self, *_args):
            pass

        def check(self):
            return unknown

    monkeypatch.setattr(mul_proof, "SolverFor", _UnknownSolver)
    summary, slice_insns = _summary_and_slice()
    with pytest.raises(MulProofError, match=r"solver_result=unknown"):
        prove_mul_slice_refines_summary(summary, slice_insns)


def test_failure_is_cached_with_from_cache_marker():
    summary, slice_insns = _summary_and_slice()
    bad_summary = dataclasses.replace(
        summary,
        result_stack_offsets=(-64, -56, -48, -32),
    )
    with pytest.raises(MulProofError) as first:
        prove_mul_slice_cached(bad_summary, slice_insns)
    assert not first.value.from_cache
    with pytest.raises(MulProofError) as second:
        prove_mul_slice_cached(bad_summary, slice_insns)
    assert second.value.from_cache
    assert str(first.value) == str(second.value)


def test_checkpoint_rejects_duplicate_register_obligations():
    summary, slice_insns = _summary_and_slice()
    proof = _MulSliceProof(summary, slice_insns, timeout_ms=10_000, label="dup")
    value = BitVec("dup_value", 64)
    with pytest.raises(MulProofError, match=r"checkpoint register overlap"):
        proof._prove_segment_outputs(
            mul_proof.SMTState(),
            [],
            (
                ("z0", Register.R8, value),
                ("carry0", Register.R8, BitVecVal(0, 64)),
            ),
            label="dup-check",
        )
