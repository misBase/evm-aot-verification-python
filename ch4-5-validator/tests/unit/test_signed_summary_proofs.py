"""Real raw replay gates; no mocked solver or arithmetic lemma."""
import pytest

from tests.integration.test_single_ins_equivalence import X86_SDIV_CORE_HEX_SEQUENCE, X86_SMOD_CORE_HEX_SEQUENCE
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.summaries.sdiv import discover_sdiv_summaries
from x86_64.summaries.smod import discover_smod_summaries
from x86_64.summaries.signed_proof import SignedProofError, clear_proof_cache, prove_signed_slice, prove_signed_slice_cached

CASES = [
    (X86_SDIV_CORE_HEX_SEQUENCE, discover_sdiv_summaries),
    ('49c7850001000000000000' + X86_SMOD_CORE_HEX_SEQUENCE, discover_smod_summaries),
]


@pytest.mark.parametrize('code,discover', CASES)
def test_real_depth_truncated_replay_is_rejected(code, discover):
    blocks = identify_basic_blocks(disassemble_hex(code))
    [summary] = discover(blocks, strict=True)
    with pytest.raises(SignedProofError, match='raw'):
        prove_signed_slice(summary, blocks, profile=AOT_COMPILER_PROFILE, max_depth=1)


@pytest.mark.slow
@pytest.mark.parametrize('code,discover', CASES)
def test_wrong_builtin_operand_slots_match_but_cannot_be_certified(code, discover):
    bad = code.replace('49c7452800000000c3', '49c7452810000000c3', 1)
    assert bad != code
    blocks = identify_basic_blocks(disassemble_hex(bad))
    [summary] = discover(blocks, strict=True)
    clear_proof_cache()
    with pytest.raises(SignedProofError, match='effect_'):
        prove_signed_slice_cached(summary, blocks, profile=AOT_COMPILER_PROFILE)
    with pytest.raises(SignedProofError) as failure:
        prove_signed_slice_cached(summary, blocks, profile=AOT_COMPILER_PROFILE)
    assert failure.value.from_cache
    clear_proof_cache()
