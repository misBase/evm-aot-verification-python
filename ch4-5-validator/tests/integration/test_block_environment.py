"""Actual codegen returns NUMBER, TIMESTAMP and GASLIMIT as three words."""
import pytest

from tests.integration.test_block_program import load
from verification.block_program import BlockProgramVerifier
from verification.program_verifier import GasCheck
from x86_64.semantics import _CALLENGINE_FIELD_MAP


@pytest.mark.parametrize("bad_offset", [None, 0x50, 0x58, 0x60])
def test_symbolic_block_environment_certificate_and_wrong_field_reads(monkeypatch, bad_offset):
    if bad_offset is not None:
        wrong = "callengine_block_timestamp" if bad_offset == 0x50 else "callengine_block_number"
        monkeypatch.setitem(_CALLENGINE_FIELD_MAP, (bad_offset, 8), wrong)
    result = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=5000,
                                  wall_timeout_seconds=60).verify_program_pair(
        *load("block_environment", GasCheck.FULL))
    if bad_offset is None:
        assert result.verified, result.message
        assert result.certificate.entry.edges
    else:
        assert not result.verified and result.certificate is None
        assert "outcome mismatch" in result.message and "solver=sat" in result.message
