"""A real STATICCALL consumes written memory and returns its success word."""
import pytest

from tests.integration.test_block_program import load
from verification.block_program import BlockProgramVerifier
from verification.program_verifier import GasCheck


@pytest.mark.parametrize("fallback", ["none", "full-program"])
@pytest.mark.parametrize("fault", [None, "call_site", "memory_coordinates"])
def test_host_call_certificate_and_one_sided_faults(monkeypatch, fallback, fault):
    import x86_64.go_function_semantics as host
    if fault == "call_site":
        original = host.GoFunctionSemantics.apply
        def drop_site(self, *args, **kwargs):
            kwargs["evm_pc"] = None
            return original(self, *args, **kwargs)
        monkeypatch.setattr(host.GoFunctionSemantics, "apply", drop_site)
    elif fault == "memory_coordinates":
        monkeypatch.setattr(host, "memory_as_offset_view", lambda memory, base: memory)
    result = BlockProgramVerifier(gas_check=GasCheck.FULL, timeout_ms=5000,
        fallback=fallback, wall_timeout_seconds=60).verify_program_pair(
            *load("block_host_memory", GasCheck.FULL),
            # Force the independent path when testing its host mapping.
            candidates={} if fallback == "full-program" else None)
    if fault is None:
        assert result.verified, result.message
    else:
        assert not result.verified and result.certificate is None
        assert "mismatch" in result.message
