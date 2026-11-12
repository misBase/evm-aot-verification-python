"""Inner-cap stop classification uses the active cap, not a restored outer cap.

This exercises production control flow and a real SQLite cache with controlled
memory/solver boundaries; it does not allocate native OOM-sized formulas.
"""
from types import SimpleNamespace

import pytest
import z3

import common.isolated_sat as isolated
import common.node_monitor as monitor
import verification.block_equivalence as be
from verification import proof_cache
import x86_64.cfg_state as cs


@pytest.mark.parametrize("raised", [False, True], ids=["answered", "raised"])
@pytest.mark.parametrize("reason", ["canceled", "Resource limits hit in check"])
@pytest.mark.parametrize("at_inner_cap", [True, False], ids=["memory-stop", "ordinary-timeout"])
def test_inner_cap_memory_unknown_is_not_a_cached_timeout(monkeypatch, tmp_path, reason, at_inner_cap, raised):
    allocated_mb, settings = [100], []
    monkeypatch.setattr(cs, "_CAPS", [])
    monkeypatch.setattr(cs, "_WATCH", {"tripped": False})
    monkeypatch.setattr(cs, "_LAST_EXIT", {"over": False})
    monkeypatch.setattr(cs, "Z3_get_estimated_alloc_size", lambda: allocated_mb[0] * 2**20)
    monkeypatch.setattr(cs, "set_param", lambda name, value: settings.append((name, value)))
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    monkeypatch.setattr(monitor, "_ABORT", [None])
    monkeypatch.setattr(be, "QUERY_MEMORY_MB", 20)
    monkeypatch.setattr(isolated, "expensive_bitblast", lambda query: False)
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "proof.sqlite"))

    class StoppedSolver:
        def set(self, *args, **kwargs):
            pass

        def add(self, *args):
            pass

        def check(self):
            assert cs._CAPS == [200, 120]
            allocated_mb[0] = 120 if at_inner_cap else 100
            if raised:  # Z3 may stop with an exception instead of an unknown answer
                raise z3.Z3Exception(reason)
            return z3.unknown

        def reason_unknown(self):
            return reason

    monkeypatch.setattr(be, "Then", lambda *args: SimpleNamespace(solver=StoppedSolver))
    query = z3.BitVec("nested_memory_byte", 8) == 1
    with cs.z3_memory_cap(100):
        if raised and not at_inner_cap:  # not a memory stop: the exception is the caller's
            with pytest.raises(z3.Z3Exception):
                be.solve_pure_bv(query, 1000)
            return
        assert be.solve_pure_bv(query, 1000) == "unknown"
        assert cs._CAPS == [200]

    assert cs._CAPS == []
    assert settings == [("memory_high_watermark_mb", value) for value in (200, 120, 200, 0)]
    cached = proof_cache.cached_answer(proof_cache.query_key("bv_abstraction", query), 1)
    assert cached == (None if at_inner_cap else "unknown")
    assert cs.memory_tripped() is at_inner_cap
