import json
from verification.block_equivalence import _parse_transport
"""Large nonlinear paths are isolated before incremental push/add internalizes them."""
from pathlib import Path
import subprocess
import sys

import pytest
from z3 import BitVecs, BoolVal, Solver, URem, set_param

import common.isolated_sat as isolated
import verification.block_equivalence as be
from x86_64.cfg_state import PrefixSolver, X86Constraints


def _path():
    x, y, z = BitVecs("reach_isolated_x reach_isolated_y reach_isolated_z", 512)
    path = X86Constraints()
    path.add(URem(x * y, z) == 1)
    return path


@pytest.mark.parametrize("answers,kept", [
    (["sat"], True), (["unsat"], False), (["unknown", "unsat"], False),
    (["unknown", "unknown", "sat"], True), (["unknown"] * 3, True),
])
@pytest.mark.parametrize("incremental", [False, True])
def test_only_unsat_prunes_and_no_old_model_is_reused(monkeypatch, answers, kept, incremental):
    calls, results = [], iter(answers)
    def solve(query, wall, **kw):
        calls.append((query, wall, kw))
        return next(results)
    monkeypatch.setattr(isolated, "isolated_sat", solve)
    monkeypatch.setattr(be, "abstract_nonlinear_mul", lambda f: pytest.fail("last probe prepared in parent"))
    prefix = PrefixSolver() if incremental else None
    if prefix is not None:
        monkeypatch.setattr(prefix, "check", lambda *a, **k: pytest.fail("expensive path reached push/add"))
    path = _path()
    assert path.is_possible(17, prefix) is kept
    assert path._witness is None and len(calls) == len(answers)
    assert all(wall == 170 and kw["rlimit"] == 170000 for _, wall, kw in calls)
    if len(calls) >= 2:
        assert calls[1][2]["blast"] is True
    if len(calls) >= 3:
        assert calls[2][2]["refute_probe"] is True
        assert calls[2][0].eq(path.as_bool())


def test_small_paths_keep_the_incremental_solver_and_its_valid_witness(monkeypatch):
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a, **k: pytest.fail("small query isolated"))
    x, _ = BitVecs("reach_small_x reach_small_y", 8)
    path = X86Constraints()
    path.add(x == 5)
    assert path.is_possible(1000, PrefixSolver()) and path._witness is not None


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS limit uses Linux /proc")
def test_child_has_its_own_global_memory_parameters_and_rlimit():
    solver = Solver()
    solver.add(BoolVal(True))
    text = solver.to_smt2()
    try:
        set_param("memory_high_watermark_mb", 1)
        child = subprocess.run([sys.executable, str(Path(isolated.__file__).resolve()), "3000", "64", "0", "0"],
                               input=text, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
    finally:
        set_param("memory_high_watermark_mb", 0)
    assert child.returncode == 0
    assert json.loads(child.stdout) == dict(parsed_alpha=_parse_transport(text)[1], payload="sat")
    assert isolated.isolated_sat(_path().as_bool(), 3000, rlimit=1) == "unknown"
