import json
from verification.block_equivalence import _parse_transport
"""The last reachability fallback shares one child budget, and only refutes F."""
from pathlib import Path
from time import monotonic
from types import SimpleNamespace
import gzip
import sys

import pytest
import z3 as z

import common.isolated_sat as isolated
import verification.block_equivalence as be
from verification import proof_cache
import x86_64.cfg_state as cs


def budget(resources=300000, seconds=2):
    return isolated._ProbeBudget(monotonic() + seconds, resources)


def sat_formula():
    word = z.BitVec("refute_sat_word", 64)
    return z.And(word == 2, be._memory_cost(word) > 0)


def test_existing_potential_can_refute_after_abstract_sat_with_empty_identity_records():
    word = z.BitVec("refute_monotone_word", 64)
    formula = z.And(z.ULE(word, 7), z.UGT(be._memory_cost(word), be._memory_cost(z.BitVecVal(7, 64))))
    original_check = type(z.Solver()).check
    assert isolated._refute_probe(formula, budget()) == "unsat"
    assert type(z.Solver()).check is original_check


def test_true_original_sat_never_becomes_a_refutation():
    formula = sat_formula()
    solver = z.Solver(); solver.add(formula)
    assert solver.check() == z.sat and z.is_true(solver.model().eval(formula, model_completion=True))
    assert isolated._refute_probe(formula, budget()) == "unknown"


class NativeStub:
    def __init__(self, answer=z.unsat, reason=""):
        self.parameters, self.answer, self.reason = {}, answer, reason

    def set(self, *args, **kwargs):
        self.parameters.update(dict(zip(args[::2], args[1::2])))
        self.parameters.update(kwargs)

    def add(self, *args):
        pass

    def check(self, *args):
        return self.answer

    def reason_unknown(self):
        return self.reason


def test_proxy_keeps_original_per_query_limits_even_after_larger_set():
    native = NativeStub()
    proxy = isolated._ProbeSolver(native, budget(10000000, 10), 1000)
    proxy.set(rlimit=250)
    assert native.parameters == {"timeout": 1000, "rlimit": 250}
    proxy.check()
    assert native.parameters == {"timeout": 1000, "rlimit": 250}
    proxy.set("timeout", 5000, "rlimit", 1000)
    assert native.parameters == {"timeout": 1000, "rlimit": 250}
    proxy.check()
    assert native.parameters == {"timeout": 1000, "rlimit": 250}
    proxy.set(timeout=2, rlimit=3)
    assert native.parameters == {"timeout": 2, "rlimit": 3}
    proxy.check()
    assert native.parameters == {"timeout": 2, "rlimit": 3}


def test_original_incomplete_query_retains_qf_then_general_factory_order(monkeypatch):
    calls = []
    def factory(timeout_ms, formula=None):
        calls.append((timeout_ms, formula is None))
        return NativeStub(z.unknown if len(calls) == 1 else z.unsat, "incomplete")
    monkeypatch.setattr(be, "_solver", factory)
    with isolated._probe_adapters(budget()):
        assert be.solve_query(z.BoolVal(False), 100) == "unsat"
    assert [general for _, general in calls] == [False, True]
    assert calls[1][0] <= calls[0][0] == 100


def test_child_adapters_bypass_disk_cache_and_keep_original_pure_bv_tactic(monkeypatch, tmp_path):
    original_then, tactics = be.Then, []
    def then(*args):
        tactics.append(args)
        return original_then(*args)
    monkeypatch.setattr(be, "Then", then)
    monkeypatch.setattr(proof_cache, "enabled", lambda: pytest.fail("child consulted old cache"))
    old_cache = str(tmp_path / "old.sqlite")
    monkeypatch.setenv("BLOCK_PROOF_CACHE", old_cache)
    with isolated._probe_adapters(budget()):
        assert be.solve_query(z.BoolVal(False), 100) == "unsat"
        assert be.solve_pure_bv(z.BoolVal(False), 100) == "unsat"
        wide = z.BitVec("refute_wide", 512)
        assert be.solve_query(z.And(z.BoolVal(False), z.UDiv(wide, wide + 1) == 3), 100) == "unsat"
    assert tactics == [("simplify", "ackermannize_bv", "bit-blast", "sat")]
    assert isolated.os.environ["BLOCK_PROOF_CACHE"] == old_cache
    assert not Path(old_cache).exists()


def test_private_solver_memory_sentinel_is_unknown(monkeypatch):
    monkeypatch.setattr(be, "_solve_query", lambda *args: "memory")
    with isolated._probe_adapters(budget()):
        assert be.solve_query(z.BoolVal(False), 100) == "unknown"


@pytest.mark.parametrize("phase", ["mul", "potential"])
def test_any_nested_child_attempt_is_logged_and_refused(monkeypatch, capsys, phase):
    def nested(*args):
        return isolated.isolated_sat(z.BoolVal(True), 100)
    monkeypatch.setattr(be, "value_cut" if phase == "mul" else "refute_over_bounded_potential", nested)
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("nested child started"))
    assert isolated._refute_probe(sat_formula(), budget()) == "unknown"
    assert "nested isolation refused" in capsys.readouterr().err


def test_unproved_actual_dependency_prevents_unsat(monkeypatch):
    monkeypatch.setattr(be, "refute_over_bounded_potential", lambda f, t:
                        (f, "unsat", (be.Obligation("broken", "false", "unknown"),)))
    assert isolated._refute_probe(sat_formula(), budget()) == "unknown"


def test_late_memo_success_is_rejected_even_without_another_solver(monkeypatch):
    word = z.BitVec("refute_cached_identity", 8)
    assert be._identity_proof(word, word) is not None
    clock = [0.0]
    monkeypatch.setattr(isolated, "monotonic", lambda: clock[0])
    shared = isolated._ProbeBudget(1, 100000)
    def cached_late():
        clock[0] = 2
        return be._identity_proof(word, word)
    with pytest.raises(isolated._ProbeBudgetExceeded):
        shared.call(cached_late)


def test_late_cached_potential_success_cannot_refute(monkeypatch):
    clock = [0.0]
    monkeypatch.setattr(isolated, "monotonic", lambda: clock[0])
    monkeypatch.setattr(be, "value_cut", lambda f: (f, False))
    def cached_late(formula, timeout):
        clock[0] = 2
        return formula, "unsat", ()
    monkeypatch.setattr(be, "refute_over_bounded_potential", cached_late)
    assert isolated._refute_probe(z.BoolVal(False), isolated._ProbeBudget(1, 100000)) == "unknown"


def test_preparation_resource_overshoot_is_rejected_not_hidden():
    x, y = z.BitVecs("refute_prepare_x refute_prepare_y", 64)
    shared = budget(1)
    with pytest.raises(isolated._ProbeBudgetExceeded):
        shared.call(z.simplify, x+y+x+y+x+y+x+y)
    assert shared.spent() > 1  # Postchecking does not undo actual preparation consumption.


def test_parent_serialization_over_resource_budget_never_starts_child(monkeypatch):
    x, y = z.BitVecs("refute_serialize_x refute_serialize_y", 64)
    def serialize(formula):
        z.simplify(x+y+x+y+x+y+x+y)
        return "(assert true)"
    monkeypatch.setattr(be, "_to_smt2", serialize)
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("overspent child started"))
    assert isolated.isolated_sat(z.BoolVal(True), 1000, rlimit=1, refute_probe=True) == "unknown"


def test_late_parent_serialization_never_starts_child(monkeypatch):
    clock = [0.0]
    monkeypatch.setattr(isolated, "monotonic", lambda: clock[0])
    def serialize(formula):
        clock[0] = 2
        return "(assert true)"
    monkeypatch.setattr(be, "_to_smt2", serialize)
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("late child started"))
    assert isolated.isolated_sat(z.BoolVal(True), 1000, rlimit=100000, refute_probe=True) == "unknown"


def test_overloaded_input_is_unknown_without_starting_child(monkeypatch):
    from tests.unit.test_overloaded_serialization import formulas
    original, _ = formulas()
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("unsafe child started"))
    assert isolated.isolated_sat(original, 1000, rlimit=100000, refute_probe=True) == "unknown"


@pytest.mark.parametrize("kwargs", [{}, {"pure_bv": True}, {"scalar_model": True}])
def test_existing_protocol_arguments_have_no_new_flags(monkeypatch, kwargs):
    commands = []
    monkeypatch.setattr(isolated.subprocess, "run", lambda command, **kw:
                        commands.append(command) or SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload={"answer":"unknown"} if kwargs.get("scalar_model") else "sat"))))
    isolated._run_isolated(z.BoolVal(True), monotonic()+1, **kwargs)
    assert len(commands[0]) == (8 if kwargs.get("scalar_model") else 7)


@pytest.mark.parametrize("answer", ["sat", "nonsense"])
def test_new_mode_accepts_only_unsat_not_a_candidate_sat(monkeypatch, answer):
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw:
                        SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload=answer))))
    assert isolated.isolated_sat(z.BoolVal(True), 1000, rlimit=100000, refute_probe=True) == "unknown"


def test_refutation_mode_dispatch_charges_transport_and_forwards_absolute_deadline(monkeypatch):
    commands = []
    monkeypatch.setattr(isolated.subprocess, "run", lambda command, **kw:
                        commands.append(command) or SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload="unsat"))))
    assert isolated.isolated_sat(z.BoolVal(False), 1000, rlimit=100000, refute_probe=True) == "unsat"
    assert commands[0][-3:-1] == ["0", "1"]
    assert 0 < int(commands[0][5]) <= 100000
    assert float(commands[0][-1]) > monotonic()


def test_prefix_and_exact_blast_precede_only_the_last_new_slot(monkeypatch):
    calls = []
    prefix = SimpleNamespace(check=lambda *a: calls.append("prefix") or z.unknown, witness_seconds=0)
    monkeypatch.setattr(cs, "_bounded_check", lambda s, t, tag:
                        calls.append(tag) or z.unknown)
    def child(formula, wall, **kwargs):
        calls.append(("child", wall, kwargs))
        return "unknown"
    monkeypatch.setattr(isolated, "isolated_sat", child)
    word = z.BitVec("refute_caller_word", 8)
    path = cs.X86Constraints(); path.add(word*word == 2)
    assert path.is_possible(17, prefix)
    assert calls == ["prefix", "blast", ("child", 170, {"rlimit": 170000, "refute_probe": True})]
    assert path._witness is None


def test_no_prefix_probe_before_exact_route_is_unchanged(monkeypatch):
    calls = []
    monkeypatch.setattr(cs, "_bounded_check", lambda s, t, tag:
                        calls.append(tag) or z.unsat)
    monkeypatch.setattr(isolated, "isolated_sat", lambda *a, **kw: pytest.fail("old first probe isolated"))
    word = z.BitVec("refute_no_prefix_word", 8)
    path = cs.X86Constraints(); path.add(word*word == 2)
    assert not path.is_possible(17)
    assert calls == ["probe"]


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS boundary requires Linux /proc")
def test_real_current_safe_query_refuted_in_one_original_budget():
    path = Path(__file__).with_name("data") / "x86_reachability_potential_c19b.smt2.gz"
    values = z.parse_smt2_string(gzip.decompress(path.read_bytes()).decode())
    formula = values[0] if len(values) == 1 else z.And(*values)
    assert isolated.isolated_sat(formula, 10000, rlimit=10000000, refute_probe=True) == "unsat"


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS boundary requires Linux /proc")
def test_real_child_sat_and_resource_failure_keep_parent_usable():
    assert isolated.isolated_sat(sat_formula(), 3000, rlimit=100000, refute_probe=True) == "unknown"
    assert isolated.isolated_sat(z.BoolVal(False), 1, rlimit=1, refute_probe=True) == "unknown"
    solver = z.Solver(); solver.add(z.Bool("refute_parent_usable"))
    assert solver.check() == z.sat


def test_a_double_rlimit_count_still_gives_the_child_an_integer_budget(monkeypatch):
    # Past 2^32 Z3 reports "rlimit count" as a double; the child parses its budget with int().
    from types import SimpleNamespace
    import z3
    counts = iter([5_000_000_000.0, 5_000_000_123.0])
    class Stats:
        def get_key_value(self, key):
            return next(counts)
    monkeypatch.setattr(z3.Solver, "statistics", lambda self: Stats())
    seen = []
    def run(command, **kwargs):
        seen.append(command)
        return SimpleNamespace(returncode=1, stdout="", stderr="")
    monkeypatch.setattr(isolated.subprocess, "run", run)
    word = z3.BitVec("double_count_word", 8)
    isolated._run_isolated(word * word == 2, monotonic() + 5, rlimit=10_000_000, refute_probe=True)
    assert seen and seen[0][5] == str(10_000_000 - 123)
