"""A transported scalar assignment is accepted only after exact original-F replay."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest
import z3 as z

import common.isolated_sat as isolated
from verification.block_equivalence import _parse_transport


def formula():
    x, y = z.BitVecs("scalar_x scalar_y", 64)
    return z.And(x == 1, y == 1, x*y == 1, z.Bool("scalar_b"))


def payload():
    return {"answer": "sat", "constants": [
        {"name": "scalar_x", "sort": "BV", "width": 64, "value": 1},
        {"name": "scalar_y", "sort": "BV", "width": 64, "value": 1},
        {"name": "scalar_b", "sort": "Bool", "width": 0, "value": True},
    ]}


def respond(monkeypatch, value, returncode=0):
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: SimpleNamespace(
        returncode=returncode, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload=value))))


def test_parent_rebuilds_original_context_model_without_creating_a_context(monkeypatch):
    query, calls = formula(), []
    def run(command, **kw):
        calls.append((command, kw))
        sent = z.And(*z.parse_smt2_string(kw["input"]))
        check = z.Solver(); check.add(query != sent)
        assert check.check() == z.unsat
        return SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload=payload())))
    monkeypatch.setattr(isolated.subprocess, "run", run)
    monkeypatch.setattr(z, "Context", lambda *a, **kw: pytest.fail("new parent Context"))
    model = isolated.isolated_small_mul_model(query, 5000)
    assert model is not None and model.ctx is query.ctx
    assert z.is_true(model.eval(query, model_completion=True))
    command, options = calls[0]
    assert command[-1] == "1" and command[-2] == "0"
    assert 0 < options["timeout"] <= 5


@pytest.mark.parametrize("bad", ["missing", "extra", "duplicate", "wrong_sort", "wrong_width",
                                  "wrong_value", "negative", "overflow", "bool_int", "bv_bool",
                                  "extra_field", "not_sat", "not_object"])
def test_malformed_or_false_models_are_rejected(monkeypatch, bad):
    value = copy.deepcopy(payload())
    if bad == "missing": value["constants"].pop()
    elif bad == "extra": value["constants"].append({"name": "extra", "sort": "BV", "width": 64, "value": 0})
    elif bad == "duplicate": value["constants"][1] = value["constants"][0].copy()
    elif bad == "wrong_sort": value["constants"][0]["sort"] = "Int"
    elif bad == "wrong_width": value["constants"][0]["width"] = 32
    elif bad == "wrong_value": value["constants"][0]["value"] = 0
    elif bad == "negative": value["constants"][0]["value"] = -1
    elif bad == "overflow": value["constants"][0]["value"] = 2**64
    elif bad == "bool_int": value["constants"][2]["value"] = 1
    elif bad == "bv_bool": value["constants"][0]["value"] = True
    elif bad == "extra_field": value["constants"][0]["extra"] = 0
    elif bad == "not_sat": value["answer"] = "unsat"
    else: value = "sat"
    respond(monkeypatch, value)
    assert isolated.isolated_small_mul_model(formula(), 5000) is None


@pytest.mark.parametrize("kind", ["binder", "lambda", "open_var", "uf", "array", "int", "real"])
def test_entire_formula_eligibility_is_checked_before_launch(monkeypatch, kind):
    x = z.BitVec("eligibility_x", 8)
    if kind == "binder": extra = z.ForAll(x, x == x)
    elif kind == "lambda": extra = z.Select(z.Lambda(x, x), x) == x
    elif kind == "open_var": extra = z.Var(0, z.BoolSort())
    elif kind == "uf": extra = z.Function("unsupported_uf", x.sort(), x.sort())(x) == 0
    elif kind == "array": extra = z.Select(z.K(x.sort(), x), x) == 0
    elif kind == "int": extra = z.Int("unsupported_int") == 0
    else: extra = z.Real("unsupported_real") == 0
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("unsupported candidate launched"))
    assert isolated.isolated_small_mul_model(z.And(formula(), extra), 5000) is None


@pytest.mark.parametrize("failure", ["timeout", "os", "memory", "signal", "garbage"])
def test_resource_or_process_failure_only_misses_a_witness(monkeypatch, failure):
    def run(command, **kw):
        if failure == "timeout": raise subprocess.TimeoutExpired(command, kw["timeout"])
        if failure == "os": raise OSError("unavailable")
        if failure == "memory": raise MemoryError()
        return SimpleNamespace(returncode=-6 if failure == "signal" else 0, stdout="sat" if failure == "signal" else "invalid JSON")
    monkeypatch.setattr(isolated.subprocess, "run", run)
    assert isolated.isolated_small_mul_model(formula(), 5000) is None


def test_budget_covers_eligibility_and_serialization_without_launching_after_expiry(monkeypatch):
    import verification.block_equivalence as be
    clock = [0.0]
    monkeypatch.setattr(isolated, "monotonic", lambda: clock[0])
    native = be._to_smt2
    def serialize(query):
        text = native(query)
        clock[0] = 0.101
        return text
    monkeypatch.setattr(be, "_to_smt2", serialize)
    monkeypatch.setattr(isolated.subprocess, "run", lambda *a, **kw: pytest.fail("deadline already expired"))
    assert isolated.isolated_small_mul_model(formula(), 100) is None
    # An already-expired entry does not even serialize.
    monkeypatch.setattr(be, "_to_smt2", lambda *a: pytest.fail("expired entry serialized"))
    assert isolated.isolated_small_mul_model(formula(), 0) is None


def test_expiry_during_parent_replay_discards_an_otherwise_valid_model(monkeypatch):
    clock = [0.0]
    monkeypatch.setattr(isolated, "monotonic", lambda: clock[0])
    respond(monkeypatch, payload())
    native = z.ModelRef.eval
    def eval_model(model, *args, **kw):
        result = native(model, *args, **kw)
        clock[0] = 0.101
        return result
    monkeypatch.setattr(z.ModelRef, "eval", eval_model)
    assert isolated.isolated_small_mul_model(formula(), 100) is None


@pytest.mark.parametrize("when", ["entry", "after_child"])
def test_node_abort_propagates(monkeypatch, when):
    import common.node_monitor as monitor
    monkeypatch.setattr(monitor, "_ABORT", ["stop" if when == "entry" else None])
    def run(*a, **kw):
        monitor._ABORT[0] = "stop"
        return SimpleNamespace(returncode=0, stdout=json.dumps(dict(parsed_alpha=_parse_transport(kw["input"])[1], payload=payload())))
    monkeypatch.setattr(isolated.subprocess, "run", run)
    with pytest.raises(monitor.NodeMemoryExceeded):
        isolated.isolated_small_mul_model(formula(), 5000)


def test_child_search_uses_input_aware_freshness_and_never_reports_narrow_unsat(monkeypatch):
    import common.fresh_symbols as fresh
    x, y = z.BitVecs("child_model_x child_model_y", 64)
    occupied = z.BitVec("small_operand!0", 1)
    native, created = fresh.FreshConst, []
    def collide(sort, prefix):
        created.append(True)
        return occupied if len(created) == 1 else native(sort, prefix)
    monkeypatch.setattr(fresh, "FreshConst", collide)
    query = z.And(x == 1, y == 1, x*y == 1, occupied == 1)
    end = isolated.monotonic()+5
    value = isolated._small_mul_payload(query, end)
    assert value is not None and len(created) >= 3
    model = isolated._scalar_model(query, isolated._scalar_constants(query, end), value, end)
    assert z.is_true(model.eval(query, model_completion=True))
    # The unrestricted original is SAT, while the onebit candidate is UNSAT.
    miss = z.And(x == 2, y == 2, x*y == 4)
    check = z.Solver(); check.add(miss); assert check.check() == z.sat
    assert isolated._small_mul_payload(miss, isolated.monotonic()+5) is None
    assert isolated._small_mul_payload(z.And(x*y == 5, x*y == 6), isolated.monotonic()+5) is None


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS boundary requires Linux /proc")
@pytest.mark.parametrize("sample,sha", [
    ("prefix", "bc73a675b79a8a4c93c950e69d0910d7261b0e6587d361e1a1293a6d9d01b6b3"),
    ("blast", "26c05a1f2743ea600b522d974ae492cb032c7dd27cdb18325634fef6dd087e8e"),
])
def test_real_safe_row0_queries_retain_their_original_valid_witness(sample, sha):
    data = gzip.decompress((Path(__file__).parent/"data"/f"18089_model_row0_{sample}.smt2.gz").read_bytes())
    assert hashlib.sha256(data).hexdigest() == sha
    query = z.And(*z.parse_smt2_string(data.decode()))
    model = isolated.isolated_small_mul_model(query, 5000)
    assert model is not None and z.is_true(model.eval(query, model_completion=True))


@pytest.mark.skipif(sys.platform != "linux", reason="hard AS boundary requires Linux /proc")
def test_actual_child_memory_and_time_limits_do_not_harm_the_parent(monkeypatch):
    import common.node_monitor as monitor
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: 2)
    assert isolated.isolated_small_mul_model(formula(), 5000) is None
    monkeypatch.setattr(monitor, "memory_headroom_mb", lambda: None)
    assert isolated.isolated_small_mul_model(formula(), 1) is None
    check = z.Solver(); check.add(z.Bool("surviving_parent")); assert check.check() == z.sat
