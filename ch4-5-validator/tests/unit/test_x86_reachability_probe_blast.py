"""UF refutations retain exact copy/read semantics without inventing SAT witnesses."""
import gzip
from pathlib import Path
import sys
from time import monotonic
from types import SimpleNamespace

import pytest
from z3 import (Array, BitVecs, BitVecSort, Select, Store, Z3Exception,
                is_app, is_quantifier, is_select, is_store, parse_smt2_string,
                sat, unknown, unsat)

import common.isolated_sat as isolated
import verification.block_equivalence as be
import x86_64.cfg_state as cs


def _path():
    x, y, i, j = BitVecs("probe_blast_x probe_blast_y probe_blast_i probe_blast_j", 8)
    memory = Array("probe_blast_mem", BitVecSort(8), BitVecSort(8))
    path = cs.X86Constraints()
    path.add(x * y == 3)
    path.add(Select(Store(memory, i, x * y), j) != 3)
    path.add(i == j)
    return path


def _has_read_over_store(formula):
    work, seen = [formula], set()
    while work:
        term = work.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if is_select(term) and is_store(term.arg(0)):
            return True
        if is_app(term) or is_quantifier(term):
            work.extend(term.children())
    return False


def _unknown_prefix(monkeypatch):
    prefix = cs.PrefixSolver()
    monkeypatch.setattr(prefix, "check", lambda *a, **k: unknown)
    return prefix


def test_no_prefix_probe_exposes_read_over_write_before_refuting(monkeypatch):
    real, probes = cs._bounded_check, []

    def check(solver, timeout, tag="incremental", wall_ms=None):
        if tag == "blast":  # Exercise the UF fallback independently of exact search.
            return unknown
        if tag == "probe":
            assert not any(_has_read_over_store(q) for q in solver.assertions())
            probes.append(solver)
        return real(solver, timeout, tag, wall_ms)

    monkeypatch.setattr(cs, "_bounded_check", check)
    path = _path()
    assert not path.is_possible(1000)
    assert len(probes) == 1 and path._witness is None


@pytest.mark.parametrize("probe_answer", [sat, unknown])
def test_no_prefix_abstract_sat_or_unknown_never_becomes_a_path_witness(monkeypatch, probe_answer):
    calls = []

    def check(solver, timeout, tag="incremental", wall_ms=None):
        calls.append(tag)
        return probe_answer if tag == "probe" else unknown

    monkeypatch.setattr(cs, "_bounded_check", check)
    path = _path()
    assert path.is_possible(1000)
    assert calls.count("probe") == 1 and path._witness is None


def test_no_prefix_probe_blast_oom_keeps_the_path(monkeypatch):
    abstract, simplify, probing = be.abstract_nonlinear_mul, cs.simplify, [False]

    def abstraction(formula):
        result = abstract(formula)
        probing[0] = True
        return result

    def capped_simplify(formula, **kwargs):
        if probing[0] and kwargs.get("blast_select_store"):
            raise Z3Exception("out of memory")
        return simplify(formula, **kwargs)

    monkeypatch.setattr(be, "abstract_nonlinear_mul", abstraction)
    monkeypatch.setattr(cs, "simplify", capped_simplify)
    monkeypatch.setattr(cs, "_bounded_check", lambda *a, **k: unknown)
    path = _path()
    assert path.is_possible(1000) and path._witness is None


@pytest.mark.parametrize("answer", ["unsat", "unknown"])
def test_prefix_last_slot_delegates_original_formula_and_budget(monkeypatch, answer):
    calls = []
    prefix = cs.PrefixSolver()
    prefix.witness_seconds = 0  # the cascade up to the probe; the witness search: test_reachability_witness_search
    monkeypatch.setattr(prefix, "check", lambda conjuncts, timeout:
                        calls.append(("prefix", timeout)) or unknown)
    monkeypatch.setattr(cs, "_bounded_check", lambda solver, timeout, tag:
                        calls.append((tag, timeout)) or unknown)
    path = _path()
    original = path.as_bool()

    def child(query, timeout, **kwargs):
        assert query.eq(original), "delegate the original F, never its UF relaxation"
        calls.append(("child", timeout, kwargs))
        return answer

    monkeypatch.setattr(isolated, "isolated_sat", child)
    assert path.is_possible(17, prefix) == (answer != "unsat")
    assert calls == [("prefix", 17), ("blast", 17),
                     ("child", 170, {"rlimit": 170000, "refute_probe": True})]
    assert path._witness is None


@pytest.mark.parametrize("outcome", ["sat", "unknown", "oom", "transport_error"])
def test_prefix_child_miss_or_failure_keeps_path_without_witness(monkeypatch, outcome):
    prefix = _unknown_prefix(monkeypatch)
    monkeypatch.setattr(cs, "_bounded_check", lambda *args: unknown)
    path = _path()
    original, calls = path.as_bool(), []

    def transport(query, end, **kwargs):
        assert query.eq(original)
        assert kwargs == dict(blast=False, rlimit=10000000, pure_bv=False, refute_probe=True)
        assert end > monotonic()
        calls.append(outcome)
        if outcome == "oom":
            raise MemoryError("child allocation")
        if outcome == "transport_error":
            raise OSError("child unavailable")
        return SimpleNamespace(returncode=0, stdout=outcome, stderr="")

    # Stub only the transport boundary. Parent solver monkeypatches do not
    # cross into a real interpreter; isolated_sat still filters abstract SAT.
    monkeypatch.setattr(isolated, "_run_isolated", transport)
    assert path.is_possible(1000, prefix) and path._witness is None
    assert calls == [outcome]


def test_expensive_probe_blast_stays_in_the_isolated_child(monkeypatch):
    calls, answers = [], iter(["unknown", "unknown", "unsat"])
    monkeypatch.setattr(isolated, "expensive_bitblast", lambda f: True)

    def solve(query, timeout, **kwargs):
        assert query.eq(original)
        calls.append((timeout, kwargs))
        return next(answers)

    monkeypatch.setattr(isolated, "isolated_sat", solve)
    simplify = cs.simplify

    def parent_simplify(formula, **kwargs):
        assert not kwargs.get("blast_select_store"), "expensive view must be built in the child"
        return simplify(formula, **kwargs)

    monkeypatch.setattr(cs, "simplify", parent_simplify)
    path = _path()
    original = path.as_bool()
    assert not path.is_possible(17, cs.PrefixSolver())
    assert calls == [(170, {"rlimit": 170000}),
                     (170, {"blast": True, "rlimit": 170000}),
                     (170, {"rlimit": 170000, "refute_probe": True})]
    assert path._witness is None


def _real_copy_and_word_gas_formula():
    fixture = Path(__file__).with_name("data") / "x86_reachability_copy_word_gas.smt2.gz"
    return parse_smt2_string(gzip.decompress(fixture.read_bytes()).decode())[0]


def test_real_copy_and_word_gas_probe_mathematics_in_process():
    formula = _real_copy_and_word_gas_formula()
    shared = isolated._ProbeBudget(monotonic() + 30, 30000000)
    assert isolated._refute_probe(formula, shared) == "unsat"


@pytest.mark.skipif(sys.platform != "linux", reason="child hard AS boundary requires Linux /proc")
def test_real_copy_and_word_gas_path_refuted_by_actual_child(monkeypatch):
    formula = _real_copy_and_word_gas_formula()
    path = cs.X86Constraints()
    path._constraints = list(formula.children())
    prefix = _unknown_prefix(monkeypatch)
    real = cs._bounded_check

    def check(solver, timeout, tag="incremental", wall_ms=None):
        return unknown if tag == "blast" else real(solver, timeout, tag, wall_ms)

    monkeypatch.setattr(cs, "_bounded_check", check)
    # Correctness regression, not a timing assertion. The same-budget performance
    # comparison is separately archived with the unchanged real query and history.
    assert not path.is_possible(3000, prefix)
    assert path._witness is None
