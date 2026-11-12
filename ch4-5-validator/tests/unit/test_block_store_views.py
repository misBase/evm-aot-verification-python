"""Conditional Store alignment is query-scoped and preserves the full BV domain."""
import gzip
from pathlib import Path
from time import monotonic

import pytest
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, Bool, ForAll, If, Lambda,
                Not, Select, Store, Var, parse_smt2_string, substitute)

import verification.block_equivalence as be


def query(label, *, sign=True, wrong_address=False, wrong_value=False, base_value=None):
    mem = Array(f"sv_{label}_mem", BitVecSort(64), BitVecSort(8))
    base, address, read = (BitVec(f"sv_{label}_{n}", 64) for n in ("base", "address", "read"))
    negative = Bool(f"sv_{label}_negative")
    index = BitVec(f"sv_{label}_index", 64)
    logical = Store(mem, address, If(negative, BitVecVal(255, 8), BitVecVal(0, 8)))
    absolute = Store(Lambda([index], Select(mem, index - base)),
                     base + address + int(wrong_address), BitVecVal(254 if wrong_value else 255, 8))
    formula = And(negative if sign else Not(negative),
                  Select(logical, read) != Select(absolute, base + read))
    if base_value is not None:
        formula = And(formula, base == base_value)
    return formula


@pytest.mark.parametrize("base_value", [None, 0, (1 << 64) - 1])
def test_symbolic_base_and_modular_wrap_are_not_restricted(base_value):
    formula = query(f"wrap_{base_value}", base_value=base_value)
    _, answer, lemmas = be.refute_store_views(formula, 3000)
    assert answer == "unsat" and lemmas and all(o.proved for o in lemmas)
    assert any(o.name.startswith("store_view_read") for o in lemmas)
    assert any(c.name.startswith("store_view_value") for o in lemmas for c in o.lemmas)


@pytest.mark.parametrize("changes", [dict(wrong_address=True), dict(wrong_value=True)])
def test_wrong_store_field_cannot_refute_a_real_counterexample(changes):
    formula = query(f"wrong_{changes}", **changes)
    assert be.solve_query(formula, 1000) == "sat"
    unchanged, answer, lemmas = be.refute_store_views(formula, 3000)
    assert answer == "unknown" and unchanged.eq(formula) and not lemmas


def test_conditional_bytes_are_not_reused_under_another_base():
    good, bad = query("conditional", sign=True), query("conditional", sign=False)
    assert be.refute_store_views(good, 3000)[1] == "unsat"
    assert be.solve_query(bad, 1000) == "sat"
    unchanged, answer, lemmas = be.refute_store_views(bad, 3000)
    assert answer == "unknown" and unchanged.eq(bad) and not lemmas


def test_unknown_and_expired_deadlines_leave_the_original_query(monkeypatch):
    formula = query("unknown")
    monkeypatch.setattr(be, "solve_query", lambda *a, **kw: "unknown")
    unchanged, answer, lemmas = be.refute_store_views(formula, 3000)
    assert answer == "unknown" and unchanged.eq(formula) and not lemmas
    unchanged, answer, lemmas = be.refute_store_views(formula, 3000, monotonic() - 1)
    assert answer == "unknown" and unchanged.eq(formula) and not lemmas


def test_binders_and_free_vars_are_not_treated_as_ground_reads():
    formula = query("binder")
    index = BitVec("sv_binder_read", 64)
    for candidate in (ForAll([index], formula), substitute(formula, (index, Var(0, BitVecSort(64))))):
        unchanged, answer, lemmas = be.refute_store_views(candidate, 3000)
        assert answer == "unknown" and unchanged.eq(candidate) and not lemmas


def test_store_order_is_not_changed_even_when_write_addresses_alias():
    mem = Array("sv_order_mem", BitVecSort(64), BitVecSort(8))
    base, a, b, index = (BitVec(f"sv_order_{n}", 64) for n in ("base", "a", "b", "index"))
    logical = Store(Store(mem, a, BitVecVal(11, 8)), b, BitVecVal(22, 8))
    absolute = Store(Store(Lambda([index], Select(mem, index - base)), base + b, BitVecVal(22, 8)),
                     base + a, BitVecVal(11, 8))
    formula = And(a == b, Select(logical, a) != Select(absolute, base + a))
    assert be.solve_query(formula, 1000) == "sat"
    unchanged, answer, lemmas = be.refute_store_views(formula, 3000)
    assert answer == "unknown" and unchanged.eq(formula) and not lemmas


def test_real_4418_capture_is_refuted_with_conditional_store_dependencies():
    path = Path(__file__).with_name("data") / "block_4418_x86_maps_1_0.smt2.gz"
    formula = And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))
    _, answer, lemmas = be.refute_store_views(formula, 30000)
    assert answer == "unsat" and lemmas and all(o.proved for o in lemmas)
    reads = [o for o in lemmas if o.name.startswith("store_view_read")]
    assert len(reads) == 20
    assert any(c.name.startswith("offset_view_step") for o in reads for c in o.lemmas)
    assert any(c.name.startswith("store_view_value") for o in reads for c in o.lemmas)


def prefix_query(label, *, wrong_prefix=False, reverse=False, wrong_value=False):
    mem = Array(f"sv_prefix_{label}_mem", BitVecSort(64), BitVecSort(8))
    base, p, a, b, read, index = (BitVec(f"sv_prefix_{label}_{n}", 64)
                                for n in ("base", "p", "a", "b", "read", "index"))
    negative = Bool(f"sv_prefix_{label}_negative")
    shared = Store(mem, p, BitVecVal(33, 8))
    view_root = Store(mem, p, BitVecVal(34, 8)) if wrong_prefix else shared
    logical = Store(Store(shared, a, If(negative, BitVecVal(11, 8), BitVecVal(0, 8))),
                    b, BitVecVal(22, 8))
    writes = [(a, 12 if wrong_value else 11), (b, 22)]
    absolute = Lambda([index], Select(view_root, index - base))
    for address, value in (reversed(writes) if reverse else writes):
        absolute = Store(absolute, base + address, BitVecVal(value, 8))
    # p, a, b, and read remain unconstrained: the prefix may alias every later access.
    return And(negative, Select(logical, read) != Select(absolute, base + read)), (p, a, b, read)


@pytest.mark.parametrize("alias", [False, True])
def test_identical_stored_prefix_is_preserved_with_possible_or_actual_aliases(alias):
    formula, (p, a, b, read) = prefix_query(f"ok_{alias}")
    if alias:
        formula = And(formula, p == a, a == b, b == read)
    _, answer, lemmas = be.refute_store_views(formula, 5000)
    assert answer == "unsat" and lemmas and all(o.proved for o in lemmas)


@pytest.mark.parametrize("change", ["wrong_prefix", "reverse", "wrong_value"])
def test_stored_prefix_alignment_does_not_omit_or_reorder_writes(change):
    formula, (p, a, b, read) = prefix_query(change, **{change: True})
    if change == "wrong_prefix":
        formula = And(formula, read == p, p != a, p != b)
    elif change == "reverse":
        formula = And(formula, a == b, read == a)
    else:
        formula = And(formula, read == a, a != b)
    assert be.solve_query(formula, 1000) == "sat"
    unchanged, answer, lemmas = be.refute_store_views(formula, 5000)
    assert answer == "unknown" and unchanged.eq(formula) and not lemmas


def test_real_stored_prefix_capture_keeps_all_checked_dependencies():
    path = Path(__file__).with_name("data") / "h2_19169_stored_prefix_stack.smt2.gz"
    formula = And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))
    _, answer, lemmas = be.refute_store_views(formula, 30000)
    assert answer == "unsat" and lemmas and all(o.proved for o in lemmas)
    reads = [o for o in lemmas if o.name.startswith("store_view_read")]
    assert len(reads) == 12 and all(o.required_lemmas for o in reads)
    assert any(o.name == "divrem_congruence" for o in lemmas)
