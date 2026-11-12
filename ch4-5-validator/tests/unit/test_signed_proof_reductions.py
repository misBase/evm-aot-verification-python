"""Small real-solver checks for the signed gate's generic proof reductions."""
from dataclasses import replace

import pytest
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, BoolVal, ForAll,
                FreshConst, Lambda, Not, Select, SolverFor, Store,
                Z3_OP_UNINTERPRETED, is_const, is_quantifier, is_select,
                simplify, substitute, unsat)

from common.store_forwarding import forward_selects
from verification.block_equivalence import Obligation
from x86_64.summaries.signed_proof import (
    _abstract_input_bytes, _effect_parts, refute_signed_effect,
)


def _array(name):
    return Array(name, BitVecSort(64), BitVecSort(8))


def _check(formula):
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=1000)
    solver.add(formula)
    return solver.check()


def _walk(term):
    seen, work = set(), [term]
    while work:
        node = work.pop()
        if node.get_id() not in seen:
            seen.add(node.get_id())
            yield node
            work.extend(node.children())


def _many_writes(*, wrong_last=False):
    root = _array("many_write_root")
    addresses = [BitVecVal(i, 64) for i in range(70)]
    values = [BitVec(f"many_write_value_{i}", 8) for i in range(70)]
    left = right = root
    # The final tested location is beyond the first 64 discovered addresses.
    for i in reversed(range(70)):
        left = Store(left, addresses[i], values[i])
    for i in range(70):
        value = values[i] + 1 if wrong_last and i == 69 else values[i]
        right = Store(right, addresses[i], value)
    return left == right, addresses


def test_effect_parts_retain_all_written_addresses_beyond_64():
    goal, addresses = _many_writes()
    parts = _effect_parts(goal)
    assert len(parts) == 9
    covered = {node.arg(1).get_id() for part in parts for node in _walk(part) if is_select(node)}
    assert {address.get_id() for address in addresses} <= covered
    answer, records = refute_signed_effect(BoolVal(True), goal, 1000)
    assert answer == "unsat" and len(records) == len(parts)
    assert all(record.proved for record in records)


def test_effect_parts_reject_a_bad_write_after_the_first_64_addresses():
    goal, _ = _many_writes(wrong_last=True)
    parts = _effect_parts(goal)
    assert len(parts) == 9
    assert all(_check(Not(simplify(forward_selects(part)))) == unsat for part in parts[:-1])
    assert _check(Not(simplify(forward_selects(parts[-1])))) != unsat
    answer, records = refute_signed_effect(BoolVal(True), goal, 1000)
    assert answer != "unsat" and not records


def test_same_root_written_address_union_is_exhaustive_with_aliasing():
    root = _array("alias_root")
    x, y = BitVec("alias_x", 64), BitVec("alias_y", 64)
    a, b = BitVec("alias_a", 8), BitVec("alias_b", 8)
    goal = Store(root, x, a) == Store(root, y, b)
    parts = _effect_parts(goal)
    assert _check(Not(goal == And(*parts))) == unsat
    answer, records = refute_signed_effect(And(x == y, a == b), goal, 1000)
    assert answer == "unsat" and records and all(r.proved for r in records)


def test_effect_parts_preserve_bv64_wraparound_without_a_no_wrap_assumption():
    root = _array("wrap_root")
    base = BitVec("wrap_base", 64)
    top = base + BitVecVal((1 << 64)-1, 64)
    wrapped = base - BitVecVal(1, 64)
    left = Store(Store(root, top, BitVecVal(3, 8)), base, BitVecVal(5, 8))
    right = Store(Store(root, base, BitVecVal(5, 8)), wrapped, BitVecVal(3, 8))
    goal = left == right
    assert _check(Not(goal == And(*_effect_parts(goal)))) == unsat
    answer, records = refute_signed_effect(BoolVal(True), goal, 1000)
    assert answer == "unsat" and all(r.proved for r in records)


def test_different_array_roots_keep_the_original_full_equality():
    a, b = _array("different_a"), _array("different_b")
    at = BitVec("different_at", 64)
    goal = Store(a, at, BitVecVal(1, 8)) == Store(b, at, BitVecVal(1, 8))
    [part] = _effect_parts(goal)
    assert part.eq(goal)
    answer, records = refute_signed_effect(BoolVal(True), goal, 1000)
    assert answer != "unsat" and not records
    assert _effect_parts(a == a) == []


def test_free_byte_abstraction_has_an_exact_reverse_instance():
    root, at = _array("byte_instance_root"), BitVec("byte_instance_at", 64)
    first, second = Select(root, at), Select(root, at + 1)
    original = And(first != second, first + second == BitVecVal(9, 8))
    abstract = _abstract_input_bytes(original)
    assert not abstract.eq(original)
    inverse, work = {}, [(original, abstract)]
    while work:
        old, new = work.pop()
        if old.eq(new):
            continue
        if is_select(old) and is_const(old.arg(0)) and old.size() == 8:
            assert is_const(new) and new.size() == 8
            inverse[new.get_id()] = (new, old)
        else:
            assert old.decl().eq(new.decl()) and old.num_args() == new.num_args()
            work.extend(zip(old.children(), new.children()))
    assert len(inverse) == 2
    assert substitute(abstract, *inverse.values()).eq(original)
    assert not any(is_select(node) for node in _walk(abstract))


def test_fresh_byte_names_do_not_capture_an_occupied_name_in_another_sort():
    probe = FreshConst(BitVecSort(8), "signed_byte")
    next_serial = int(str(probe.decl().name()).rsplit("!", 1)[1]) + 1
    occupied_name = f"signed_byte!{next_serial}"
    occupied = BitVec(occupied_name, 64)
    root, at = _array("byte_collision_root"), BitVec("byte_collision_at", 64)
    original = And(Select(root, at) == 0, occupied == 7)
    abstract = _abstract_input_bytes(original)
    byte_vars = [node for node in _walk(abstract) if is_const(node)
                 and node.decl().kind() == Z3_OP_UNINTERPRETED
                 and node.sort() == BitVecSort(8)]
    assert len(byte_vars) == 1 and str(byte_vars[0].decl().name()) != occupied_name
    assert any(node.eq(occupied) for node in _walk(abstract))


@pytest.mark.parametrize("binder", ["forall", "lambda"])
def test_byte_abstraction_keeps_a_query_with_any_binder_unchanged(binder):
    root = _array("binder_root")
    free, bound = BitVec("binder_free", 64), BitVec("binder_bound", 64)
    inside = (ForAll(bound, Select(root, bound) == 0) if binder == "forall"
              else Select(Lambda(bound, Select(root, bound)), free) == 0)
    original = And(Select(root, free) == 0, inside)
    assert any(is_quantifier(node) for node in _walk(original))
    assert _abstract_input_bytes(original).eq(original)


def test_derived_effect_manifest_rejects_missing_or_unproved_parts():
    a, b = _array("manifest_a"), _array("manifest_b")
    at = BitVec("manifest_at", 64)
    p, q, r, s = (BitVec(f"manifest_{name}", 8) for name in ("p", "q", "r", "s"))
    goal = And(Store(a, at, p) == Store(a, at, q), Store(b, at, r) == Store(b, at, s))
    answer, records = refute_signed_effect(And(p == q, r == s), goal, 1000)
    assert answer == "unsat" and len(records) == len(_effect_parts(goal)) == 2
    assert all(r.required_lemmas == tuple(c.name for c in r.lemmas) for r in records)
    effect = Obligation("effect_0", goal.sexpr(), answer, lemmas=records,
        required_lemmas=tuple(r.name for r in records), provenance="signed_full_state")
    assert effect.proved
    assert not replace(effect, lemmas=records[:-1]).proved
    assert not replace(effect, required_lemmas=effect.required_lemmas[:-1]).proved
    assert not replace(effect, lemmas=records + (records[-1],)).proved
    assert not replace(effect, lemmas=(records[0], replace(records[1], answer="unknown"))).proved
    bad_dependency = Obligation("bad_normalization", "true", "sat")
    corrupted = replace(records[1], lemmas=(bad_dependency,), required_lemmas=(bad_dependency.name,))
    assert not replace(effect, lemmas=(records[0], corrupted)).proved


def test_a_wrong_scalar_state_and_a_wrong_array_state_are_never_proved():
    value = BitVec("wrong_scalar", 64)
    answer, records = refute_signed_effect(BoolVal(True), value == value + 1, 1000)
    assert answer != "unsat" and not records
    root, at = _array("wrong_array"), BitVec("wrong_array_at", 64)
    goal = Store(root, at, BitVecVal(1, 8)) == Store(root, at, BitVecVal(2, 8))
    answer, records = refute_signed_effect(BoolVal(True), goal, 1000)
    assert answer != "unsat" and not records
