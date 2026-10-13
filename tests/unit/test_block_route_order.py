"""Winner-first route order in _check (_winners_first): only the order and the
time shares of the routes change, never which formula a route refutes."""
from time import monotonic

import pytest
from z3 import And, BitVec, Not, simplify

import verification.block_equivalence as be
from verification.block_equivalence import BlockEquivalenceProver, _route_class, _winners_first

c = BitVec("route_order_c", 64)


def test_route_class_drops_path_indices_and_keeps_goal_parts():
    assert _route_class("pair_67_9_goal_2_of_7") == "pair_goal_2_of_7"
    assert _route_class("pair_3_4_goal_2_of_7") == _route_class("pair_67_9_goal_2_of_7")
    assert _route_class("pair_3_4_goal_6_of_7") != _route_class("pair_3_4_goal_2_of_7")
    assert _route_class("x86_maps_3_5") == "x86_maps"
    assert _route_class("x86_maps_group_12") == "x86_maps_group"
    assert _route_class("x86_empty_4") == "x86_empty"
    assert _route_class("pair_12_3") == "pair"
    assert _route_class("entry_nonempty") == "entry_nonempty"


def test_winners_first_keeps_the_table_without_wins():
    routes = [("lia", False), ("quick", True), ("blast", True), ("unify", True), ("unify", False)]
    assert _winners_first(routes, {}) == routes
    # Misses alone never reorder.
    assert _winners_first(routes, {("blast", True): (0, 90.0), ("lia", False): (0, 30.0)}) == routes


def test_winners_first_orders_by_refutations_per_second():
    routes = [("lia", False), ("quick", True), ("blast", True), ("unify", True), ("unify", False)]
    stats = {("unify", True): (2, 400.0), ("quick", True): (1, 3.0), ("blast", True): (0, 200.0)}
    out = _winners_first(routes, stats)
    assert out[:2] == [("quick", True), ("unify", True)]          # 1/3s before 2/400s
    assert out[2:] == [("lia", False), ("blast", True), ("unify", False)]  # rest in table order
    assert sorted(out) == sorted(routes)                          # every route still there


class _Routes:
    """Stub every route of _check; `wins` names the routes that refute F."""

    def __init__(self, monkeypatch, prover, wins):
        self.calls, self.wins, self.deadlines = [], set(wins), {}
        self.prover = prover
        monkeypatch.setattr(be, "solve_query", lambda q, t: "unknown")
        monkeypatch.setattr(be, "pin_split", lambda f, t, d=None: None)
        monkeypatch.setattr(be, "_alias_split", lambda *a, **k: self.log("alias", a[0]) and None)
        monkeypatch.setattr(be, "refute_over_bv_abstraction",
                            lambda f, t: (f, self.answer("bvabs", f)))
        # Normalising "rewrites" F (marked by the double negation) so the norm routes run.
        monkeypatch.setattr(be, "normalize_word_arith", lambda f, deadline=None: (Not(Not(f)), ()))
        monkeypatch.setattr(prover, "_retry_over_lia", lambda f: (f, self.answer("lia", f), ()))
        monkeypatch.setattr(prover, "_retry_over_potential", lambda f: (f, self.answer("potential", f), ()))
        monkeypatch.setattr(prover, "_retry_over_nonlinear_mul",
                            lambda f, a, split=False: (f, self.answer("mul", f), ()))
        monkeypatch.setattr(prover, "_retry_with_uf_unification", lambda f, a: (f, self.answer("unify", f), ()))

    def log(self, route, f):
        name = route + ("*" if f.decl().name() == "not" and f.arg(0).decl().name() == "not" else "")
        self.calls.append(name)
        self.deadlines[name] = self.prover.deadline
        return name

    def answer(self, route, f):
        return "unsat" if self.log(route, f) in self.wins else "unknown"


def _check(prover, name):
    records = []
    ok = prover._check(name, And(c != 0, c != 1), records)
    return ok, records[-1]


def test_route_that_refuted_a_class_goes_first_for_its_siblings(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    routes = _Routes(monkeypatch, prover, {"mul*"})
    ok, record = _check(prover, "pair_1_2_goal_2_of_7")
    assert ok and record.proved
    first = list(routes.calls)
    assert first[0] == "lia" and first[-1] == "mul*"               # the table order, no history
    routes.calls.clear()
    ok, _ = _check(prover, "pair_3_4_goal_2_of_7")                # same class: winner first
    assert ok and routes.calls == ["mul*"]
    routes.calls.clear()
    ok, _ = _check(prover, "pair_3_4_goal_6_of_7")                # another class: table order
    assert ok and routes.calls == first


def test_static_switch_keeps_the_table(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    routes = _Routes(monkeypatch, prover, {"mul*"})
    _check(prover, "pair_1_2_goal_2_of_7")
    first = list(routes.calls)
    routes.calls.clear()
    monkeypatch.setattr(be, "_ROUTE_ORDER_STATIC", True)
    _check(prover, "pair_3_4_goal_2_of_7")
    assert routes.calls == first


def test_promoted_route_failing_falls_back_to_every_other_route(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    routes = _Routes(monkeypatch, prover, {"mul*"})
    _check(prover, "pair_1_2_goal_2_of_7")
    table = list(routes.calls)
    routes.calls.clear()
    routes.wins = {"unify"}                                       # this sibling needs plain unify
    ok, record = _check(prover, "pair_3_4_goal_2_of_7")
    assert ok and record.proved
    # The promoted route, then every other route in table order until one refutes F.
    assert routes.calls == ["mul*"] + [r for r in table if r != "mul*"] + ["unify*", "unify"]
    stats = prover._route_stats["pair_goal_2_of_7"]
    assert stats[("mul", True)][0] == 1 and stats[("unify", False)][0] == 1


def test_nothing_refutes_nothing_is_proved(monkeypatch):
    # Reordering cannot turn unknown into a proof: with no refuting route the
    # record stays unknown, before and after a class has a winner.
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    routes = _Routes(monkeypatch, prover, {"mul*"})
    assert _check(prover, "pair_1_2_goal_2_of_7")[0]
    routes.wins = set()
    ok, record = _check(prover, "pair_3_4_goal_2_of_7")
    assert not ok and record.answer == "unknown"


def test_promoted_route_gets_half_of_what_is_left(monkeypatch):
    prover = BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    routes = _Routes(monkeypatch, prover, {"mul*"})
    _check(prover, "pair_1_2_goal_2_of_7")
    end = monotonic() + 1000
    prover.deadline = end
    _check(prover, "pair_3_4_goal_2_of_7")
    assert routes.deadlines["mul*"] - monotonic() == pytest.approx(500, abs=5)
