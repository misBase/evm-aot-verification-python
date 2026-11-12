import pytest
"""block_parallel.close_edge, batch 2: F forward/join path, G1 per-conjunct screen,
G2 parts through _check_all, H2 independence screen, per-edge outcome cache,
UF congruence split. Every group has a FALSE claim that must not be proved."""
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, Concat, Extract, Function, If, Lambda, Not, Select,
                Store, ULT, ZeroExt)

import verification.block_equivalence as be
from verification.block_equivalence import Obligation
from verification.block_parallel import close_edge
from verification.cutpoint_relation import RelationGoal as G

REAL_SOLVE = be.solve_query
x, y, z = BitVec("ce_x", 64), BitVec("ce_y", 64), BitVec("ce_z", 64)
h = BitVec("ce_hard", 64)  # queries mentioning it are made "unknown" where a test says so


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    # Answers must come from the solver, not a proof cache from earlier runs; serial _check_all
    # (with a pair pool, _check runs in worker processes where test patches do not apply).
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


class Stub:
    """Prover double: every part is one real solver call; names of checked parts are kept."""
    timeout_ms = 3000

    def __init__(self):
        self.checked, self.check_all_calls = [], 0

    def _check(self, name, formula, records, *, expected="unsat", split=True):
        self.checked.append(name)
        records.append(Obligation(name, formula.sexpr(), REAL_SOLVE(formula, 3000)))
        return records[-1].proved

    def _check_all(self, obligations, records):
        self.check_all_calls += 1
        for name, formula, _ in obligations:
            yield self._check(name, formula, records)


def real_prover(monkeypatch=None):
    p = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    p.checked = []
    check = p._check

    def recording(name, *a, **k):
        p.checked.append(name)
        return check(name, *a, **k)
    p._check = recording
    return p


def unknown_when(monkeypatch, predicate):
    monkeypatch.setattr(be, "solve_query", lambda q, ms: "unknown" if predicate(q.sexpr()) else REAL_SOLVE(q, ms))


def lemma_names(record):
    return [l.name for l in record.lemmas]


# ---- F: callEngine mirror read back through byte stores --------------------------------

def _mirror_limb(overwrite):
    v, w, r13 = BitVec("ce_v", 64), BitVec("ce_w", 64), BitVec("ce_r13", 64)
    V = ZeroExt(0, (v >> 5) * (v >> 5)) + w
    m = Array("ce_m", BitVecSort(64), BitVecSort(8))
    for i in range(8):
        m = Store(m, r13 + 0x70 + i, Extract(8 * i + 7, 8 * i, V))
    for i in range(8):
        m = Store(m, r13 + 0x30 + i, Extract(8 * i + 7, 8 * i, w))
    if overwrite:
        m = Store(m, r13 + 0x73, BitVecVal(0xAB, 8))
    return Concat(*[Select(m, r13 + 0x70 + i) for i in reversed(range(8))]) == V


def test_f_mirror_goal_closes_by_forward_and_join_without_a_solver_part(monkeypatch):
    # On CErc20 10233 the abstraction and every route stayed unknown; here the shape is small
    # enough for bvabs, so take it out to see the forward/join step alone.
    monkeypatch.setattr(be, "refute_over_bv_abstraction", lambda f, ms: (f, "unknown"))
    p = Stub()
    record = close_edge(p, "H2_f", x == 5, [("t0", [G("callengine_mirror", _mirror_limb(False))])])
    assert record.proved and "t0" in record.formula
    assert p.checked == []  # no part needed the premise or a solver route
    assert lemma_names(record) == ["H2_f_t0_callengine_mirror_0"]


def test_f_soundness_overwritten_mirror_byte_is_not_proved():
    p = Stub()
    record = close_edge(p, "H2_f", x == 5, [("t0", [G("callengine_mirror", _mirror_limb(True))])])
    assert not record.proved


# ---- G1: screen per conjunct ------------------------------------------------------------

def test_g1_wrong_target_refuted_by_one_conjunct_when_the_conjunction_is_hard(monkeypatch):
    # base's conjuncts all share x: the independence screen has nothing to drop.
    base = And(x == 5, ULT(x, 10))
    unknown_when(monkeypatch, lambda s: "ce_hard" in s)
    goals = [("t0", [G("stack_geometry", And(x == 6, h == 0))]), ("t1", [G("stack_geometry", x == 5)])]
    p = Stub()
    record = close_edge(p, "H2_g1", base, goals)
    assert record.proved and "t1" in record.formula
    assert not any("_t0_" in n for n in p.checked), p.checked


def test_g1_soundness_screen_never_proves_a_false_target():
    base = And(x == 5, ULT(x, 10))
    goals = [("t0", [G("stack_geometry", And(x == 5, h == 0))]), ("t1", [G("stack_geometry", x == 7)])]
    assert not close_edge(Stub(), "H2_g1", base, goals).proved
    assert not close_edge(real_prover(), "H2_g1", base, goals).proved


# ---- G2: the hard parts go through _check_all -------------------------------------------

def test_g2_parts_checked_through_check_all_and_recorded():
    base = And(x == 5, ULT(y, 10))
    p = Stub()
    record = close_edge(p, "H2_g2", base, [("t0", [G("memory", And(ULT(y, 11), ULT(x, 6)))])])
    assert record.proved and p.check_all_calls == 1
    assert lemma_names(record) == ["H2_g2_t0_memory_0", "H2_g2_t0_memory_1"]
    assert all(l.proved for l in record.lemmas)


def test_g2_stops_at_the_first_failed_part_and_tries_the_next_target():
    base = And(x == 5, ULT(y, 10))
    goals = [("t0", [G("memory", ULT(y, 9)), G("gas", ULT(y, 11)), G("status", ULT(y, 12))]),
             ("t1", [G("memory", ULT(y, 12))])]
    p = real_prover()
    record = close_edge(p, "H2_g2", base, goals)
    assert record.proved and "t1" in record.formula
    assert [n for n in p.checked if "_t0_" in n] == ["H2_g2_t0_memory_0"]  # gas / status never ran


def test_g2_soundness_one_false_part_fails_the_edge():
    base = And(x == 5, ULT(y, 10))
    goals = [("t0", [G("memory", ULT(y, 11)), G("gas", ULT(y, 9))])]
    assert not close_edge(real_prover(), "H2_g2", base, goals).proved
    assert not close_edge(Stub(), "H2_g2", base, goals).proved


# ---- H2 independence screen ---------------------------------------------------------------

def test_independence_screen_skips_a_target_whose_conjunct_no_base_conjunct_mentions(monkeypatch):
    base = And(x == 5, ULT(y, 10))
    # Any query over the whole premise and z is "unknown" (Safe 8915 t0: 3635s).
    unknown_when(monkeypatch, lambda s: "ce_z" in s and "ce_x" in s)
    goals = [("t0", [G("stack_constant_predicate", z == 0), G("memory", ULT(y, 11))]),
             ("t1", [G("stack_constant_predicate", x == 5), G("memory", ULT(y, 11))])]
    p = Stub()
    record = close_edge(p, "H2_ind", base, goals)
    assert record.proved and "t1" in record.formula
    assert not any("_t0_" in n for n in p.checked + lemma_names(record))


def test_independence_screen_needs_a_model_unknown_does_not_skip(monkeypatch):
    base = And(x == 5, ULT(y, 10))
    unknown_when(monkeypatch, lambda s: "ce_z" in s)  # cone ∧ ¬c unknown too
    goals = [("t0", [G("stack_constant_predicate", z == 0)]), ("t1", [G("stack_constant_predicate", x == 5)])]
    p = Stub()
    record = close_edge(p, "H2_ind", base, goals)
    assert record.proved and "t1" in record.formula
    assert any("_t0_" in n for n in p.checked)  # t0 was not screened out, its part ran (and failed)


def test_independence_screen_keeps_a_target_its_cone_implies():
    # cone of x != 6 is {x == 5}; x == 5 ∧ ¬(x != 6) is UNSAT, so t0 must not be skipped.
    base = And(x == 5, ULT(y, 10))
    record = close_edge(Stub(), "H2_ind", base, [("t0", [G("stack_constant_predicate", x != 6)])])
    assert record.proved and "t0" in record.formula


def test_independence_screen_soundness_false_independent_target_is_not_proved():
    base = And(x == 5, ULT(y, 10))
    goals = [("t0", [G("stack_constant_predicate", z == 0), G("memory", ULT(y, 11))])]
    record = close_edge(Stub(), "H2_ind", base, goals)
    assert not record.proved and record.name == "H2_ind"  # the whole-disjunction fallback, SAT


# ---- per-edge outcome cache ---------------------------------------------------------------

def test_outcome_cache_reuses_a_proved_conjunct_for_the_next_target():
    base = And(x == 5, ULT(y, 10))
    shared = G("memory", ULT(y, 11))
    goals = [("t0", [shared, G("gas", ULT(y, 9))]), ("t1", [shared, G("gas", ULT(y, 12))])]
    p = Stub()
    record = close_edge(p, "H2_oc", base, goals)
    assert record.proved and "t1" in record.formula
    assert [n for n in p.checked if "_memory_" in n] == ["H2_oc_t0_memory_0"]  # checked once
    assert "H2_oc_t0_memory_0" in lemma_names(record)  # t1's record carries the reused proof


def test_outcome_cache_failure_skips_later_targets_with_that_conjunct():
    base = And(x == 5, ULT(y, 10))
    bad = G("memory", ULT(y, 9))
    goals = [("t0", [bad]), ("t1", [G("gas", ULT(y, 11)), bad]), ("t2", [G("memory", ULT(y, 11))])]
    p = Stub()
    record = close_edge(p, "H2_oc", base, goals)
    assert record.proved and "t2" in record.formula
    assert not any("_t1_" in n for n in p.checked), p.checked


def test_outcome_cache_soundness_shared_proof_does_not_cover_a_false_conjunct():
    base = And(x == 5, ULT(y, 10))
    shared = G("memory", ULT(y, 11))
    goals = [("t0", [shared, G("gas", ULT(y, 9))]), ("t1", [shared, G("gas", ULT(y, 8))])]
    assert not close_edge(Stub(), "H2_oc", base, goals).proved


# ---- UF congruence split ------------------------------------------------------------------

BV8 = BitVecSort(8)
M = Array("ce_M", BitVecSort(64), BV8)
i, k, n, n2 = BitVec("ce_i", 64), BitVec("ce_k", 64), BitVec("ce_n", 64), BitVec("ce_n2", 64)
v8 = BitVec("ce_v8", 8)  # stored at k; the base says v8 == M[k], so both slices read the same bytes
sha3 = Function("ce_sha3_slice", ArraySort(BitVecSort(64), BV8), BitVecSort(64), BitVecSort(64))
sha3b = Function("ce_sha3_bytes", BitVecSort(16 + 64 + 64), BitVecSort(64))


def _slice(length, stored, shift=0):
    mem = Store(M, k, v8) if stored else M
    return Lambda([i], If(ULT(i, length), Select(mem, i + shift), BitVecVal(0, 8)))


def test_congruent_arguments_leaves():
    from verification.block_parallel import _congruent_arguments
    s1, s2 = BitVec("ce_s1", 64), BitVec("ce_s2", 64)
    a, b = sha3(_slice(n, True), n), sha3(_slice(n, False), n + x - 1)
    nested = sha3b(Concat(BitVecVal(0x1901, 16), y, a)) == sha3b(Concat(BitVecVal(0x1901, 16), y, b))
    for conjunct in (a == b, nested):
        leaves = _congruent_arguments(conjunct)
        assert leaves is not None and len(leaves) == 2
        assert REAL_SOLVE(And(*(l == r for l, r in leaves), Not(conjunct)), 3000) == "unsat"  # leaves imply it
    two = sha3b(Concat(BitVecVal(1, 16), s1, y)) == sha3b(Concat(BitVecVal(1, 16), s2, x))
    assert len(_congruent_arguments(two)) == 1  # two Concat parts differ: the Concat pair is one leaf
    assert _congruent_arguments(s1 + 1 == 1 + s1) is None  # interpreted root
    assert _congruent_arguments(a == a) is None


def test_congruence_split_proves_through_argument_leaves_with_a_lemma():
    base = And(x == 1, ULT(n, 100), v8 == Select(M, k))
    goal = sha3(_slice(n, True), n) == sha3(_slice(n, False), n + x - 1)
    record = close_edge(real_prover(), "H2_cg", base, [("t0", [G("live_stack_prefix", goal)])])
    assert record.proved and "t0" in record.formula
    names = lemma_names(record)
    assert "H2_cg_t0_live_stack_prefix_0_congruence" in names
    assert sum("_arg" in nm for nm in names) == 2, names


def test_congruence_split_soundness_differing_leaves_are_not_proved():
    base = ULT(n, 100)
    wrong_len = sha3(_slice(n, False), n) == sha3(_slice(n, False), n2)  # n2 unconstrained
    wrong_mem = sha3(_slice(n, False), n) == sha3(_slice(n, False, shift=1), n)  # different bytes
    for goal in (wrong_len, wrong_mem):
        record = close_edge(real_prover(), "H2_cg", base, [("t0", [G("live_stack_prefix", goal)])])
        assert not record.proved, goal
        assert "congruence" not in " ".join(lemma_names(record))


def test_congruence_split_failing_leaves_fall_back_to_the_whole_check():
    # base constrains sha3 itself: the leaves differ, yet the goal holds (the split is a
    # strengthening only; the fallback proves it).
    a, b = sha3(_slice(n, False), n), sha3(_slice(n, False), n2)
    record = close_edge(real_prover(), "H2_cg", And(a == 7, b == 7), [("t0", [G("live_stack_prefix", a == b)])])
    assert record.proved
