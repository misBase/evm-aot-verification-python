"""Terminal goal splitting and extensional Skolemisation in BlockEquivalenceProver._check."""
from z3 import (And, Array, BitVec, BitVecSort, Bool, ForAll, If, Lambda, Not, Or, Select, Solver, Store, sat,
                unsat)

import verification.block_equivalence as be
from verification.block_equivalence import (BlockEquivalenceProver, Obligation, _goal_split,
                                            skolemize_array_disequalities)

MEM = BitVecSort(64), BitVecSort(8)


def answer(formula):
    solver = Solver()
    solver.set(timeout=5000)
    solver.add(formula)
    return solver.check()


def _unknown_first(monkeypatch):
    """The quick exact query on the whole pair is 'unknown', forcing the split."""
    real, calls = be.solve_query, []

    def fake(formula, timeout_ms):
        calls.append(formula)
        return "unknown" if len(calls) == 1 else real(formula, timeout_ms)
    monkeypatch.setattr(be, "solve_query", fake)


def _pair(x, goals):
    return And(And(x == 1), Not(And(*goals)))


def test_goal_split_refutes_every_goal(monkeypatch):
    x = BitVec("gs_x", 64)
    _unknown_first(monkeypatch)
    records = []
    assert BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair_0_0", _pair(x, [x + 1 == 2, x != 0]),
                                                                      records)
    assert [l.name for l in records[-1].lemmas] == ["pair_0_0_goal_0_of_2", "pair_0_0_goal_1_of_2"]


def test_goal_split_satisfiable_goal_is_a_counterexample(monkeypatch):
    x = BitVec("gs_x", 64)
    _unknown_first(monkeypatch)
    records = []
    assert not BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("pair_0_0", _pair(x, [x == 1, x == 2]),
                                                                          records)
    assert records[-1].answer == "sat" and not records[-1].proved


def test_goal_split_only_on_the_last_negated_conjunction():
    x = BitVec("gs_x", 64)
    assert _goal_split(And(x == 1, x != 2)) is None
    assert _goal_split(And(Not(And(x == 1, x == 2)), x == 1)) is None
    parts = _goal_split(And(And(x == 1, Not(And(x == 1, x != 3)))))  # unary And of the SMT2 round trip
    assert parts is not None and len(parts) == 2


def test_missing_goal_part_is_not_proved():
    part = lambda k, n: Obligation(f"pair_goal_{k}_of_{n}", "(false)", "unsat")
    assert Obligation("pair", "(x)", "unsat", lemmas=(part(0, 2), part(1, 2))).proved
    assert not Obligation("pair", "(x)", "unsat", lemmas=(part(0, 2),)).proved
    assert not Obligation("pair", "(x)", "unsat", lemmas=(part(0, 2), part(1, 3), part(2, 3))).proved


def test_unproved_nested_lemma_invalidates_the_pair():
    part = Obligation("pair_goal_0_of_1", "(false)", "unsat", lemmas=(Obligation("normalize_0", "(x)", "unknown"),))
    assert not Obligation("pair", "(x)", "unsat", lemmas=(part,)).proved


def test_skolemised_memmove_goal_is_refuted():
    m = Array("gs_m", *MEM)
    i = BitVec("gs_i", 64)
    view = Lambda([i], If(i == 0, Select(m, 1), Select(m, i)))  # EVM-style closed form
    formula = Not(view == Store(m, 0, Select(m, 1)))
    rewritten, lemmas = skolemize_array_disequalities(formula)
    assert [l.name for l in lemmas] == ["extensionality_0"] and all(l.proved for l in lemmas)
    assert answer(rewritten) == unsat
    records = []
    assert BlockEquivalenceProver([], [], {}, timeout_ms=3000)._check("goal", formula, records)
    assert records[-1].lemmas[0].name == "extensionality_0"


def test_each_disequality_gets_its_own_witness():
    # A, B differ only at 0 and C, D only at 1: SAT, but no single w witnesses both.
    a, b, c, d = (Array(n, *MEM) for n in ("gs_a", "gs_b", "gs_c", "gs_d"))
    j = BitVec("gs_j", 64)
    formula = And(a == Store(b, 0, Select(b, 0) + 1), c == Store(d, 1, Select(d, 1) + 1), a != b, c != d)
    rewritten, lemmas = skolemize_array_disequalities(formula)
    assert len(lemmas) == 2 and answer(rewritten) == sat
    w = BitVec("gs_w", 64)
    shared = And(a == Store(b, 0, Select(b, 0) + 1), c == Store(d, 1, Select(d, 1) + 1),
                 Select(a, w) != Select(b, w), Select(c, w) != Select(d, w))
    assert answer(shared) == unsat  # the wrong (shared-witness) Skolemisation would "prove" it


def test_disequality_below_top_level_is_not_skolemised():
    a, b = Array("gs_a", *MEM), Array("gs_b", *MEM)
    p, k = Bool("gs_p"), BitVec("gs_k", 64)
    for formula in (Or(a != b, p), Not(And(p, a != b)), Not(Not(a == b)),
                    ForAll([k], Not(Store(a, k, 0) == b))):
        rewritten, lemmas = skolemize_array_disequalities(formula)
        assert lemmas == () and rewritten.eq(formula)
