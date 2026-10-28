"""Task N (remaining blocks): generic fixes.

- Product-word generalisation (_generalize_product_words): an execution
  assumption that bridges a 256-bit compare of a limb-wise product (EQ / LT
  borrow chains) is a tautology about the whole word; generalising each bvmul
  alone leaves the limbs as carry sums and stays unknown (Aave 11831
  evm_assumption_7).
- Potential range axioms (potential_range_axioms / refute_over_bounded_potential):
  the memory-cost potential P read as C is bounded and non-decreasing on
  w <= 2^32 - 1; an x86 path that fails a 64-bit overflow check on a memory
  charge is empty only with these (Permit2 1327 x86 paths 6/7).
"""
from dataclasses import replace
from pathlib import Path
from random import Random

import pytest
from z3 import (And, BitVec, BitVecVal, BoolVal, Concat, Extract, If, Implies, Not, ULE, ULT, ZeroExt, is_app,
                is_true, parse_smt2_file, simplify, substitute, substitute_funs, Var, Z3_OP_BMUL)

import verification.block_equivalence as be
from state.smt_state import SMTState
from verification.loop_induction import SegmentPath

SMT2 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "n" / "smt2"


@pytest.fixture(autouse=True)
def _no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _has_mul(t):
    seen, work = set(), [t]
    while work:
        u = work.pop()
        if u.get_id() in seen or not is_app(u):
            continue
        seen.add(u.get_id())
        if u.decl().kind() == Z3_OP_BMUL:
            return True
        work.extend(u.children())
    return False


def _limb_product(prefix):
    """A 128-bit product of two 64-bit limbs pairs, assembled limb-wise (low, high with carry)."""
    a0, a1, b0, b1 = (BitVec(f"{prefix}_{s}", 64) for s in ("a0", "a1", "b0", "b1"))
    full = ZeroExt(64, a0) * ZeroExt(64, b0)
    low = Extract(63, 0, full)
    high = Extract(127, 64, full) + a1 * b0 + a0 * b1
    return Concat(high, low)


def _borrow_free(x, y):
    """No borrow out of x - y, in 129-bit arithmetic (the bridge's spelling)."""
    return Extract(128, 128, ZeroExt(1, x) - ZeroExt(1, y)) == 0


def test_product_words_are_generalised():
    word = _limb_product("gw")
    c = BitVecVal(10**27, 128)
    hint = (word == c) == And(_borrow_free(word, c), _borrow_free(c, word))
    generalised = be._generalize_product_words(hint)
    assert generalised is not None and not _has_mul(generalised)
    assert be.solve_query(Not(generalised), 5000) == "unsat"   # valid for every word, hence for the product


def test_no_word_without_a_product():
    a, b = BitVec("nw_a", 64), BitVec("nw_b", 64)
    assert be._generalize_product_words(Concat(a, b) == Concat(b, a)) is None
    assert be._generalize_product_words(Extract(7, 0, a * b) == 0) is None  # a product, but no wide word


def test_generalised_words_do_not_prove_a_non_tautology():
    word = _limb_product("nt")
    hint = ULT(word, BitVecVal(5, 128))   # holds for some products only
    generalised = be._generalize_product_words(hint)
    assert be.solve_query(Not(generalised), 5000) == "sat"


def test_aave_11831_evm_assumption_7_is_proved_by_word_generalisation(monkeypatch):
    query = And(*parse_smt2_file(str(SMT2 / "aave_11831_evm_assumption_7.smt2")))
    goal = [c for c in be._conjuncts(query) if c.decl().name() == "not"][-1]
    assumption = goal.arg(0)
    premise = And(*[c for c in be._conjuncts(query) if not c.eq(goal)])
    path = SegmentPath("terminal", None, BoolVal(True), SMTState.create_initial_state(num_inputs=0))
    path.state.assumptions = [assumption]
    initial = SMTState.create_initial_state(num_inputs=0)
    initial.assumptions = []
    other = SegmentPath("terminal", None, BoolVal(True), SMTState.create_initial_state(num_inputs=0))
    other.state.assumptions = []
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    goals, real_check = [], prover._check

    def check(name, formula, records, **kw):
        if name.startswith("evm_assumption"):
            goals.append(formula)
        return real_check(name, formula, records, **kw)
    monkeypatch.setattr(prover, "_check", check)
    records = []
    prover.check_paths([path], [other], premise, initial, records)
    assert len(goals) == 1 and not _has_mul(goals[0])       # the generalised word query, not the premise one
    assumption_record = [r for r in records if r.name.startswith("evm_assumption")]
    assert len(assumption_record) == 1 and assumption_record[0].proved
    assert assumption_record[0].elapsed_seconds < 5


# --- memory potential range ----------------------------------------------------


def _words(prefix):
    """Word count of a 32-byte-rounded end offset fmp + len (x86: (31 + end) >> 5)."""
    fmp, n = BitVec(f"{prefix}_fmp", 64), BitVec(f"{prefix}_len", 64)
    end = fmp + n
    return fmp, n, Concat(BitVecVal(0, 5), Extract(63, 5, 31 + end))


def _overflowing_log_charge(prefix):
    """premise ∧ path of an x86 LOG whose cost 8*len + 1125 + expansion overflows 64 bits, after the
    path bounded fmp and len below 2^35, so w < 2^32 (Permit2 1327 x86 path 6 checks 32w < 2^37)."""
    fmp, n, w = _words(prefix)
    old = BitVec(f"{prefix}_old_words", 64)
    charge = If(ULE(w, old), BitVecVal(0, 64), be._memory_cost(w) - be._memory_cost(old))
    return And(ULE(old, 1 << 32), ULT(fmp, 1 << 35), ULT(n, 1 << 35),
               Extract(127, 64, 8 * ZeroExt(64, n)) == 0,
               Extract(64, 64, ZeroExt(1, 8 * n) + ZeroExt(1, 1125 + charge)) == 1)


def test_overflowing_charge_is_refuted_only_with_the_range_axioms(monkeypatch):
    formula = _overflowing_log_charge("ov")
    query, answer, _ = be.refute_over_bounded_potential(formula, 10000)
    assert answer == "unsat"
    monkeypatch.setattr(be, "potential_range_axioms", lambda f: [])
    assert be.refute_over_bounded_potential(formula, 10000)[1] == "unknown"   # nothing to bound: not applicable
    abstract, _ = be.abstract_memory_potential(formula)
    target, _, axioms, _ = be.telescope_potential(abstract)
    assert be.refute_over_bv_abstraction(And(target, *axioms), 10000)[1] == "sat"  # P alone: any function


def test_range_axioms_hold_for_the_memory_cost():
    formula = _overflowing_log_charge("va")
    abstract, _ = be.abstract_memory_potential(formula)
    target, _, _, _ = be.telescope_potential(abstract)
    axioms = be.potential_range_axioms(target)
    assert axioms
    p = be._potential(64)
    cost = And(*axioms)
    read = substitute_funs(cost, (p, be._memory_cost(Var(0, p.domain(0)))))  # P read as C
    leaves = sorted({str(c) for c in _leaves(read)})
    rng = Random(7)
    for _ in range(200):
        values = [(BitVec(name, 64), BitVecVal(rng.choice((rng.getrandbits(64), rng.getrandbits(33), rng.getrandbits(20))), 64))
                  for name in leaves]
        assert is_true(simplify(substitute(read, *values)))


def _leaves(t):
    seen, work, out = set(), [t], []
    while work:
        u = work.pop()
        if u.get_id() in seen or not is_app(u):
            continue
        seen.add(u.get_id())
        if u.num_args() == 0 and u.decl().kind() == be.Z3_OP_UNINTERPRETED:
            out.append(u)
        work.extend(u.children())
    return out


def test_no_range_axioms_below_64_bits():
    w = BitVec("nb_w", 32)
    abstract, changed = be.abstract_memory_potential(ULT(be._memory_cost(w), 100))
    assert changed and be.potential_range_axioms(abstract) == []


def test_monotonicity_is_capped(monkeypatch):
    ws = [BitVec(f"mc_w{k}", 64) for k in range(4)]
    abstract, _ = be.abstract_memory_potential(And(*(ULT(be._memory_cost(w), 100) for w in ws)))
    assert len(be.potential_range_axioms(abstract)) == 4 + 4 * 3
    monkeypatch.setattr(be, "_POTENTIAL_MONOTONE_APPS", 3)
    assert len(be.potential_range_axioms(abstract)) == 4


# --- blasted witness -----------------------------------------------------------


def _store_chain_path(prefix, feasible=True):
    """A path condition reading through a store chain over a lambda array (as copy results are)."""
    from z3 import Array, BitVecSort, Lambda, Select, Store
    m = Array(f"{prefix}_m", BitVecSort(64), BitVecSort(8))
    i, a, b, n = (BitVec(f"{prefix}_{s}", 64) for s in ("i", "a", "b", "n"))
    copied = Lambda([i], If(ULT(i - a, n), Select(m, i + 1), Select(m, i)))
    mem = Store(Store(copied, b, BitVecVal(7, 8)), b + 1, BitVecVal(9, 8))
    constraints = [ULT(n, 64), ULT(a, 1 << 20), Select(mem, b) == 7, Select(mem, a) == 3]
    if not feasible:
        constraints.append(Select(mem, b + 1) == 8)
    return constraints


def _reachability(monkeypatch, constraints, answers):
    """is_possible on `constraints` with the incremental check (and, if given, the blasted one) forced."""
    import x86_64.cfg_state as cfg_state
    from x86_64.cfg_state import PrefixSolver, X86Constraints
    real = cfg_state._bounded_check
    tags = []

    def bounded(solver, timeout_ms, tag, wall_ms=None):
        tags.append(tag)
        return answers[tag] if tag in answers else real(solver, timeout_ms, tag, wall_ms)
    monkeypatch.setattr(cfg_state, "_bounded_check", bounded)
    path = X86Constraints()
    for c in constraints:
        path.add(c)
    return path, path.is_possible(prefix_solver=PrefixSolver()), tags


def test_blasted_query_restores_the_witness(monkeypatch):
    from z3 import unknown
    path, kept, tags = _reachability(monkeypatch, _store_chain_path("bw"), {"incremental": unknown})
    assert kept and tags[:2] == ["incremental", "blast"]
    assert path._witness is not None and is_true(path._witness.eval(path.as_bool(), model_completion=True))


def test_blasted_unsat_prunes(monkeypatch):
    from z3 import unknown
    path, kept, tags = _reachability(monkeypatch, _store_chain_path("bu", feasible=False), {"incremental": unknown})
    assert not kept and tags == ["incremental", "blast"]


def test_blasted_unknown_falls_through_and_keeps_the_path(monkeypatch):
    from z3 import unknown
    path, kept, tags = _reachability(monkeypatch, _store_chain_path("bk"), {"incremental": unknown, "blast": unknown})
    assert kept and path._witness is None                    # unknown never prunes, never invents a witness


def test_summary_entry_falls_back_to_the_blasted_query(monkeypatch):
    import verification.block_summaries as bs
    from tests.unit.test_memgas_summary import RENAMED_HEX, _blocks
    from x86_64.summaries import X86SummaryConfig
    runtime = bs.VerifiedSummaryRuntime(_blocks(RENAMED_HEX), X86SummaryConfig.enabled(memgas="strict"), timeout_ms=30000)
    # Expected-SAT queries go through _sat_model (N3: it keeps the model for the next entry).
    real, queries = bs._sat_model, []

    def solve(query, timeout_ms, *a, **k):
        queries.append(query)
        return ("unknown", None) if len(queries) == 1 else real(query, timeout_ms, *a, **k)
    monkeypatch.setattr(bs, "_sat_model", solve)
    record = runtime._solve("entry", And(*_store_chain_path("se")), "sat")
    assert record.answer == "sat" and len(queries) == 2


def test_summary_unsat_check_falls_back_to_the_blasted_query(monkeypatch):
    import verification.block_summaries as bs
    from tests.unit.test_memgas_summary import RENAMED_HEX, _blocks
    from x86_64.summaries import X86SummaryConfig
    runtime = bs.VerifiedSummaryRuntime(_blocks(RENAMED_HEX), X86SummaryConfig.enabled(memgas="strict"), timeout_ms=30000)
    real, queries = bs.solve_query, []

    def solve(query, timeout_ms, *a, **k):
        queries.append(query)
        return "unknown" if len(queries) == 1 else real(query, timeout_ms, *a, **k)
    monkeypatch.setattr(bs, "solve_query", solve)
    infeasible = _store_chain_path("su", feasible=False)
    record = runtime._solve("copy_domain", And(infeasible[-1], *infeasible[:-1]))  # not decided syntactically
    assert record.proved and len(queries) == 2


def test_aave_7200_hit_premise_is_sat_once_blasted():
    from z3 import SolverFor, sat
    premise = And(*parse_smt2_file(str(SMT2 / "aave_7200_entry_71f8d.smt2")))
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", 60000)
    solver.add(simplify(premise, blast_select_store=True))
    assert solver.check() == sat
    assert is_true(solver.model().eval(premise, model_completion=True))   # a model of the premise itself


def test_copy_precondition_falls_back_to_the_blasted_query(monkeypatch):
    import x86_64.summaries.copy_loop as copy_loop
    from z3 import unknown, unsat
    x, y = BitVec("cp_x", 64), BitVec("cp_y", 64)
    real, calls = copy_loop.SolverFor, []

    class Undecided:
        """The first (plain) full query answers unknown; later ones are real."""
        def __init__(self, logic):
            self.solver, self.n = real(logic), len(calls)
            calls.append(self)

        def __getattr__(self, name):
            return getattr(self.solver, name)

        def check(self):
            return unknown if self.n == 0 else self.solver.check()
    monkeypatch.setattr(copy_loop, "SolverFor", Undecided)
    result = copy_loop._implication_result(And(ULT(x, 10), y == x + 1), [], ULT(y, 12), timeout_ms=5000)
    assert result == unsat and len(calls) == 2


# --- undecided summary entry ---------------------------------------------------


def _memgas_runtime(monkeypatch, entry_answer):
    """The memgas summary of test_memgas_summary with the hit's entry check forced to `entry_answer`."""
    from tests.unit.test_memgas_summary import RENAMED_HEX, _blocks
    from verification.block_summaries import VerifiedSummaryRuntime
    from x86_64.summaries import X86SummaryConfig
    from x86_64.summaries.memgas import exit_guard
    from x86_64.summaries.memgas_proof import clear_proof_cache, generic_memgas_state

    clear_proof_cache()
    runtime = VerifiedSummaryRuntime(_blocks(RENAMED_HEX), X86SummaryConfig.enabled(memgas="strict"), timeout_ms=30000)
    real = runtime._solve

    def solve(name, formula, expected="unsat"):
        record = real(name, formula, expected)
        return replace(record, answer=entry_answer) if name == "entry" else record
    monkeypatch.setattr(runtime, "_solve", solve)
    [summary] = runtime.summaries
    state = generic_memgas_state()
    return runtime, summary, state, exit_guard(summary.payload, state)


def test_undecided_entry_still_applies_the_summary(monkeypatch):
    runtime, summary, state, guard = _memgas_runtime(monkeypatch, "unknown")
    runtime.apply(summary, state, path_condition=Not(guard))
    [certificate] = runtime.certificates
    entry = next(o for o in certificate.obligations if o.name == "entry")
    assert (entry.answer, entry.expected) == ("unknown", "unknown")     # recorded as undecided, not as SAT
    assert certificate.complete
    assert all(o.proved and o.answer == "unsat" for o in certificate.obligations if o.name != "entry")


def test_undecided_entry_does_not_excuse_a_failed_obligation(monkeypatch):
    from x86_64.summaries.base import SummaryPreconditionError
    runtime, summary, state, _ = _memgas_runtime(monkeypatch, "unknown")
    with pytest.raises(SummaryPreconditionError, match="memgas_exit_guard_excluded"):
        runtime.apply(summary, state)               # the exit guard is not excluded on this path
    assert not runtime.certificates


def test_refuted_entry_is_still_rejected(monkeypatch):
    from x86_64.summaries.base import SummaryPreconditionError
    runtime, summary, state, guard = _memgas_runtime(monkeypatch, "unsat")
    with pytest.raises(SummaryPreconditionError, match="entry: unsat"):
        runtime.apply(summary, state, path_condition=Not(guard))
    assert not runtime.certificates


def test_byte_copy_hit_on_infeasible_path_is_vacuous(monkeypatch):
    from tests.unit.test_block_summary_certificates import copy_case
    from verification.mcopy_induction import DeadHitCertificate
    runtime, summary, state = copy_case(7)
    assert summary.kind == "copy_loop" and not summary.payload.template.startswith("mcopy")
    monkeypatch.setattr("verification.block_summaries.run_x86_segment",
                        lambda *a, **k: pytest.fail("an infeasible hit must not be replayed"))
    assert runtime.apply(summary, state, path_condition=BoolVal(False)) is not None
    [certificate] = runtime.certificates
    assert isinstance(certificate, DeadHitCertificate) and certificate.complete


# --- node-level unification cap -------------------------------------------------


def test_node_unification_gets_a_quarter_of_what_is_left(monkeypatch):
    from time import monotonic
    from z3 import Function, BitVecSort
    f = Function("nu_host", BitVecSort(64), BitVecSort(64))
    x, y = BitVec("nu_x", 64), BitVec("nu_y", 64)
    pairs = [(f"pair_0_{k}", And(f(x + k) == 1, f(y) == 2), "") for k in range(2)]
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    prover.deadline = monotonic() + 400
    seen = []

    def unify(formulas, timeout_ms, deadline=None, cache=None, max_lemmas=64, stall_seconds=None):
        seen.append((deadline, stall_seconds))
        return formulas, ()
    monkeypatch.setattr(be, "unify_across", unify)
    prover._unify_node(pairs)
    assert len(seen) == 1 and seen[0][0] is not None and seen[0][0] <= monotonic() + 100 + 1
    assert seen[0][1] == 10.0  # N4 fix 19: also stops after 10 query timeouts without a merge


@pytest.mark.parametrize("row", [6, 7])
def test_permit2_1327_x86_row_is_empty(row):
    query = And(*parse_smt2_file(str(SMT2 / "permit2_1327" / f"x86_empty_{row}.smt2")))
    assert be.refute_over_bounded_potential(query, 30000)[1] == "unsat"
