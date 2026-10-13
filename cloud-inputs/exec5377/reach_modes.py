"""Reachability-check variants for X86Constraints.is_possible (monkeypatched by xseg.py).

Every mode returns False only on an exact-or-relaxed UNSAT (sound pruning);
unknown/sat keep the path.
"""
from time import monotonic

from z3 import SolverFor, is_true, sat, unsat

from x86_64.cfg_state import DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS, _bounded_check


def _rlimit(solver):
    st = solver.statistics()
    return st.get_key_value("rlimit count") if "rlimit count" in st.keys() else 0


def _timed_check(solver, timeout_ms, tag, info):
    before = _rlimit(solver)
    t = monotonic()
    r = _bounded_check(solver, timeout_ms, tag)
    info[tag] = [str(r), round(monotonic() - t, 4), _rlimit(solver) - before]
    return r


def base(self, solver_timeout, info):
    """Line-for-line X86Constraints.is_possible (snap-r34h), with timers."""
    if self._witness is not None and is_true(self._witness.eval(self.as_bool(), model_completion=True)):
        info["w"] = 1
        return True
    solver = SolverFor("QF_AUFBV")
    for constraint in self._constraints:
        solver.add(constraint)
    for flag_cond in self.flag_constraints.values():
        solver.add(flag_cond)
    timeout_ms = solver_timeout if solver_timeout is not None else DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS
    from verification.block_equivalence import abstract_nonlinear_mul
    t = monotonic()
    relaxed, changed = abstract_nonlinear_mul(self.as_bool())
    info["abs"] = round(monotonic() - t, 4)
    if changed:
        probe = SolverFor("QF_AUFBV")
        probe.add(relaxed)
        if _timed_check(probe, timeout_ms, "probe", info) == unsat:
            self._witness = None
            return False
    result = _timed_check(solver, timeout_ms, "exact", info)
    self._witness = solver.model() if result == sat else None
    return result != unsat


class PrefixSolver:
    """One incremental solver per executor: a push scope per path-condition conjunct.
    A query pops back to the longest common conjunct prefix (by AST identity) with
    the previous query and pushes the rest, so sibling/descendant paths reuse the
    solver's internalized terms and learned clauses. Assertions are exactly the
    path condition: its UNSAT is the path condition's UNSAT."""

    def __init__(self):
        self.solver = SolverFor("QF_AUFBV")
        self.stack = []  # the asserted ASTs (kept alive: their ids stay unique)

    def check(self, conjuncts, timeout_ms, info):
        common, stack = 0, self.stack
        while common < min(len(stack), len(conjuncts)) and stack[common].get_id() == conjuncts[common].get_id():
            common += 1
        if len(stack) > common:
            self.solver.pop(len(stack) - common)
            del stack[common:]
        for c in conjuncts[common:]:
            self.solver.push()
            self.solver.add(c)
            stack.append(c)
        info["reuse"] = common
        return _timed_check(self.solver, timeout_ms, "inc", info)


CURRENT = [None]


def install_executor_hook():
    from x86_64.cfg_executor import X86SymbolicExecutor
    inner = X86SymbolicExecutor._is_state_reachable

    def hooked(self, state):
        CURRENT[0] = self
        return inner(self, state)
    X86SymbolicExecutor._is_state_reachable = hooked


def incprobe(self, solver_timeout, info):
    """Witness, then the executor's incremental exact query; only an unknown pays
    for the mul->UF refutation probe on a fresh solver."""
    if self._witness is not None and is_true(self._witness.eval(self.as_bool(), model_completion=True)):
        info["w"] = 1
        return True
    timeout_ms = solver_timeout if solver_timeout is not None else DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS
    executor = CURRENT[0]
    prefix = getattr(executor, "_prefix_solver", None)
    if prefix is None:
        prefix = executor._prefix_solver = PrefixSolver()
    conjuncts = list(self._constraints) + list(self.flag_constraints.values())
    result = prefix.check(conjuncts, timeout_ms, info)
    if result == sat:
        self._witness = prefix.solver.model()
        return True
    self._witness = None
    if result == unsat:
        return False
    from verification.block_equivalence import abstract_nonlinear_mul
    relaxed, changed = abstract_nonlinear_mul(self.as_bool())
    if changed:
        probe = SolverFor("QF_AUFBV")
        probe.add(relaxed)
        if _timed_check(probe, timeout_ms, "probe", info) == unsat:
            return False
    return True


MODELS = []  # recent reachability models (prototype stand-in for passing the path's witness to apply)


def install_entry_witness(log):
    """Summary-hit "entry" (premise SAT) answered by a model of the premise when one of the
    recent reachability models satisfies it: a model is a SAT certificate."""
    from verification.block_summaries import VerifiedSummaryRuntime
    from verification.block_equivalence import Obligation
    inner = VerifiedSummaryRuntime._solve
    hits = [0, 0]

    def solve(self, name, formula, expected="unsat"):
        if name == "entry" and expected == "sat":
            t = monotonic()
            for m in reversed(MODELS[-16:]):
                if is_true(m.eval(formula, model_completion=True)):
                    hits[0] += 1
                    self.proof_queries += 1
                    return Obligation(name, formula.sexpr(), "sat", expected, monotonic() - t)
            hits[1] += 1
        return inner(self, name, formula, expected)
    VerifiedSummaryRuntime._solve = solve
    return hits


_orig_incprobe = incprobe


def incprobe_models(self, solver_timeout, info):
    r = _orig_incprobe(self, solver_timeout, info)
    if r and self._witness is not None:
        if not MODELS or MODELS[-1] is not self._witness:
            MODELS.append(self._witness)
            del MODELS[:-16]
    return r


ABS_MEMO, ABS_FUNCS = {}, {}


def _abstract_conjunct(c):
    """Per-conjunct bvmul->UF abstraction with one shared UF per (width, arity):
    interpreting each UF as bvmul extends every model, so UNSAT transfers back."""
    from verification.block_equivalence import abstract_nonlinear_mul
    k = c.get_id()
    hit = ABS_MEMO.get(k)
    if hit is None:
        hit = ABS_MEMO[k] = (c, abstract_nonlinear_mul(c, functions=ABS_FUNCS)[0])
    return hit[1]


def incprobe2(self, solver_timeout, info):
    """incprobe, but the unknown fallback probe is incremental too (per-executor
    PrefixSolver over the abstracted conjuncts)."""
    if self._witness is not None and is_true(self._witness.eval(self.as_bool(), model_completion=True)):
        info["w"] = 1
        return True
    timeout_ms = solver_timeout if solver_timeout is not None else DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS
    executor = CURRENT[0]
    if getattr(executor, "_prefix_solver", None) is None:
        executor._prefix_solver, executor._probe_solver = PrefixSolver(), PrefixSolver()
    conjuncts = list(self._constraints) + list(self.flag_constraints.values())
    result = executor._prefix_solver.check(conjuncts, timeout_ms, info)
    if result == sat:
        self._witness = executor._prefix_solver.solver.model()
        return True
    self._witness = None
    if result == unsat:
        return False
    t = monotonic()
    relaxed = [_abstract_conjunct(c) for c in conjuncts]
    info["abs"] = round(monotonic() - t, 4)
    if any(not r.eq(c) for r, c in zip(relaxed, conjuncts)):
        sub = {}
        r = executor._probe_solver.check(relaxed, timeout_ms, sub)
        info["probe"] = sub.get("inc")
        if r == unsat:
            return False
    return True


def incprobe2_models(self, solver_timeout, info):
    r = incprobe2(self, solver_timeout, info)
    if r and self._witness is not None:
        if not MODELS or MODELS[-1] is not self._witness:
            MODELS.append(self._witness)
            del MODELS[:-16]
    return r


MODES = {"base": base, "incprobe": incprobe, "incprobe_entry": incprobe_models, "incprobe2_entry": incprobe2_models}
