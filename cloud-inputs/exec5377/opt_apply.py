r"""Prototype (monkeypatch): refute `premise /\\ goal` by a complementary conjunct before solving.

P6. A summary gate asks whether the path condition excludes a goal G (memgas exit
    guard: the executor's split itself appended Not(guard) to the path). If
    simplify(G) is false, or equals simplify(Not(c)) for one of the path
    condition's conjuncts c, then c /\\ G is propositionally UNSAT, hence so is
    every conjunction containing both: no solver call is needed. Otherwise the
    unchanged solver query runs. simplify is an equivalence-preserving rewriter.
"""
from time import monotonic

from z3 import And, Not, is_and, is_false, simplify

RECENT = 16  # conjuncts examined, most recent first (the split appends Not(guard) last)
STATS = {"hit": 0, "miss": 0}


def _flat(e, out):
    if is_and(e):
        for c in e.children():
            _flat(c, out)
    else:
        out.append(e)
    return out


def complement_refutes(conjuncts, goal):
    g = simplify(goal)
    if is_false(g):
        return True
    for c in conjuncts[::-1][:RECENT]:
        if simplify(Not(c)).eq(g):
            return True
    return False


def install():
    import x86_64.summaries.memgas as memgas
    from verification.block_summaries import VerifiedSummaryRuntime
    from verification.block_equivalence import Obligation

    inner_require = memgas._require_implied

    def require_implied(summary, state, path_condition, goal, label, timeout_ms):
        conjuncts = _flat(path_condition, []) if path_condition is not None else []
        if complement_refutes(conjuncts, Not(goal)):
            STATS["hit"] += 1
            return
        STATS["miss"] += 1
        return inner_require(summary, state, path_condition, goal, label, timeout_ms)
    memgas._require_implied = require_implied

    inner_solve = VerifiedSummaryRuntime._solve

    def solve(self, name, formula, expected="unsat"):
        if expected == "unsat" and is_and(formula) and formula.num_args() >= 2:
            started = monotonic()
            top = formula.children()
            if complement_refutes(_flat(And(*top[:-1]), []), top[-1]):
                STATS["hit"] += 1
                self.proof_queries += 1
                return Obligation(name, formula.sexpr(), "unsat", expected, monotonic() - started)
            STATS["miss"] += 1
        return inner_solve(self, name, formula, expected)
    VerifiedSummaryRuntime._solve = solve
    return STATS
