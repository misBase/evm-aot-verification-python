"""Run only the unify(norm) route of _check on a goal part, timing its steps.
Usage (cwd=snapshot, PYTHONPATH=.): unify_only.py FILE.smt2 PART [seconds]"""
import functools
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file

import verification.block_equivalence as be

T0 = monotonic()


def traced(owner, name):
    fn = getattr(owner, name)

    @functools.wraps(fn)
    def wrapper(*a, **k):
        t = monotonic()
        out = fn(*a, **k)
        info = out[1] if isinstance(out, tuple) and len(out) > 1 and isinstance(out[1], str) else (
            f"{len(out[1])} lemmas" if isinstance(out, tuple) and len(out) > 1 and isinstance(out[1], tuple) else type(out).__name__)
        print(f"  [{monotonic()-T0:7.1f}] {name} {monotonic()-t:.1f}s -> {info}", flush=True)
        return out
    setattr(owner, name, wrapper)


for n in ("unify_uf_arguments", "sweep_equalities", "_refute_by_cases", "_refute_over_light_premise"):
    if hasattr(be, n):
        traced(be, n)
_sq = be.solve_query


def sq(formula, timeout_ms):
    t = monotonic()
    a = _sq(formula, timeout_ms)
    if monotonic() - t > 1:
        print(f"    [{monotonic()-T0:7.1f}] solve_query {monotonic()-t:.1f}s budget={timeout_ms} -> {a}", flush=True)
    return a


be.solve_query = sq
path, k = sys.argv[1], int(sys.argv[2])
secs = float(sys.argv[3]) if len(sys.argv) > 3 else 1200
part = be._goal_split(And(*parse_smt2_file(path)))[k]
sk, _ = be.skolemize_array_disequalities(part)
target, rw = be.normalize_word_arith(sk)
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = monotonic() + secs
t = monotonic()
proved, answer, lemmas = prover._retry_with_uf_unification(target, "unknown")
print("unify(norm)", answer, f"{monotonic()-t:.1f}s", "lemmas", len(lemmas), [l.name for l in lemmas][-3:], flush=True)
