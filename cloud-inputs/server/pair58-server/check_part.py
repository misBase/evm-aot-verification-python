"""Production _check on one goal part of a captured obligation, with per-route timing.
Usage (cwd=snapshot, PYTHONPATH=.): check_part.py FILE.smt2 PART|all [seconds]
PART=all runs the whole obligation (as check_obligation.py)."""
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
        ans = out[1] if isinstance(out, tuple) and len(out) > 1 and isinstance(out[1], str) else (
            out if isinstance(out, str) else type(out).__name__)
        print(f"  [{monotonic()-T0:7.1f}] {name} {monotonic()-t:.1f}s -> {ans}", flush=True)
        return out
    setattr(owner, name, wrapper)


P = be.BlockEquivalenceProver
for n in ("_retry_over_lia", "_retry_over_potential", "_retry_over_nonlinear_mul", "_retry_with_uf_unification"):
    traced(P, n)
for n in ("pin_split", "_alias_split", "refute_over_bv_abstraction", "normalize_word_arith"):
    traced(be, n)

_sq = be.solve_query


def sq(formula, timeout_ms):
    t = monotonic()
    a = _sq(formula, timeout_ms)
    if monotonic() - t > 2:
        print(f"    [{monotonic()-T0:7.1f}] solve_query {monotonic()-t:.1f}s budget={timeout_ms} -> {a}", flush=True)
    return a


be.solve_query = sq

path, part = sys.argv[1], sys.argv[2]
secs = float(sys.argv[3]) if len(sys.argv) > 3 else 1800
f = And(*parse_smt2_file(path))
if part != "all":
    f = be._goal_split(f)[int(part)]
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = monotonic() + secs
records, started = [], monotonic()
ok = prover._check(path.rsplit("/", 1)[-1] + f"_p{part}", f, records, split=(part == "all"))
print(path.rsplit("/", 1)[-1], part, "proved" if ok else records[-1].answer, f"{monotonic() - started:.1f}s",
      f"lemmas={len(records[-1].lemmas)}", flush=True)
