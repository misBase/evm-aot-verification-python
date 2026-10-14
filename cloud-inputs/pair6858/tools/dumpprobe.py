"""Run the unify* route (normalize -> _retry_with_uf_unification) on one goal part, logging
every _prove_equal / light / unsat_core / case-tree call.
Usage (repo root, PYTHONPATH=.): unifyprobe.py FILE.smt2 PART seconds [plain]"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify

import verification.block_equivalence as be

T0 = monotonic()


def log(*a):
    print(f"[{monotonic() - T0:7.1f}]", *a, flush=True)


def wrap(name, fn, show):
    def w(*args, **kw):
        t = monotonic()
        r = fn(*args, **kw)
        log(f"{name} {monotonic() - t:.2f}s -> {show(r, args)}")
        return r
    return w


def short(t):
    s = " ".join(t.sexpr().split())
    return f"{len(s)}:{s[:120]}"


real_pe = be._prove_equal


def prove_equal(premise, x, y, budget_ms, deadline, cache=None):
    log(f"_prove_equal budget={budget_ms} x={short(x)} y={short(y)}")
    t = monotonic()
    r = real_pe(premise, x, y, budget_ms, deadline, cache)
    log(f"  _prove_equal {monotonic() - t:.2f}s -> {'proved' if r is not None else None}")
    return r


be._prove_equal = prove_equal
real_light = be._refute_over_light_premise


def light_dump(parts, goal, budget_ms):
    if sys._getframe(2).f_code.co_name == "_retry_with_uf_unification":
        open(OUT, "w").write(be._to_smt2(And(*parts)))
        log("dumped opaque query", len(parts), "conjuncts")
    return real_light(parts, goal, budget_ms)


be._refute_over_light_premise = light_dump
be._refute_over_light_premise = wrap("  light", be._refute_over_light_premise,
                                     lambda r, a: f"{'hit' if r else 'miss'} budget={a[2]} parts={len(a[0])}")
be.unsat_core = wrap("  unsat_core", be.unsat_core, lambda r, a: f"{r is not None} {a[3] if len(a) > 3 else ''}")
be._refute_by_cases = wrap("  cases", be._refute_by_cases, lambda r, a: f"{r is not None} budget={a[2]}")
real_sq = be.solve_query


def sq(formula, timeout_ms):
    t = monotonic()
    r = real_sq(formula, timeout_ms)
    if monotonic() - t > 1.0:
        log(f"    solve_query {timeout_ms}ms {monotonic() - t:.2f}s -> {r} caller={sys._getframe(1).f_code.co_name}")
    return r


be.solve_query = sq

path, k, seconds = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
OUT = sys.argv[4]
f = And(*parse_smt2_file(path))
part = be._goal_split(f)[k]
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = monotonic() + seconds
formula, _ = be.skolemize_array_disequalities(part)
split = be.pin_split(formula, 30000, prover.deadline)
log("pin_split", None if split is None else ("sat" if split == "sat" else len(split[1])))
if split is not None and split != "sat":
    formula = split[0]
if "plain" not in sys.argv:
    formula, rewrites = be.normalize_word_arith(formula, deadline=prover.deadline)
    log("normalize", len(rewrites))
proved, answer, lemmas = prover._retry_with_uf_unification(formula, "unknown")
log("RESULT", answer, [l.name for l in lemmas])
