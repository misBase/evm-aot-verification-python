"""Experiment: when the light query is SAT, does its model satisfy the full premise ∧ goal?
(If so the pair is genuinely unequal and the full attempt could be skipped.)
Usage (cwd=patched snapshot, PYTHONPATH=.): modelcheck.py FILE.smt2 PART"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, sat, is_true

import verification.block_equivalence as be

stats = {"sat": 0, "confirmed": 0, "unsat": 0, "other": 0, "t": 0.0}


def light_with_model(parts, goal, budget_ms):
    light = [c for c in parts if not (be._no_binder(c) and be._heavy(c))]
    if len(light) == len(parts):
        return None
    t = monotonic()
    query = simplify(And(*light, goal))
    s = be._solver(budget_ms, query)
    s.add(query)
    r = s.check()
    if r == sat:
        stats["sat"] += 1
        m = s.model()
        if all(is_true(m.eval(c, model_completion=True)) for c in parts) and is_true(m.eval(goal, model_completion=True)):
            stats["confirmed"] += 1
    elif str(r) == "unsat":
        stats["unsat"] += 1
        stats["t"] += monotonic() - t
        return [(query, monotonic() - t)], frozenset(c.get_id() for c in light)
    else:
        stats["other"] += 1
    stats["t"] += monotonic() - t
    return None


be._refute_over_light_premise = light_with_model
part = be._goal_split(And(*parse_smt2_file(sys.argv[1])))[int(sys.argv[2])]
sk, _ = be.skolemize_array_disequalities(part)
target, _ = be.normalize_word_arith(sk)
base = be.abstract_nonlinear_mul(target, functions={})[0]
t = monotonic()
_, lemmas = be.unify_uf_arguments(base, 30000, monotonic() + 900, cache={})
print("unify_uf_arguments", f"{monotonic()-t:.1f}s", len(lemmas), "lemmas", stats, flush=True)
