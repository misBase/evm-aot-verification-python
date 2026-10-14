"""Dump the opaque-UF queries of the unify* route on goal part K after the UF merges:
exp_opaque.py FILE.smt2 OUT_PREFIX [K] [--light-ms N]   (repository root, PYTHONPATH=.)

Writes OUT_PREFIX.full.smt2 (simplify(unified[opaque])) and OUT_PREFIX.light.smt2
(its non-heavy conjuncts, as _refute_over_light_premise builds it). --light-ms
(diagnostic) raises _LIGHT_MS so the merges of the route succeed regardless of load.
"""
import sys
from time import monotonic

from z3 import And, BoolVal, Solver, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be


def dump(formula, path):
    s = Solver()
    s.add(formula)
    with open(path, "w") as handle:
        handle.write(s.to_smt2())


def main():
    sys.setrecursionlimit(100000)
    path, out = sys.argv[1], sys.argv[2]
    k = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 2
    if "--light-ms" in sys.argv:
        be._LIGHT_MS = int(sys.argv[sys.argv.index("--light-ms") + 1])
    f = And(*parse_smt2_file(path))
    part, _ = be.skolemize_array_disequalities(be._goal_split(f)[k])
    target, _ = be.normalize_word_arith(part)
    base = be.abstract_nonlinear_mul(target, functions={})[0]
    # Only the array-argument pairs (memory arguments): the mul-UF pairs all fail here (unify log).
    real = be._uf_applications
    be._uf_applications = lambda g: [a for a in real(g) if any(be._is_array_term(x) for x in a[0].children())]
    t = monotonic()
    unified, lemmas = be.unify_uf_arguments(base, 30000, monotonic() + 1800, cache={})
    print(f"unify {monotonic() - t:.1f}s lemmas {len(lemmas)}", flush=True)
    opaque = [(a, c) for a, c in be._uf_app_constants(unified) if any(be._is_array_term(x) for x in a.children())]
    query = simplify(substitute(unified, *opaque))
    dump(query, out + ".full.smt2")
    light = [c for c in be._conjuncts(query) if not (be._no_binder(c) and be._heavy(c))]
    dump(simplify(And(*light, BoolVal(True))), out + ".light.smt2")
    print(f"conjuncts {len(be._conjuncts(query))} light {len(light)}", flush=True)


if __name__ == "__main__":
    main()
