"""Isolate the sha3_slice argument equality of goal part K (repository root, PYTHONPATH=.):
exp_sha3.py FILE.smt2 [K] [--norm] [--seconds N]

Builds part K of the goal split (R ∧ ¬g_K, after skolemize_array_disequalities),
optionally normalize_word_arith, then for each differing argument pair of the
sha3_slice applications outside binders times: the light-premise query, the full
premise query (hide(premise) ∧ hide(differ)), and reports sizes.
"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be


def main():
    sys.setrecursionlimit(100000)
    path = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2
    seconds = float(sys.argv[sys.argv.index("--seconds") + 1]) if "--seconds" in sys.argv else 120
    f = And(*parse_smt2_file(path))
    part, _ = be.skolemize_array_disequalities(be._goal_split(f)[k])
    if "--norm" in sys.argv:
        t = monotonic()
        part, rewrites = be.normalize_word_arith(part)
        print(f"normalize {monotonic() - t:.1f}s, {len(rewrites)} rewrites")
    premise_parts = [c for c in be._conjuncts(part) if be._no_binder(c)]
    print(f"conjuncts {len(be._conjuncts(part))}, binder-free {len(premise_parts)},"
          f" heavy {sum(1 for c in premise_parts if be._heavy(c))}")
    for apps in be._uf_applications(part):
        print("UF", apps[0].decl().name(), len(apps))
        for i, first in enumerate(apps):
            for other in apps[i + 1:]:
                for n, (x, y) in enumerate(zip(first.children(), other.children())):
                    if x.eq(y):
                        continue
                    print(f"  arg {n}: {len(x.sexpr())} / {len(y.sexpr())} chars")
                    premise = And(*premise_parts)
                    differ = be._differ(x, y)
                    opaque = be._uf_app_constants(premise, differ)
                    hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
                    t = monotonic()
                    r = be._refute_over_light_premise(premise_parts, hide(differ), int(seconds * 1000))
                    print(f"    light: {'unsat' if r else 'no'} {monotonic() - t:.1f}s")
                    t = monotonic()
                    a = be.solve_query(simplify(And(hide(premise), hide(differ))), int(seconds * 1000))
                    print(f"    full: {a} {monotonic() - t:.1f}s", flush=True)


if __name__ == "__main__":
    main()
