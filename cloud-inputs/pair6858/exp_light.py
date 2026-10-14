"""Time the light-premise query of the sha3_slice argument pair of goal part K
(after skolemize + normalize_word_arith, as the unify* route sees it):
exp_light.py FILE.smt2 [K] [--repeat N]   (repository root, PYTHONPATH=.)

Reports solve time of simplify(light ∧ hide(differ)) with a 120s budget, the
answer at the production 2s cap, and the size of the light premise.
"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be


def main():
    sys.setrecursionlimit(100000)
    path = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2
    repeat = int(sys.argv[sys.argv.index("--repeat") + 1]) if "--repeat" in sys.argv else 3
    f = And(*parse_smt2_file(path))
    part, _ = be.skolemize_array_disequalities(be._goal_split(f)[k])
    part, _ = be.normalize_word_arith(part)
    base = be.abstract_nonlinear_mul(part, functions={})[0]
    parts = [c for c in be._conjuncts(base) if be._no_binder(c)]
    for apps in be._uf_applications(base):
        for i, first in enumerate(apps):
            for other in apps[i + 1:]:
                for x, y in zip(first.children(), other.children()):
                    if x.eq(y):
                        continue
                    premise = And(*parts)
                    differ = be._differ(x, y)
                    opaque = be._uf_app_constants(premise, differ)
                    hide = (lambda t: substitute(t, *opaque)) if opaque else (lambda t: t)
                    light = [c for c in parts if not (be._no_binder(c) and be._heavy(c))]
                    print(f"{apps[0].decl().name()}: {len(parts)} conjuncts, light {len(light)}, x {len(x.sexpr())} y {len(y.sexpr())} array {be._is_array_term(x)}", flush=True)
                    query = simplify(And(*light, hide(differ)))
                    for _ in range(repeat):
                        t = monotonic()
                        a = be.solve_query(query, 120_000)
                        t1 = monotonic() - t
                        t = monotonic()
                        b = be.solve_query(query, be._LIGHT_MS)
                        print(f"  120s: {a} {t1:.2f}s; at {be._LIGHT_MS}ms: {b} {monotonic() - t:.2f}s", flush=True)


if __name__ == "__main__":
    main()
