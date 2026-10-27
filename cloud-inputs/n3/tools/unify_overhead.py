"""cProfile of unify_uf_arguments on one guard case of an obligation (where the non-solver time goes).

Usage (repo root, PYTHONPATH=.): unify_overhead.py FILE.smt2 [--seconds S] [--case true|false|none]
Splits on the smallest ite guard over a multiply-applied UF (as guard_split.py) unless --case none.
Diagnostics only.
"""
import cProfile
import pstats
import sys
import time

from z3 import And, BoolVal, Not, Z3_OP_ITE, is_app, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be

argv = sys.argv[1:]
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 300
which = argv[argv.index("--case") + 1] if "--case" in argv else "true"
formula = And(*parse_smt2_file(argv[0]))
if which != "none":
    multi = {apps[0].decl().get_id() for apps in be._uf_applications(formula)}
    memo = {}

    def has_app(t):
        if t.get_id() not in memo:
            memo[t.get_id()] = is_app(t) and (
                (t.decl().kind() == be.Z3_OP_UNINTERPRETED and t.decl().get_id() in multi)
                or any(has_app(c) for c in t.children()))
        return memo[t.get_id()]
    found, seen, work = {}, set(), [formula]
    while work:
        t = work.pop()
        if t.get_id() in seen or not is_app(t):
            continue
        seen.add(t.get_id())
        if t.decl().kind() == Z3_OP_ITE and (has_app(t.arg(1)) or has_app(t.arg(2))):
            found.setdefault(simplify(t.arg(0)).get_id(), (len(simplify(t.arg(0)).sexpr()), t.arg(0)))
        work.extend(t.children())
    c = min(found.values(), key=lambda v: v[0])[1]
    v = which == "true"
    formula = And(c if v else Not(c), simplify(substitute(formula, (c, BoolVal(v)))))
prof = cProfile.Profile()
prof.enable()
started = time.monotonic()
unified, lemmas = be.unify_uf_arguments(formula, 30000, time.monotonic() + seconds)
prof.disable()
print(f"{len(lemmas)} lemmas in {time.monotonic() - started:.1f}s", flush=True)
pstats.Stats(prof).sort_stats("cumulative").print_stats(40)
pstats.Stats(prof).sort_stats("tottime").print_stats(25)
