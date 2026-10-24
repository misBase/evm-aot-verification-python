"""Experiment: split an obligation on the ite guards above its UF applications, then unify each case.

Usage (repo root, PYTHONPATH=.): guard_split.py FILE.smt2 [--ms N] [--max-guards K]
Prints the guards (ite conditions with a UF application of a multiply-applied UF in a branch),
then for each of the 2^k cases: the UF applications left, unify_uf_arguments merges, and the
answer of the unified case (direct and blasted). Diagnostics only.
"""
import itertools
import sys
import time

from z3 import And, BoolVal, Not, Z3_OP_ITE, is_app, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be

argv = sys.argv[1:]
ms = int(argv[argv.index("--ms") + 1]) if "--ms" in argv else 30000
k_max = int(argv[argv.index("--max-guards") + 1]) if "--max-guards" in argv else 4
formula = And(*parse_smt2_file(argv[0]))
multi = {apps[0].decl().get_id() for apps in be._uf_applications(formula)}


def has_app(t, memo):
    if t.get_id() in memo:
        return memo[t.get_id()]
    out = is_app(t) and ((t.decl().kind() == be.Z3_OP_UNINTERPRETED and t.decl().get_id() in multi)
                         or any(has_app(c, memo) for c in t.children()))
    memo[t.get_id()] = out
    return out


guards, seen, work, memo = {}, set(), [formula], {}
while work:
    t = work.pop()
    if t.get_id() in seen or not is_app(t):
        continue
    seen.add(t.get_id())
    if t.decl().kind() == Z3_OP_ITE and (has_app(t.arg(1), memo) or has_app(t.arg(2), memo)):
        c = simplify(t.arg(0))
        guards.setdefault(c.get_id(), (t.arg(0), c, len(t.arg(0).sexpr())))
    work.extend(t.children())
print("guards", len(guards), flush=True)
for raw, c, size in sorted(guards.values(), key=lambda g: g[2]):
    print("  ", size, " ".join(c.sexpr().split())[:200], flush=True)
chosen = [raw for raw, _, _ in sorted(guards.values(), key=lambda g: g[2])][:k_max]
for values in itertools.product((True, False), repeat=len(chosen)):
    started = time.monotonic()
    case = substitute(formula, *[(c, BoolVal(v)) for c, v in zip(chosen, values)])
    case = And(*[c if v else Not(c) for c, v in zip(chosen, values)], simplify(case))
    apps = be._uf_applications(case)
    unified, lemmas = be.unify_uf_arguments(case, ms, time.monotonic() + 600)
    after = be._uf_applications(unified)
    direct = be.solve_query(simplify(unified), ms)
    blasted = be.solve_query(simplify(unified, blast_select_store=True), ms) if direct != "unsat" else "-"
    print(f"case {values}: apps {[len(a) for a in apps]} -> {[len(a) for a in after]}, {len(lemmas)} merges, "
          f"direct {direct}, blasted {blasted}, {time.monotonic() - started:.1f}s", flush=True)
