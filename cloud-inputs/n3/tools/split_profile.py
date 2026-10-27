"""Profile guard_split's per-case unification: every _prove_equal call (UF, sizes, outcome, seconds).

Usage (repo root, PYTHONPATH=.): split_profile.py FILE.smt2 [--ms N] [--max-guards K]
Same cases as cloud-inputs/n2/tools/guard_split.py. Diagnostics only.
"""
import itertools
import sys
import time

from z3 import And, BoolVal, Not, Z3_OP_ITE, is_app, parse_smt2_file, simplify, substitute

import verification.block_equivalence as be

argv = sys.argv[1:]
ms = int(argv[argv.index("--ms") + 1]) if "--ms" in argv else 30000
k_max = int(argv[argv.index("--max-guards") + 1]) if "--max-guards" in argv else 1
formula = And(*parse_smt2_file(argv[0]))
T0 = time.monotonic()
orig = be._prove_equal
calls = []


def prove_equal(premise, x, y, budget_ms, deadline, cache=None):
    t = time.monotonic()
    out = orig(premise, x, y, budget_ms, deadline, cache)
    calls.append((len(x.sexpr()), len(y.sexpr()), out is not None, time.monotonic() - t))
    print(f"[{time.monotonic() - T0:7.1f}s]   prove_equal {len(x.sexpr())}/{len(y.sexpr())} "
          f"{'ok' if out is not None else 'FAIL'} {time.monotonic() - t:.1f}s", flush=True)
    return out


be._prove_equal = prove_equal
multi = {apps[0].decl().get_id() for apps in be._uf_applications(formula)}


def has_app(t, memo):
    if t.get_id() in memo:
        return memo[t.get_id()]
    out = is_app(t) and ((t.decl().kind() == be.Z3_OP_UNINTERPRETED and t.decl().get_id() in multi)
                         or any(has_app(c, memo) for c in t.children()))
    memo[t.get_id()] = out
    return out


found, seen, work, memo = {}, set(), [formula], {}
while work:
    t = work.pop()
    if t.get_id() in seen or not is_app(t):
        continue
    seen.add(t.get_id())
    if t.decl().kind() == Z3_OP_ITE and (has_app(t.arg(1), memo) or has_app(t.arg(2), memo)):
        found.setdefault(simplify(t.arg(0)).get_id(), (len(simplify(t.arg(0)).sexpr()), t.arg(0)))
    work.extend(t.children())
guards = [g for _, g in sorted(found.values(), key=lambda v: v[0])]
print("guards", len(guards), [len(g.sexpr()) for g in guards][:10], flush=True)
for values in itertools.product((True, False), repeat=min(k_max, len(guards))):
    chosen = guards[:len(values)]
    started = time.monotonic()
    calls.clear()
    case = substitute(formula, *[(c, BoolVal(v)) for c, v in zip(chosen, values)])
    case = And(*[c if v else Not(c) for c, v in zip(chosen, values)], simplify(case))
    apps = be._uf_applications(case)
    unified, lemmas = be.unify_uf_arguments(case, ms, time.monotonic() + 1800)
    t_unify = time.monotonic() - started
    direct = be.solve_query(simplify(unified), ms)
    ok = sum(1 for c in calls if c[2])
    print(f"case {values}: apps {[len(a) for a in apps]} -> {[len(a) for a in be._uf_applications(unified)]}, "
          f"{len(lemmas)} lemmas, calls {len(calls)} ok {ok} ({sum(c[3] for c in calls if c[2]):.1f}s) "
          f"fail {len(calls) - ok} ({sum(c[3] for c in calls if not c[2]):.1f}s), unify {t_unify:.1f}s, "
          f"direct {direct}, {time.monotonic() - started:.1f}s", flush=True)
