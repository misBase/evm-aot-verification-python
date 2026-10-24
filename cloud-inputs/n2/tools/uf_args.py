"""UF applications of a captured obligation and whether their arguments are provably equal.

Usage (repo root, PYTHONPATH=.): uf_args.py FILE.smt2 [--ms N] [--name UF]
For every pair of applications of one UF (default: all UFs with >1 application) and each
argument position whose terms differ: the argument sizes, which free constants each side
uses, and `x != y` under the obligation's binder-free conjuncts R decided directly and
after blast_select_store (each --ms, default 30000). Diagnostics only.
"""
import sys
import time
from itertools import combinations

from z3 import And, Not, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]
ms = int(argv[argv.index("--ms") + 1]) if "--ms" in argv else 30000
only = argv[argv.index("--name") + 1] if "--name" in argv else None
formula = And(*parse_smt2_file(argv[0]))
rest = [c for c in be._conjuncts(formula)]
premise = And(*rest[:-1]) if len(rest) > 1 else formula  # last conjunct: the negated goal


def consts(t):
    out, seen, work = set(), set(), [t]
    while work:
        u = work.pop()
        if u.get_id() in seen:
            continue
        seen.add(u.get_id())
        if u.num_args() == 0 and u.decl().kind() == be.Z3_OP_UNINTERPRETED:
            out.add(u.decl().name())
        work.extend(u.children())
    return out


for apps in be._uf_applications(formula):
    name = apps[0].decl().name()
    if only and name != only:
        continue
    print(f"{name}: {len(apps)} applications", flush=True)
    for a, b in combinations(apps, 2):
        for k in range(a.num_args()):
            x, y = a.arg(k), b.arg(k)
            if x.eq(y):
                continue
            sx, sy = simplify(x), simplify(y)
            print(f"  pair {a.get_id()}/{b.get_id()} arg {k}: sizes {len(x.sexpr())}/{len(y.sexpr())}, "
                  f"consts {sorted(consts(x))[:6]} / {sorted(consts(y))[:6]}, simplify-equal {sx.eq(sy)}",
                  flush=True)
            query = And(premise, Not(x == y))
            for label, q in (("direct", query), ("blast", simplify(query, blast_select_store=True))):
                started = time.monotonic()
                answer = be.solve_query(q, ms)
                print(f"    {label}: {answer} {time.monotonic() - started:.1f}s", flush=True)
