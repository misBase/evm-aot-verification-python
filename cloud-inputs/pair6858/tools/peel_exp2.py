"""Peel matching stores off the select disequality of a dumped opaque query, then solve.
Usage (repo root, PYTHONPATH=.): peel_exp.py FILE.smt2 timeout_ms"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import (And, parse_smt2_file, simplify, is_not, is_eq, is_select, is_store, Select, is_true, Not,
                is_quantifier, substitute_vars)

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
tmo = int(sys.argv[2])
parts = be._conjuncts(f)


def peel(x, y):
    a, i = x.arg(0), x.arg(1)
    b, j = y.arg(0), y.arg(1)
    d = simplify(j - i, bv_sort_ac=True)
    n, excl = 0, []
    while is_store(a) and is_store(b):
        if not a.arg(2).eq(b.arg(2)):
            print("value mismatch at", n, a.arg(2), b.arg(2))
            break
        if not simplify(b.arg(1) - a.arg(1), bv_sort_ac=True).eq(d):
            print("address mismatch at", n, simplify(b.arg(1) - a.arg(1), bv_sort_ac=True), d)
            break
        excl.append(i != a.arg(1))
        a, b, n = a.arg(0), b.arg(0), n + 1
    print("peeled", n, "stores; left", is_store(a), is_store(b), flush=True)
    return Select(a, i), Select(b, j), excl


out = []
for c in parts:
    if is_not(c) and is_eq(c.arg(0)) and is_select(c.arg(0).arg(0)) and is_select(c.arg(0).arg(1)):
        x, y, excl = peel(c.arg(0).arg(0), c.arg(0).arg(1))
        g = And(*excl, Not(x == y)) if "excl" in sys.argv else Not(x == y)
        print("goal after peel:", " ".join(simplify(g).sexpr().split()).replace("blk5377_30_None_None_", "")[:3000])
        out.append(g)
    else:
        out.append(c)
light = [c for c in out if not (be._no_binder(c) and be._heavy(c))]
for label, q in (("peeled light", simplify(And(*light))), ("peeled full", simplify(And(*out)))):
    t = monotonic()
    print(label, be.solve_query(q, tmo), f"{monotonic() - t:.1f}s", flush=True)
