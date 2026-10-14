"""Prototype: peel the matching top stores of a read disequality A[i] != B[j] (j = i + d)
in a dumped opaque query, then time the residual: exp_peel.py FILE.smt2 [SECONDS] [--no-diseq]
(PYTHONPATH=.)."""
import sys
from time import monotonic

from z3 import And, BoolVal, is_eq, is_not, is_select, is_store, parse_smt2_file, simplify

import verification.block_equivalence as be


def peel(a, i, b, j):
    d = simplify(j - i)
    diseq, n = [], 0
    while is_store(a) and is_store(b):
        (ra, ka, va), (rb, kb, vb) = a.children(), b.children()
        if not simplify(kb - ka - d).eq(simplify(i - i)) or not simplify(va == vb, bv_sort_ac=True).eq(BoolVal(True)):
            break
        diseq.append(i != ka)
        a, b, n = ra, rb, n + 1
    return n, a, b, diseq


def main():
    sys.setrecursionlimit(100000)
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 300
    parts = be._conjuncts(And(*parse_smt2_file(sys.argv[1])))
    out = []
    for c in parts:
        if is_not(c) and is_eq(c.arg(0)) and all(is_select(x) for x in c.arg(0).children()):
            (a, i), (b, j) = (x.children() for x in c.arg(0).children())
            n, ra, rb, diseq = peel(a, i, b, j)
            print(f"peeled {n} stores; rest A store={is_store(ra)} B store={is_store(rb)}")
            out.append(simplify(ra[i] != rb[j]))
            if "--no-diseq" not in sys.argv:
                out.extend(diseq)
        else:
            out.append(c)
    t = monotonic()
    q = simplify(And(*out))
    print("residual", be.solve_query(q, int(seconds * 1000)), f"{monotonic() - t:.1f}s", flush=True)


if __name__ == "__main__":
    main()
