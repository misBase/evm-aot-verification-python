"""Conjunct-level diff of two captured obligations (by sexpr), goal parts compared separately.
Usage (cwd=snapshot, PYTHONPATH=.): cdiff.py A.smt2 B.smt2"""
import sys
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, is_and

import verification.block_equivalence as be


def load(p):
    f = And(*parse_smt2_file(p))
    while is_and(f) and f.num_args() == 1:
        f = f.arg(0)
    *rest, last = f.children()
    prem = {}
    for c in be._conjuncts(And(*rest)):
        prem.setdefault(c.sexpr(), c)
    return prem, list(last.arg(0).children())


pa, ga = load(sys.argv[1])
pb, gb = load(sys.argv[2])
print("premise conjuncts A", len(pa), "B", len(pb), "common", len(pa.keys() & pb.keys()))
for name, only in (("ONLY A", pa.keys() - pb.keys()), ("ONLY B", pb.keys() - pa.keys())):
    print("=====", name, len(only))
    for s in sorted(only, key=len):
        print("  ", " ".join(s.split())[:1500])
for k, (x, y) in enumerate(zip(ga, gb)):
    print(f"goal[{k}] same={x.sexpr() == y.sexpr()} sizes {len(x.sexpr())} {len(y.sexpr())}")
