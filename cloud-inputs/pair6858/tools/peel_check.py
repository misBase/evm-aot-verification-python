"""peel_matching_stores on a dumped opaque query, then the light query.
Usage (repo root, PYTHONPATH=.): peel_check.py FILE.smt2 timeout_ms"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, BoolVal

import verification.block_equivalence as be

q = simplify(And(*parse_smt2_file(sys.argv[1])))
t = monotonic()
p = be.peel_matching_stores(q)
print("peel", p is not None, f"{monotonic() - t:.1f}s", flush=True)
p = simplify(p)
t = monotonic()
r = be._refute_over_light_premise(be._conjuncts(p), BoolVal(True), int(sys.argv[2]))
print("light", r is not None, f"{monotonic() - t:.1f}s", flush=True)
