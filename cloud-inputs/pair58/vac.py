"""Is the pair's premise (path conditions, goal dropped) UNSAT after normalize_word_arith? (vacuous pair)
Usage (cwd=snapshot, PYTHONPATH=.): vac.py FILE.smt2 timeout_ms"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, is_and

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
while is_and(f) and f.num_args() == 1:
    f = f.arg(0)
premise = And(*f.children()[:-1])
t = monotonic()
norm, rw = be.normalize_word_arith(premise)
print("normalized", len(rw), f"{monotonic()-t:.1f}s", flush=True)
t = monotonic()
print("premise(norm)", be.solve_query(norm, int(sys.argv[2])), f"{monotonic()-t:.1f}s", flush=True)
