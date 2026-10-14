"""Print the binder conjunct(s) of a dumped query, simplified, with name prefix stripped.
Usage (repo root, PYTHONPATH=.): goalprint.py FILE.smt2"""
import sys
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
for c in be._conjuncts(f):
    if not be._no_binder(c):
        print(simplify(c).sexpr().replace("blk5377_30_None_None_", ""))
