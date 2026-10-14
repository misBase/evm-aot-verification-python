"""Shape of a dumped opaque query: conjuncts with binders / heavy / mentioning given names.
Usage (repo root, PYTHONPATH=.): opaque_shape.py FILE.smt2"""
import sys
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
parts = be._conjuncts(f)
print(len(parts), "conjuncts")
for k, c in enumerate(parts):
    tag = ("BINDER " if not be._no_binder(c) else "") + ("HEAVY " if be._heavy(c) else "")
    s = " ".join(c.sexpr().split()).replace("blk5377_30_None_None_", "")
    print(f"[{k}] {tag}len={len(s)} {s[:700]}")
