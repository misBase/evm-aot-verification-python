"""shared_try.py PART NAME EDGE... : common-base query for one goal conjunct over several edges' part files
(h2s/H2_c0_<edge>_t1_<NAME>.smt2); production _check on it."""
import sys
from time import monotonic
from z3 import *
import verification.block_equivalence as be

d, name, edges = sys.argv[1], sys.argv[2], sys.argv[3:]
forms = [be._conjuncts(And(*parse_smt2_file(f"{d}/H2_c0_{e}_t1_{name}.smt2"))) for e in edges]
goals = [max((c for c in cs if is_not(c)), key=lambda c: len(c.sexpr())) for cs in forms]
print("goal identical across files:", len({g.sexpr() for g in goals}) == 1, flush=True)
texts = [{c.sexpr() for c in cs} for cs in forms]
common = set.intersection(*texts)
base = [c for c in forms[0] if c.sexpr() in common and not c.eq(goals[0])]
print("conjuncts", [len(cs) for cs in forms], "common base", len(base), flush=True)
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = monotonic() + float(sys.argv[0] and 2400)
records = []
t = monotonic()
ok = prover._check(f"H2_{name}_shared", And(*base, goals[0]), records)
print(name, edges, "shared:", "proved" if ok else records[-1].answer, f"{monotonic() - t:.1f}s", flush=True)
