"""Variants of a dumped opaque query. Usage (repo root, PYTHONPATH=.): opaque_exp.py FILE.smt2 timeout_ms VARIANT...
VARIANTs: light, full, blast (light + blast_select_store), lightgoal (only conjuncts sharing constants
with the goal, transitively, light), core (unsat core of light over light conjuncts)."""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, Solver, Bool

import verification.block_equivalence as be

f = And(*parse_smt2_file(sys.argv[1]))
tmo = int(sys.argv[2])
parts = be._conjuncts(f)
goal = [c for c in parts if not be._no_binder(c)]
light = [c for c in parts if not (be._no_binder(c) and be._heavy(c))]
print(len(parts), "conjuncts", len(light), "light", len(goal), "goal", flush=True)


def run(label, q):
    t = monotonic()
    print(label, be.solve_query(q, tmo), f"{monotonic() - t:.1f}s", flush=True)


for v in sys.argv[3:]:
    if v == "light":
        run(v, simplify(And(*light)))
    elif v == "full":
        run(v, simplify(And(*parts)))
    elif v == "blast":
        run(v, simplify(And(*light), blast_select_store=True))
    elif v == "core":
        s = Solver()
        s.set("timeout", tmo)
        lits = {}
        for k, c in enumerate(light):
            if be._no_binder(c):
                p = Bool(f"core_{k}")
                lits[p] = c
                s.assert_and_track(c, p)
            else:
                s.add(c)
        t = monotonic()
        r = s.check()
        print("core", r, f"{monotonic() - t:.1f}s", flush=True)
        if str(r) == "unsat":
            for p in s.unsat_core():
                print("  ", " ".join(lits[p].sexpr().split()).replace("blk5377_30_None_None_", "")[:600])
