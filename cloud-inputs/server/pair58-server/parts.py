"""Per-goal-part quick look: premise SAT?, and each R ∧ ¬g_k with plain solve_query.
Usage (cwd=snapshot, PYTHONPATH=.): parts.py FILE.smt2 [timeout_ms] [only_parts,comma]"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file, simplify, Solver, SolverFor, is_and

import verification.block_equivalence as be

path = sys.argv[1]
tmo = int(sys.argv[2]) if len(sys.argv) > 2 else 60000
only = None if len(sys.argv) <= 3 else {int(x) for x in sys.argv[3].split(",")}
f = And(*parse_smt2_file(path))
top = f
while is_and(top) and top.num_args() == 1:
    top = top.arg(0)
*rest, last = top.children()
premise = And(*rest)
if only is None or -1 in only:
    t = monotonic()
    print("premise", be.solve_query(simplify(premise), tmo), f"{monotonic()-t:.1f}s", flush=True)
for k, part in enumerate(be._goal_split(f)):
    if only is not None and k not in only:
        continue
    t = monotonic()
    g, _ = be.skolemize_array_disequalities(part)
    print(f"part {k}", be.solve_query(simplify(g), tmo), f"{monotonic()-t:.1f}s", flush=True)
