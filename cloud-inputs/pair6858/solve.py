"""solve.py FILE.smt2 [SECONDS] [--blast]: solve_query on a dumped query (PYTHONPATH=.).
--blast first simplifies with blast_select_store=True (as the blast route does)."""
import sys
from time import monotonic

from z3 import And, parse_smt2_file, simplify

import verification.block_equivalence as be

sys.setrecursionlimit(100000)
f = And(*parse_smt2_file(sys.argv[1]))
seconds = float(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 600
if "--blast" in sys.argv:
    f = simplify(f, blast_select_store=True)
t = monotonic()
print(sys.argv[1], be.solve_query(f, int(seconds * 1000)), f"{monotonic() - t:.1f}s", flush=True)
