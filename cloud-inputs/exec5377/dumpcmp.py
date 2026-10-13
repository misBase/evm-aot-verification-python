"""Compare two paths.smt2 dumps (same block): structural hash, then semantic equivalence.

usage: dumpcmp.py DIR_A DIR_B [TIMEOUT_MS]   (cwd = snapshot, PYTHONPATH=.)
"""
import json
import sys
from pathlib import Path
from time import monotonic

from z3 import Xor, SolverFor, parse_smt2_file, unsat

sys.path.insert(0, str(Path(__file__).parent))
from canon_hash import canon_hash  # noqa: E402
from verification.block_equivalence import abstract_nonlinear_mul  # noqa: E402

a, b = Path(sys.argv[1]), Path(sys.argv[2])
tmo = int(sys.argv[3]) if len(sys.argv) > 3 else 30000
ma, mb = (json.loads((d / "paths_meta.json").read_text()) for d in (a, b))
A, B = list(parse_smt2_file(str(a / "paths.smt2"))), list(parse_smt2_file(str(b / "paths.smt2")))
print("meta", ma, mb, "premise same hash", canon_hash(A[0]) == canon_hash(B[0]), flush=True)
memo = {}
res = {"same_hash": 0, "equivalent": 0, "unknown": 0, "DIFFERENT": 0}
for label, off, n in (("evm", 1, ma["evm"]), ("x86", 1 + ma["evm"], ma["x86"])):
    for j in range(n):
        x, y = A[off + j], B[off + j]
        if canon_hash(x, memo) == canon_hash(y, memo):
            res["same_hash"] += 1
            continue
        t = monotonic()
        q = Xor(x, y)
        relaxed, _ = abstract_nonlinear_mul(q)  # UNSAT of the abstraction: equivalent
        s = SolverFor("QF_AUFBV")
        s.set(timeout=tmo)
        s.add(relaxed)
        r = s.check()
        if r != unsat:
            s = SolverFor("QF_AUFBV")
            s.set(timeout=tmo)
            s.add(q)
            r2 = s.check()
            r = r2
        key = "equivalent" if r == unsat else ("DIFFERENT" if str(r) == "sat" else "unknown")
        res[key] += 1
        print(label, j, key, f"{monotonic() - t:.1f}s", flush=True)
print(res, flush=True)
