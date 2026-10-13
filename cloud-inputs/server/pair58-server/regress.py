"""Production _check (as check_obligation.py) over a list of captured obligations, sequentially.
Usage (cwd=snapshot, PYTHONPATH=.): regress.py LIST
LIST lines: <path.smt2> <seconds>"""
import sys
from time import monotonic
sys.setrecursionlimit(100000)
from z3 import And, parse_smt2_file

import verification.block_equivalence as be

for line in open(sys.argv[1]):
    if not line.strip() or line.startswith("#"):
        continue
    path, secs = line.split()
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + float(secs)
    records, started = [], monotonic()
    try:
        ok = prover._check(path.rsplit("/", 1)[-1], And(*parse_smt2_file(path)), records)
        answer = "proved" if ok else records[-1].answer
    except be.ProofBudgetExceeded:
        answer = "budget"
    print(path.rsplit("/", 1)[-1], answer, f"{monotonic() - started:.1f}s", flush=True)
