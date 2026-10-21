"""Production _check on captured SMT2 obligations, one fresh prover each (30s per query,
--seconds per obligation, default 1800). Names containing "nonempty" are expected SAT.

Usage (repo root, PYTHONPATH=.): regress.py FILE.smt2 ... [--seconds N]
"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1800
paths = [a for n, a in enumerate(argv) if a != "--seconds" and (n == 0 or argv[n - 1] != "--seconds")]
for path in paths:
    name = path.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    expected = "sat" if "nonempty" in name else "unsat"
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + seconds
    records, started = [], monotonic()
    try:
        ok = prover._check(name, And(*parse_smt2_file(path)), records, expected=expected)
        answer = ("proved" if ok else records[-1].answer)
        lemmas = len(records[-1].lemmas)
    except be.ProofBudgetExceeded:
        answer, lemmas = "budget", 0
    print(f"{name} expected={expected} {answer} {monotonic() - started:.1f}s lemmas={lemmas}", flush=True)
