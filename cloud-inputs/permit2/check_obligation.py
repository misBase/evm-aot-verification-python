"""Run the production _check of the snapshot in cwd on captured SMT2 obligations: FILE.smt2 ...
(cwd = snapshot, PYTHONPATH=.; 30s per-query budget, 1800s per obligation)"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

for path in sys.argv[1:]:
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + 1800
    records, started = [], monotonic()
    ok = prover._check(path.rsplit("/", 1)[-1], And(*parse_smt2_file(path)), records)
    print(path.rsplit("/", 1)[-1], "proved" if ok else records[-1].answer, f"{monotonic() - started:.1f}s",
          f"lemmas={len(records[-1].lemmas)}", flush=True)
