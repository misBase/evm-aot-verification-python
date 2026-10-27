"""Production _check on a row group: premise ∧ x86_J ∧ ¬(conjuncts of evm_I) (dump_paths.py directory).

Usage (repo root, PYTHONPATH=.): row_group.py DUMPDIR I J [--seconds N] [--first K]
--first K: only the first K conjuncts of evm_I (default all). Diagnostics only.
"""
import sys
from time import monotonic

from z3 import And, Not, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]
d, i, j = argv[0], int(argv[1]), int(argv[2])
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1800
first = int(argv[argv.index("--first") + 1]) if "--first" in argv else None
premise = And(*parse_smt2_file(f"{d}/premise.smt2"))
x = And(*parse_smt2_file(f"{d}/x86_{j}.smt2"))
conj = be._conjuncts(And(*parse_smt2_file(f"{d}/evm_{i}.smt2")))[:first]
if "--ks" in argv:  # only these conjunct indices (e.g. the maps a run left after the groups)
    conj = [conj[int(k)] for k in argv[argv.index("--ks") + 1].split(",") if k]
prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
prover.deadline = monotonic() + seconds
records, started = [], monotonic()
ok = prover._check("x86_maps_group_0", And(premise, x.condition if hasattr(x, "condition") else x, Not(And(*conj))),
                   records)
print(f"row {j} -> evm {i}, {len(conj)} conjuncts: {'proved' if ok else records[-1].answer} "
      f"{monotonic() - started:.1f}s, {len(records[-1].lemmas)} lemmas", flush=True)
