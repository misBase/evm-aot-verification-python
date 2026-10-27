"""Prefix scan of a joint path query (dump_paths.py output): premise ∧ evm_I ∧ x86_J[:n].

Usage (repo root, PYTHONPATH=.): prefix_scan.py DUMPDIR I J [--ms N] [--step K]
For n = 0, K, 2K, ... (and the full length) prints the answer of the direct query and of the
blast_select_store form (each --ms, default 10000), so one sees where the joint becomes UNSAT
(or where it stops being decided). Diagnostics only.
"""
import sys
import time

from z3 import And, BoolVal, is_and, parse_smt2_file, simplify

import verification.block_equivalence as be

argv = sys.argv[1:]
d, i, j = argv[0], int(argv[1]), int(argv[2])
ms = int(argv[argv.index("--ms") + 1]) if "--ms" in argv else 10000
step = int(argv[argv.index("--step") + 1]) if "--step" in argv else 10
premise = And(*parse_smt2_file(f"{d}/premise.smt2"))
evm = And(*parse_smt2_file(f"{d}/evm_{i}.smt2"))
x = And(*parse_smt2_file(f"{d}/x86_{j}.smt2"))
xs = be._conjuncts(x)
print(f"x86_{j}: {len(xs)} conjuncts", flush=True)
for n in sorted(set(range(0, len(xs), step)) | {len(xs)}):
    q = And(premise, evm, *xs[:n]) if n else And(premise, evm)
    t = time.monotonic()
    direct = be.solve_query(simplify(q), ms)
    t1 = time.monotonic() - t
    t = time.monotonic()
    blasted = be.solve_query(simplify(q, blast_select_store=True), ms)
    print(f"n={n:4d}: direct {direct} {t1:.1f}s | blasted {blasted} {time.monotonic() - t:.1f}s", flush=True)
