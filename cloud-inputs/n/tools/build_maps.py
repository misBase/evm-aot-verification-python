"""Rebuild x86_maps_J_K as _check_rows builds it, from a dump_paths.py directory.

Usage (repo root, PYTHONPATH=.): build_maps.py DUMP_DIR EVM_I X86_J K[,K..]|all OUTDIR
(EVM_I is the row's target EVM path: the `where` text of the obligation names it.)
"""
import sys
from pathlib import Path

from z3 import And, Not, parse_smt2_file

import verification.block_equivalence as be

d, i, j, ks, out = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], Path(sys.argv[5])
out.mkdir(parents=True, exist_ok=True)
premise = And(*parse_smt2_file(str(d / "premise.smt2")))
x = And(*parse_smt2_file(str(d / f"x86_{j}.smt2")))
conj = be._conjuncts(And(*parse_smt2_file(str(d / f"evm_{i}.smt2"))))
ks = range(len(conj)) if ks == "all" else [int(k) for k in ks.split(",")]
forwarded, canon = {}, {}
for k in ks:
    f = be.canon_binders(be.forward_selects(And(premise, x, Not(conj[k])), forwarded), canon)
    (out / f"x86_maps_{j}_{k}.smt2").write_text(be._to_smt2(f))
    print(k, len(conj[k].sexpr()), flush=True)
