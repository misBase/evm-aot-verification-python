"""Rebuild x86_maps_j_k (as _check_rows builds it) from a capture dir: build_maps.py CAPDIR J K[,K..] OUTDIR"""
import json
import sys
from pathlib import Path
from z3 import And, Not, parse_smt2_file
import verification.block_equivalence as be

cap, j, ks, out = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
out.mkdir(parents=True, exist_ok=True)
meta = json.loads((cap / "meta.json").read_text())
target = meta["correspondence"][j]
premise = And(*parse_smt2_file(str(cap / "premise.smt2")))
x = And(*parse_smt2_file(str(cap / f"x86_{j}.smt2")))
e = And(*parse_smt2_file(str(cap / f"evm_{target}.smt2")))
conj = be._conjuncts(e)
ks = range(len(conj)) if ks == "all" else [int(k) for k in ks.split(",")]
forwarded, canon = {}, {}
for k in ks:
    f = And(premise, x, Not(conj[k]))
    f = be.canon_binders(be.forward_selects(f, forwarded), canon)
    (out / f"x86_maps_{j}_{k}.smt2").write_text(be._to_smt2(f))
    print(k, len(conj[k].sexpr()), flush=True)
