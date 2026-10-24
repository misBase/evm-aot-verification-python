"""Show conjunct K of EVM path I (and the kind/location of x86 row J) of a dump_paths.py directory.

Usage (repo root, PYTHONPATH=.): show_conjunct.py DUMP_DIR EVM_I K [X86_J]
Prints the conjunct simplified, with memory reads and big subterms abbreviated by size.
Diagnostics only.
"""
import json
import sys
from pathlib import Path

from z3 import And, parse_smt2_file, simplify

import verification.block_equivalence as be

d, i, k = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
meta = json.loads((d / "meta.json").read_text())
print("evm", i, meta["evm"][i])
if len(sys.argv) > 4:
    j = int(sys.argv[4])
    print("x86", j, meta["x86"][j], "->", meta["found"][j])
conj = be._conjuncts(And(*parse_smt2_file(str(d / f"evm_{i}.smt2"))))
c = simplify(conj[k])
text = " ".join(c.sexpr().split())
print(f"conjunct {k} of {len(conj)}: {len(text)} chars")
print(text[:3000])
