"""Which x86 path conditions of a dump_paths.py directory carry a merged diamond (fix 18):
a top-level conjunct that is an Or (P ∧ (T_a ∨ T_b)). Diagnostics only.

Usage (repo root, PYTHONPATH=.): merged_conjuncts.py DUMP_DIR [ROW ...]
"""
import json
import sys
from pathlib import Path

from z3 import And, is_or, parse_smt2_file

import verification.block_equivalence as be

d = Path(sys.argv[1])
meta = json.loads((d / "meta.json").read_text())
rows = [int(a) for a in sys.argv[2:]] or range(len(meta["x86"]))
for j in rows:
    x = And(*parse_smt2_file(str(d / f"x86_{j}.smt2")))
    conjuncts = be._conjuncts(x)  # flattened (the SMT2 round trip nests the top-level And)
    merged = [k for k, c in enumerate(conjuncts) if is_or(c)]
    print(j, meta["x86"][j], "->", meta["found"][j], "conjuncts", len(conjuncts), "merged at", merged, flush=True)
