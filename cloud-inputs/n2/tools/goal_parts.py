"""Split a captured pair obligation into its goal parts as `_check` does, save each part, and show
what each part's goal compares (sides, size, UF applications).

Usage (repo root, PYTHONPATH=.): goal_parts.py PAIR.smt2 OUTDIR [K ...]
Writes OUTDIR/<stem>_goal_<k>_of_<n>.smt2 (after skolemize_array_disequalities, like _check).
Diagnostics only: nothing here is a proof.
"""
import sys
from pathlib import Path

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

path, out = Path(sys.argv[1]), Path(sys.argv[2])
only = {int(k) for k in sys.argv[3:]}
out.mkdir(parents=True, exist_ok=True)
formula, _ = be.skolemize_array_disequalities(And(*parse_smt2_file(str(path))))
parts = be._goal_split(formula)
print("parts", None if parts is None else len(parts), flush=True)
for k, part in enumerate(parts or ()):
    if only and k not in only:
        continue
    goal = part.arg(part.num_args() - 1).arg(0)  # Not(g_k)
    ufs = sorted({a.decl().name() for apps in be._uf_applications(goal) for a in apps})
    print(f"goal {k}: {len(goal.sexpr())} chars, ufs {ufs}", flush=True)
    print("  ", goal.sexpr()[:600].replace("\n", " "), flush=True)
    (out / f"{path.stem}_goal_{k}_of_{len(parts)}.smt2").write_text(be._to_smt2(part))
