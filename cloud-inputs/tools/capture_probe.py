"""probe_block_obligations.main, plus: every formula named with a $CAPTURE_PREFIX prefix (default x86_maps) reaching _check is saved as SMT2
(with declarations) under $CAPTURE_DIR, and its answer appended to $CAPTURE_DIR/answers.txt."""
import os
import sys
from hashlib import sha256
from pathlib import Path
from time import monotonic

from z3 import Solver

import verification.block_equivalence as be
from tools.probe_block_obligations import main

OUT = Path(os.environ["CAPTURE_DIR"])
OUT.mkdir(parents=True, exist_ok=True)
orig = be.BlockEquivalenceProver._check


def _check(self, name, formula, records, **kw):
    if name.startswith(tuple(os.environ.get("CAPTURE_PREFIX", "x86_maps").split(","))) and "_goal_" not in name:
        s = Solver()
        s.add(formula)
        text = s.to_smt2()
        path = OUT / f"{name}_{sha256(text.encode()).hexdigest()[:12]}.smt2"
        path.write_text(text)
        t = monotonic()
        ok = orig(self, name, formula, records, **kw)
        with open(OUT / "answers.txt", "a") as h:
            h.write(f"{name} {records[-1].answer} {monotonic() - t:.1f}s {path.name}\n")
        return ok
    return orig(self, name, formula, records, **kw)


be.BlockEquivalenceProver._check = _check
if __name__ == "__main__":
    sys.exit(main())
