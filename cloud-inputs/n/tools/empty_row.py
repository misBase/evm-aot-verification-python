"""Is x86 row J of a dump_paths.py directory empty? Production _empty_by_bvabs and _check.

Usage (repo root, PYTHONPATH=.): empty_row.py DUMP_DIR J [J ...] [--save SMT2_DIR]
Prints the empty-row proposal and the `x86_empty_J` _check result (30s per query,
1800s per obligation, like check_obligation.py). --save writes And(premise, x86_J).
"""
import sys
from pathlib import Path
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]
save = Path(argv[argv.index("--save") + 1]) if "--save" in argv else None
argv = [a for n, a in enumerate(argv) if a != "--save" and (n == 0 or argv[n - 1] != "--save")]
d = Path(argv[0])
premise = And(*parse_smt2_file(str(d / "premise.smt2")))
for j in map(int, argv[1:]):
    x = And(*parse_smt2_file(str(d / f"x86_{j}.smt2")))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + 1800
    if save is not None:
        save.mkdir(parents=True, exist_ok=True)
        (save / f"x86_empty_{j}.smt2").write_text(be._to_smt2(And(premise, x)))
    started = monotonic()
    proposal = prover._empty_by_bvabs(premise, type("P", (), {"condition": x})())
    print(f"x86_empty_{j} proposal", proposal, f"{monotonic() - started:.1f}s", flush=True)
    records, started = [], monotonic()
    ok = prover._check(f"x86_empty_{j}", And(premise, x), records)
    print(f"x86_empty_{j}", "proved" if ok else records[-1].answer, f"{monotonic() - started:.1f}s",
          f"lemmas={len(records[-1].lemmas)}", flush=True)
