"""Route trace of the LAST file after the others ran through _check in the same process, each with
a fresh prover (exactly as regress.py runs them), to see what module state left by earlier
obligations changes for the last one.

Usage (repo root, PYTHONPATH=.): trace_after.py OUT.json PREFIX.smt2 ... LAST.smt2 [--seconds N]
Diagnostics only.
"""
import importlib.util
import sys
from pathlib import Path
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1800
argv = [a for n, a in enumerate(argv) if a != "--seconds" and (n == 0 or argv[n - 1] != "--seconds")]
out, *prefix, last = argv
for path in prefix:
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + seconds
    records, started = [], monotonic()
    ok = prover._check(path.rsplit("/", 1)[-1], And(*parse_smt2_file(path)), records)
    print(path.rsplit("/", 1)[-1], "proved" if ok else records[-1].answer, f"{monotonic() - started:.1f}s", flush=True)
spec = importlib.util.spec_from_file_location(
    "route_trace", Path(__file__).resolve().parents[2] / "r3c" / "tools" / "route_trace.py")
rt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rt)
be.BlockEquivalenceProver._check = rt._instrumented_check()
be._refute_over_light_premise = rt._probe("light", be._refute_over_light_premise)
be.unsat_core = rt._probe("unsat_core", be.unsat_core)
be._refute_by_cases = rt._probe("cases", be._refute_by_cases)
rt._run(be.BlockEquivalenceProver([], [], {}, timeout_ms=30000), last, last.rsplit("/", 1)[-1], seconds, out)
