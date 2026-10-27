"""cloud-inputs/n/tools/regress.py (production _check, fresh prover per file) plus a log line for
each route attempt (_check's route methods wrapped; arguments and results pass through).

Usage (repo root, PYTHONPATH=.): regress_traced.py FILE.smt2 ... [--seconds N]
Diagnostics only.
"""
import sys
import time
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

T0 = time.monotonic()
P = be.BlockEquivalenceProver


def wrap(name):
    orig = getattr(P, name)

    def run(self, *a, **k):
        started = time.monotonic()
        out = orig(self, *a, **k)
        answer = out[1] if isinstance(out, tuple) and len(out) > 1 else out
        print(f"[{time.monotonic() - T0:8.1f}s]   {name} -> {answer} {time.monotonic() - started:.1f}s", flush=True)
        return out
    setattr(P, name, run)


for n in ("_retry_over_lia", "_retry_over_potential", "_retry_over_nonlinear_mul", "_retry_with_uf_unification",
          "_retry_over_guard_cases", "_unify_and_split"):
    wrap(n)

argv = sys.argv[1:]
seconds = float(argv[argv.index("--seconds") + 1]) if "--seconds" in argv else 1800
paths = [a for n, a in enumerate(argv) if a != "--seconds" and (n == 0 or argv[n - 1] != "--seconds")]
for path in paths:
    name = path.rsplit("/", 1)[-1].rsplit(".", 1)[0]
    expected = "sat" if "nonempty" in name else "unsat"
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + seconds
    records, started = [], monotonic()
    try:
        ok = prover._check(name, And(*parse_smt2_file(path)), records, expected=expected)
        answer = ("proved" if ok else records[-1].answer)
        lemmas = len(records[-1].lemmas)
        names = sorted({r.name.split("_case")[0][:24] for r in records[-1].lemmas})[:12]
    except be.ProofBudgetExceeded:
        answer, lemmas, names = "budget", 0, []
    for part in (records[-1].lemmas if records else ()):
        print(f"   part {part.name} {part.answer} {part.elapsed_seconds or 0:.1f}s lemmas={[r.name for r in part.lemmas][:8]}", flush=True)
    print(f"{name} expected={expected} {answer} {monotonic() - started:.1f}s lemmas={lemmas} {names}", flush=True)
