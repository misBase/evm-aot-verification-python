"""Run only the unify* route (normalised _retry_with_uf_unification) on goal part K
and log every light-premise probe, unsat_core probe and case tree:
exp_unify.py FILE.smt2 [K] [--light-ms N] [--seconds S]   (repository root, PYTHONPATH=.)

--light-ms overrides be._LIGHT_MS (diagnostic only). The prover gets a deadline of
S seconds (default 1800) for the route, as a promoted route would.
"""
import sys
from time import monotonic

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

LOG = []


def wrap(name, fn):
    def wrapped(*args, **kwargs):
        started = monotonic()
        result = fn(*args, **kwargs)
        extra = ""
        if name == "light":
            extra = f" budget={args[2]}ms parts={len(args[0])}"
        elif name == "core" and len(args) > 3 and isinstance(args[3], dict):
            extra = f" answer={args[3].get('answer')}"
        print(f"  {name}{extra} {monotonic() - started:.2f}s -> {'hit' if result is not None else 'miss'}",
              flush=True)
        return result
    return wrapped


def main():
    sys.setrecursionlimit(100000)
    path = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 2
    if "--light-ms" in sys.argv:
        be._LIGHT_MS = int(sys.argv[sys.argv.index("--light-ms") + 1])
    seconds = float(sys.argv[sys.argv.index("--seconds") + 1]) if "--seconds" in sys.argv else 1800
    be._refute_over_light_premise = wrap("light", be._refute_over_light_premise)
    be.unsat_core = wrap("core", be.unsat_core)
    be._refute_by_cases = wrap("cases", be._refute_by_cases)
    f = And(*parse_smt2_file(path))
    part, _ = be.skolemize_array_disequalities(be._goal_split(f)[k])
    t = monotonic()
    target, rewrites = be.normalize_word_arith(part)
    print(f"normalize {monotonic() - t:.1f}s")
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + seconds
    t = monotonic()
    proved, answer, lemmas = prover._retry_with_uf_unification(target, "unknown")
    print(f"unify*: {answer} {monotonic() - t:.1f}s lemmas={[x.name for x in lemmas]}")


if __name__ == "__main__":
    main()
