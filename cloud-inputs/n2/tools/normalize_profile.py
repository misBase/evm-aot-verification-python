"""Where normalize_word_arith spends its time on sibling obligations, and how many of its identity
proofs repeat across them (in one process, as in a node).

Usage (repo root, PYTHONPATH=.): normalize_profile.py FILE.smt2 [FILE.smt2 ...] [--plain]
--plain: no per-call wrapper (its sexpr keys cost time); totals only.
For each file in order: total seconds, _identity_proof calls / seconds, and how many of those
(old, new) pairs were already seen for an earlier file. Diagnostics only.
"""
import sys
import time

from z3 import And, parse_smt2_file

import verification.block_equivalence as be

seen, stats = set(), {}
orig = be._identity_proof


def timed(old, new, *a, **k):
    started = time.monotonic()
    out = orig(old, new, *a, **k)
    key = (old.sexpr(), new.sexpr())
    stats["calls"] += 1
    stats["seconds"] += time.monotonic() - started
    stats["repeat"] += key in seen
    stats["repeat_seconds"] += (time.monotonic() - started) if key in seen else 0.0
    seen.add(key)
    return out


if "--plain" not in sys.argv:
    be._identity_proof = timed
for path in [a for a in sys.argv[1:] if a != "--plain"]:
    stats.update(calls=0, seconds=0.0, repeat=0, repeat_seconds=0.0)
    formula = And(*parse_smt2_file(path))
    formula, _ = be.skolemize_array_disequalities(formula)
    started = time.monotonic()
    _, lemmas = be.normalize_word_arith(formula)
    total = time.monotonic() - started
    print(f"{path.rsplit('/', 1)[-1]}: {total:.1f}s, {len(lemmas)} lemmas, identity proofs {stats['calls']} "
          f"in {stats['seconds']:.1f}s, already seen {stats['repeat']} ({stats['repeat_seconds']:.1f}s)", flush=True)
