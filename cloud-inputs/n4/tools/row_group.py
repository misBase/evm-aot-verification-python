"""Group implication experiment on a dump_paths.py directory (diagnostics only: nothing here is a proof).

Usage (repo root, PYTHONPATH=.): row_group.py DUMP_DIR ROW [ROW ...] [--seconds N] [--size K] [--prefix]
    [--split]

For each x86 row j (its EVM target from meta.json `proposed`), builds
    premise ∧ x_j ∧ ¬(c_a ∧ … ∧ c_b)
over the row's conjuncts (all, or the first --size), forwarded and canonicalised as
_check_rows does, and runs production _check(split=False) on it with --seconds (default 600).
--prefix first runs discharge_maps_by_prefix on the row (3s per group, as _pair_phase) and groups
only what it leaves. --split: also time each left conjunct alone (cap --seconds each).
"""
import json
import sys
import time
from pathlib import Path

from z3 import And, Not, parse_smt2_file

import verification.block_equivalence as be

argv = sys.argv[1:]


def opt(flag, default=None):
    return argv[argv.index(flag) + 1] if flag in argv else default


d = Path(argv[0])
rows = [int(a) for a in argv[1:] if not a.startswith("--") and argv[argv.index(a) - 1] not in ("--seconds", "--size")]
seconds, size = float(opt("--seconds", 600)), opt("--size")
meta = json.loads((d / "meta.json").read_text())
premise = And(*parse_smt2_file(str(d / "premise.smt2")))
T0 = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


for j in rows:
    target = meta["proposed"][j]
    x = And(*parse_smt2_file(str(d / f"x86_{j}.smt2")))
    conj = be._conjuncts(And(*parse_smt2_file(str(d / f"evm_{target}.smt2"))))
    left = list(range(len(conj)))
    if "--prefix" in argv:
        started = time.monotonic()
        done = be.discharge_maps_by_prefix(premise, {j: x}, [(c, [(j, k)]) for k, c in enumerate(conj)], 3000)
        left = [k for k in left if (j, k) not in done]
        log(f"row {j} -> evm {target}: prefix pass {len(done)} of {len(conj)} in {time.monotonic() - started:.1f}s")
    if size is not None:
        left = left[:int(size)]
    forwarded, canon = {}, {}
    query = be.canon_binders(be.forward_selects(And(premise, x, Not(And(*(conj[k] for k in left)))), forwarded),
                             canon)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = time.monotonic() + seconds
    records, started = [], time.monotonic()
    try:
        ok = prover._check(f"x86_maps_{j}_group", query, records, split=False)
        answer = "proved" if ok else records[-1].answer
    except be.ProofBudgetExceeded:
        answer = "budget"
    stats = {f"{r}{'+n' if n else ''}": (w, round(t, 1)) for c in prover._route_stats.values() for (r, n), (w, t) in c.items()}
    log(f"row {j} -> evm {target}: group of {len(left)} conjuncts {answer} {time.monotonic() - started:.1f}s routes {stats}")
    if "--split" in argv:
        for k in left:
            prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
            prover.deadline = time.monotonic() + seconds
            q = be.canon_binders(be.forward_selects(And(premise, x, Not(conj[k])), forwarded), canon)
            records, started = [], time.monotonic()
            try:
                answer = "proved" if prover._check(f"x86_maps_{j}_{k}", q, records) else records[-1].answer
            except be.ProofBudgetExceeded:
                answer = "budget"
            log(f"   x86_maps_{j}_{k} {answer} {time.monotonic() - started:.1f}s")
