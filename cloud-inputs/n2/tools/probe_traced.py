"""tools/probe_block_obligations.py, unchanged, plus a log line for every _check (name, answer, seconds)
and for the pair phase / _unify_node. The probe's own JSON output is the result; the log only says
where the time went.

Usage (repo root, PYTHONPATH=.): probe_traced.py <probe_block_obligations.py arguments>
Diagnostics only: logging wraps the methods and passes every argument and result through.
"""
import sys
import time

import verification.block_equivalence as be
from tools import probe_block_obligations

T0 = time.monotonic()
Prover = be.BlockEquivalenceProver
orig_check, orig_phase, orig_unify = Prover._check, Prover._pair_phase, Prover._unify_node


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


def check(self, name, formula, records, **kw):
    started = time.monotonic()
    ok = orig_check(self, name, formula, records, **kw)
    log(name, records[-1].answer if records else "-", f"{time.monotonic() - started:.1f}s")
    return ok


def pair_phase(self, evm, x86, premise, pair, found, records):
    log("pair phase: evm", len(evm), "x86", len(x86), "found",
        [x if type(x) is int or x is None else str(x) for x in found])
    return orig_phase(self, evm, x86, premise, pair, found, records)


def unify_node(self, pairs, skip=frozenset()):
    started = time.monotonic()
    out = orig_unify(self, pairs, skip)
    log(f"_unify_node over {len(pairs)} obligations: {time.monotonic() - started:.1f}s, "
        f"{len(out[1])} lemmas")
    return out


Prover._check, Prover._pair_phase, Prover._unify_node = check, pair_phase, unify_node
raise SystemExit(probe_block_obligations.main(sys.argv[1:]))
