"""Run one node like probe_block_obligations.py (keep-going) and log every _check: name, answer, seconds.

Usage (repo root, PYTHONPATH=.): trace_node.py STEM NODES.json INDEX [--node-seconds N] [--save REGEX OUTDIR]
--save writes the SMT2 of every checked obligation whose name matches REGEX (before solving).
Diagnostics only.
"""
import json
import re
import sys
import time
from pathlib import Path

import verification.block_equivalence as be
from tools.probe_block_obligations import build_prover, parse_nodes

argv = sys.argv[1:]
stem, node_json, index = argv[0], argv[1], int(argv[2])
seconds = float(argv[argv.index("--node-seconds") + 1]) if "--node-seconds" in argv else 3600
save = (re.compile(argv[argv.index("--save") + 1]), Path(argv[argv.index("--save") + 2])) if "--save" in argv else None
T0 = time.monotonic()
spec = parse_nodes(json.loads(Path(node_json).read_text()))[index]
print("spec", spec, flush=True)
prover = build_prover(stem, base_addr=0x1000, timeout_ms=30000, node_seconds=seconds, max_depth=400,
                      summaries=True, keep_going=True)
orig_check = prover._check


def check(name, formula, records, **kw):
    if save is not None and save[0].search(name):
        save[1].mkdir(parents=True, exist_ok=True)
        (save[1] / f"{name}.smt2").write_text(be._to_smt2(formula))
    started = time.monotonic()
    ok = orig_check(name, formula, records, **kw)
    print(f"[{time.monotonic() - T0:8.1f}s] {name} {records[-1].answer} {time.monotonic() - started:.1f}s", flush=True)
    return ok


prover._check = check
orig_phase = prover._pair_phase


def pair_phase(evm, x86, premise, pair, found, records):
    print(f"[{time.monotonic() - T0:8.1f}s] pair phase: evm {len(evm)} x86 {len(x86)} found {found}", flush=True)
    return orig_phase(evm, x86, premise, pair, found, records)


prover._pair_phase = pair_phase
orig_unify_node, orig_prove_equal = prover._unify_node, be._prove_equal
equal_stats = {"proved": 0, "failed": 0, "seconds": 0.0}


def prove_equal(*a, **k):
    started = time.monotonic()
    proofs = orig_prove_equal(*a, **k)
    equal_stats["proved" if proofs is not None else "failed"] += 1
    equal_stats["seconds"] += time.monotonic() - started
    return proofs


def unify_node(pairs, skip=frozenset()):
    started, before = time.monotonic(), dict(equal_stats)
    out = orig_unify_node(pairs, skip)
    print(f"[{time.monotonic() - T0:8.1f}s] _unify_node over {len(pairs)} obligations: "
          f"{time.monotonic() - started:.1f}s, {len(out[1])} lemmas, {len(out[2])} rewritten, _prove_equal "
          f"{ {k: round(v - before[k], 1) for k, v in equal_stats.items()} }", flush=True)
    return out


be._prove_equal = prove_equal
prover._unify_node = unify_node
result = prover.prove(spec)
print(f"[{time.monotonic() - T0:8.1f}s] result", result.status, result.reasons, "queries", result.queries,
      "kept", [(f["name"], f["answer"], round(f["seconds"])) for f in getattr(result, "kept_failures", ())], flush=True)
