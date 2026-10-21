"""Dump one node's premise, per-path conditions and selected obligations as SMT2, then stop.

Usage (repo root, PYTHONPATH=.): dump_paths.py STEM NODES.json INDEX OUTDIR [--node-seconds N]
    [--pairs I_J,I_J,...] [--names REGEX] [--stop-on-name]

- Stops at the pair phase (before any prefix pass): writes premise.smt2, evm_<i>.smt2,
  x86_<j>.smt2, meta.json (path kinds/locations, the correspondence `_correspondence` found,
  each path's conjunct count) and, for --pairs, pair_<i>_<j>.smt2 exactly as _check_rows
  hands it to _check (forward_selects + canon_binders).
- --names REGEX: every `_check` call whose name matches is also written as <name>.smt2
  (before it is solved); with --stop-on-name the run stops after the first such dump
  (e.g. evm_assumption_7, which fails before the pair phase).
Diagnostics only: nothing here is a proof.
"""
import json
import re
import sys
import time
from pathlib import Path

from z3 import And

import verification.block_equivalence as be
from tools.probe_block_obligations import build_prover, parse_nodes

argv = sys.argv[1:]


def opt(flag, default=None):
    return argv[argv.index(flag) + 1] if flag in argv else default


stem, node_json, index, out = argv[0], argv[1], int(argv[2]), Path(argv[3])
node_seconds = float(opt("--node-seconds", 21600))
pairs = [tuple(map(int, p.split("_"))) for p in opt("--pairs", "").split(",") if p]
names = re.compile(opt("--names")) if opt("--names") else None
stop_on_name = "--stop-on-name" in argv
out.mkdir(parents=True, exist_ok=True)
T0 = time.monotonic()


class Done(Exception):
    pass


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


def pair_phase(self, evm, x86, premise, pair, found, records):
    log("pair phase: evm", len(evm), "x86", len(x86), "found", found)
    (out / "premise.smt2").write_text(be._to_smt2(premise))
    for i, e in enumerate(evm):
        (out / f"evm_{i}.smt2").write_text(be._to_smt2(e.condition))
    for j, x in enumerate(x86):
        (out / f"x86_{j}.smt2").write_text(be._to_smt2(x.condition))
    meta = dict(found=[x if type(x) is int or x is None else str(x) for x in found],
                evm=[dict(kind=e.kind, location=e.location, conjuncts=len(be._conjuncts(e.condition)))
                     for e in evm],
                x86=[dict(kind=x.kind, location=x.location, conjuncts=len(be._conjuncts(x.condition)))
                     for x in x86],
                proposed=[x if type(x) is int or x is None else str(x) for x in be.propose_from_siblings(found, x86)])
    (out / "meta.json").write_text(json.dumps(meta, indent=1))
    forwarded, canon = {}, {}
    for i, j in pairs:
        name, formula, where = pair(i, j)
        formula = be.canon_binders(be.forward_selects(formula, forwarded), canon)
        (out / f"{name}.smt2").write_text(be._to_smt2(formula))
        log("dumped", name, where)
    raise Done()


be.BlockEquivalenceProver._pair_phase = pair_phase
spec = parse_nodes(json.loads(Path(node_json).read_text()))[index]
log("spec", spec)
prover = build_prover(stem, base_addr=0x1000, timeout_ms=30000, node_seconds=node_seconds, max_depth=400,
                      summaries=True)
orig_check = prover._check


def check(name, formula, records, **kw):
    if names is not None and names.search(name):
        (out / f"{name}.smt2").write_text(be._to_smt2(formula))
        log("dumped", name)
        if stop_on_name:
            raise Done()
    t = time.monotonic()
    ok = orig_check(name, formula, records, **kw)
    log("check", name, records[-1].answer, f"{time.monotonic() - t:.1f}s")
    return ok


prover._check = check
result = prover.prove(spec)
log("result", result.status, result.reasons, "evm", result.evm_paths, "x86", result.x86_paths)
