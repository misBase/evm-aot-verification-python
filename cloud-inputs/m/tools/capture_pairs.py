"""Run prove() on one node up to the pair phase, dump every pair-phase obligation as SMT2, stop.

Usage (repo root, PYTHONPATH=.): capture_pairs.py STEM NODE_JSON OUTDIR [--node-seconds N]
Also writes OUTDIR/meta.json: paths, correspondence, prefix-discharged maps, EVM conjunct texts.
"""
import json
import sys
import time
from pathlib import Path

import verification.block_equivalence as be
from tools.probe_block_obligations import build_prover, parse_nodes

stem, node_json, out = sys.argv[1], sys.argv[2], Path(sys.argv[3])
node_seconds = float(sys.argv[sys.argv.index("--node-seconds") + 1]) if "--node-seconds" in sys.argv else 21600
out.mkdir(parents=True, exist_ok=True)
meta = {"events": []}
T0 = time.monotonic()


class Captured(Exception):
    pass


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


orig_rows = be.BlockEquivalenceProver._check_rows
orig_prefix = be.discharge_maps_by_prefix
orig_stuck = be.BlockEquivalenceProver._prove_stuck_groups
orig_corr = be.BlockEquivalenceProver._correspondence


def corr(self, evm, x86, premise, records):
    log("correspondence start", len(evm), len(x86))
    c = orig_corr(self, evm, x86, premise, records)
    log("correspondence", c)
    meta["correspondence"] = [x if type(x) is int or x is None else str(x) for x in c]
    meta["evm_conjuncts"] = {i: [str(k)[:400] for k in be._conjuncts(e.condition)] for i, e in enumerate(evm)}
    meta["evm_kinds"] = [f"{e.kind}@{e.location}" for e in evm]
    meta["x86_kinds"] = [f"{x.kind}@{x.location}" for x in x86]
    (out / "premise.smt2").write_text(be._to_smt2(premise))
    for i, e in enumerate(evm):
        (out / f"evm_{i}.smt2").write_text(be._to_smt2(e.condition))
    for j, x in enumerate(x86):
        (out / f"x86_{j}.smt2").write_text(be._to_smt2(x.condition))
    return c


def prefix(premise, conds, jobs, timeout_ms, deadline=None, stuck=None):
    t = time.monotonic()
    done = orig_prefix(premise, conds, jobs, timeout_ms, deadline, stuck)
    log("prefix pass", len(done), "discharged of", sum(len(e) for _, e in jobs), "stuck groups", len(stuck or ()),
        f"{time.monotonic() - t:.1f}s")
    meta["prefix_discharged"] = sorted(map(list, done))
    meta["stuck"] = [sorted(map(list, e)) for _, e in (stuck or ())]
    for n, (q, e) in enumerate(stuck or ()):
        (out / f"stuck_{n}.smt2").write_text(be._to_smt2(q))
    return done


def stuckg(self, stuck, done, until, per_group):
    before = set(done)
    t = time.monotonic()
    orig_stuck(self, stuck, done, until, per_group)
    log("stuck groups proved", len(set(done) - before), f"{time.monotonic() - t:.1f}s")
    meta["stuck_proved"] = sorted(map(list, set(done) - before))


def rows(self, evm, x86, premise, pair, correspondence, rws, ready, records, tolerated=()):
    orig_all = self._check_all

    def capture(pairs, recs):
        names = [n for n, _, _ in pairs]
        log("pair phase items", len(names))
        meta["items"] = names
        import os, re
        only = re.compile(os.environ.get("CAPTURE_ONLY", "."))
        for n, f, where in pairs:
            if only.search(n):
                (out / f"{n}.smt2").write_text(be._to_smt2(f))
        meta["where"] = {n: w for n, _, w in pairs}
        (out / "meta.json").write_text(json.dumps(meta, indent=1))
        raise Captured()
        yield  # generator

    self._check_all = capture
    try:
        return orig_rows(self, evm, x86, premise, pair, correspondence, rws, ready, records, tolerated)
    finally:
        del self._check_all


be.BlockEquivalenceProver._correspondence = corr
be.discharge_maps_by_prefix = prefix
be.BlockEquivalenceProver._prove_stuck_groups = stuckg
be.BlockEquivalenceProver._check_rows = rows

spec = parse_nodes(json.loads(Path(node_json).read_text()))[0]
prover = build_prover(stem, base_addr=0x1000, timeout_ms=30000, node_seconds=node_seconds, max_depth=400,
                      summaries=True)
orig_check = prover._check


def check(name, formula, records, **kw):
    t = time.monotonic()
    ok = orig_check(name, formula, records, **kw)
    if time.monotonic() - t > 5 or not ok:
        log("check", name, records[-1].answer, f"{time.monotonic() - t:.1f}s")
    return ok


prover._check = check
result = prover.prove(spec)
log("result", result.status, result.reasons, "evm", result.evm_paths, "x86", result.x86_paths)
(out / "meta.json").write_text(json.dumps(meta, indent=1))
