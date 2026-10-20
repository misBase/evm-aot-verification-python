"""Diagnostics only: reproduce the H2 edge closure of one proof instance.

Usage (repo root, PYTHONPATH=.): h2_probe.py STEM PC DEPTH CONSTS OUTDIR [--h2-seconds N] [--skip-pairs]
CONSTS: "" (symbolic) or "0:0,3:5". Discovery as verify_parallel (constant-insensitive groups), then
prove_instance with close_edge instrumented (every screen query / part logged with its time).
--skip-pairs: the node's pair phase is skipped (H2 does not read its records); NOT a proof.
"""
import json
import pickle
import sys
import time
from pathlib import Path

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.block_specialization import BlockSpecialization

stem, pc, depth, consts, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], Path(sys.argv[5])
h2_seconds = float(sys.argv[sys.argv.index("--h2-seconds") + 1]) if "--h2-seconds" in sys.argv else 21600
skip_pairs = "--skip-pairs" in sys.argv
out.mkdir(parents=True, exist_ok=True)
T0 = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


options = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=30000, node_seconds=h2_seconds,
               first_pass_node_seconds=300, max_parameter_values=32, max_depth=400, max_instances=8192,
               wall_seconds=10 ** 7, summaries=True, fallback="none", constant_insensitive=True,
               pushed_code_return_tags=False, terminal_constant_projection=False, context_constant_projection=False)
constants = tuple(tuple(int(v) for v in c.split(":")) for c in consts.split(",") if c)
spec = BlockSpecialization(pc, depth, None, None, constants)

cache = out / "discovery.pkl"
evm, x86, initial, verifier = bp.build_inputs(stem, options)
result = bp.BlockProgramResult()
setup = verifier._setup(evm, x86, initial, result, time.monotonic(), [])
if cache.exists():
    ordered = pickle.loads(cache.read_bytes())
else:
    ordered, defects = bp.discover(verifier, setup, lambda: None)
    cache.write_bytes(pickle.dumps(ordered))
    log("discovered", len(ordered), "defects", len(defects))
groups = bp.proof_groups(ordered, setup.evm, True)
contexts = groups.get(spec)
log("proof instance", spec, "contexts", contexts)
if contexts is None:
    log("not a proof instance; instances at pc:", [k for k in groups if k.pc == pc])
    raise SystemExit(1)
log("targets at successors:", {s.pc for s in ordered if s.pc != pc} and None)

bp.load_worker(stem, options, ordered)
prover = bp._WORKER["setup"].prover

if skip_pairs:
    be.BlockEquivalenceProver._pair_phase = lambda self, evm, x86, premise, pair, found, records: tuple(found)
    be.BlockProofResult.proved = property(lambda self: self.theorem is not None)

# ---- instrumentation
orig_solve = be.solve_query
STAT = {}


def solve(formula, timeout_ms, trust_unknown=True):
    t = time.monotonic()
    a = orig_solve(formula, timeout_ms, trust_unknown)
    caller = sys._getframe(1).f_code.co_name
    s = STAT.setdefault(caller, [0, 0.0])
    s[0] += 1
    s[1] += time.monotonic() - t
    if caller in ("close_edge", "independent_model") and time.monotonic() - t > 1:
        log(f"  solve<{caller}> {a} {time.monotonic() - t:.1f}s")
    return a


be.solve_query = solve
orig_check = prover._check
PARTS = []


def check(name, formula, records, **kw):
    import os, re
    save = os.environ.get("H2_SAVE")
    if save and name.startswith("H2_"):
        if re.search(save, name):
            (out / f"{name}.smt2").write_text(be._to_smt2(formula))
            log("saved", name)
        records.append(be.Obligation(name, "", "unsat"))  # diagnostics: no solving
        return True
    t = time.monotonic()
    ok = orig_check(name, formula, records, **kw)
    dt = time.monotonic() - t
    if name.startswith("H2_"):
        PARTS.append(dict(name=name, answer=records[-1].answer, seconds=round(dt, 1), size=len(formula.sexpr())))
        log("part", name, records[-1].answer, f"{dt:.1f}s")
        (out / "parts.json").write_text(json.dumps(PARTS, indent=1))
        if not ok:
            (out / f"{name}.smt2").write_text(be._to_smt2(formula))
    elif dt > 30 or not ok:
        log("check", name, records[-1].answer, f"{dt:.1f}s")
    return ok


prover._check = check
orig_close = bp.close_edge


DIGESTS = {}


def close(prover_, name, base, goals, shared=None):
    log("close_edge", name, "targets", len(goals), [s for s, _ in goals])
    from hashlib import sha256
    if "--digests" not in sys.argv and "--digests-only" not in sys.argv:
        t = time.monotonic()
        r = orig_close(prover_, name, base, goals, shared)
        log("close_edge", name, r.answer, f"{time.monotonic() - t:.1f}s")
        return r
    DIGESTS[name] = dict(
        base=[sha256(c.sexpr().encode()).hexdigest()[:12] for c in be._conjuncts(base)],
        goals={f"t{t}_{g.name}_{k}": sha256(c.sexpr().encode()).hexdigest()[:12]
               for t, (_, rel) in enumerate(goals) for g in rel for k, c in enumerate(be._conjuncts(g.condition))})
    (out / "digests.json").write_text(json.dumps(DIGESTS, indent=1))
    if "--digests-only" in sys.argv:
        return be.Obligation(name, "", "unknown")
    (out / f"{name}_base.smt2").write_text(be._to_smt2(base))
    t = time.monotonic()
    try:
        r = orig_close(prover_, name, base, goals, shared)
    except BaseException as exc:
        log("close_edge", name, "raised", type(exc).__name__, exc, f"{time.monotonic() - t:.1f}s", STAT)
        raise
    log("close_edge", name, r.answer, f"{time.monotonic() - t:.1f}s", STAT)
    return r


bp.close_edge = close
node = bp.prove_instance(spec, h2_seconds, time.time() + 10 ** 7, contexts)
log("done", node["proved"], node["status"], node["reasons"], f"{node['seconds']:.1f}s")
(out / "result.json").write_text(json.dumps(dict(reasons=node["reasons"], status=node["status"],
                                                 seconds=node["seconds"], parts=PARTS, stat=STAT), indent=1))
