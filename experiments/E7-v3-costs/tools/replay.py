"""Replay proof groups of one contract in this process, with production options.

  replay.py STEM OUT.json --pick PC:DEPTH[:M:F] [--pick ...] [--chain] [--trace FILE]
            [--node-seconds 7200] [--ordered CACHE.pkl]

Discovery runs once (cached in --ordered). Each pick selects the constant-
insensitive proof group whose spec has that pc/depth (and memory_size/fmp,
"None" for unknown); picks run in order in the same worker state, so a later
pick sees what earlier ones cached (that is the point of the depth-reuse test).
Scope: local theorem + H2 of the group only, never a program certificate.
"""
import argparse
import json
import pickle
import time
from pathlib import Path


def options(a):
    return dict(gas_check="full", num_inputs=0, gas_budget=1_000_000_000, timeout_ms=30000,
                node_seconds=a.node_seconds, first_pass_node_seconds=300, max_parameter_values=32, max_depth=400,
                max_instances=8192, wall_seconds=a.node_seconds * 4, hard_wall_seconds=a.node_seconds * 4,
                summaries=True, fallback="none", discover_first=True, node_workers=1, pair_workers_per_node=1,
                results_dir=None, node_memory_mb=None, status_dir=None, constant_insensitive=True,
                pushed_code_return_tags=False, terminal_constant_projection=False,
                context_constant_projection=False, instruction_hints=a.trace)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("stem")
    p.add_argument("out")
    p.add_argument("--pick", action="append", default=[])  # none: discovery cache only
    p.add_argument("--chain", action="store_true")
    p.add_argument("--trace")
    p.add_argument("--node-seconds", type=float, default=7200)
    p.add_argument("--ordered")
    a = p.parse_args()
    import os
    os.environ.setdefault("BLOCK_PAIR_WORKERS", "1")
    from verification import block_parallel as bp
    opts = options(a)
    cache = Path(a.ordered) if a.ordered else None
    t0 = time.monotonic()
    if cache and cache.exists():
        ordered = pickle.loads(cache.read_bytes())
    else:
        from verification.block_program import BlockProgramResult
        evm, x86, initial, verifier = bp.build_inputs(a.stem, opts)
        setup = verifier._setup(evm, x86, initial, BlockProgramResult(), time.monotonic(), [])
        ordered, defects = bp.discover(verifier, setup, lambda: None)
        assert not defects, defects[:3]
        if cache:
            cache.write_bytes(pickle.dumps(ordered))
    discovery_s = time.monotonic() - t0
    if not a.pick:
        return
    bp.load_worker(a.stem, opts, ordered)
    groups = bp.proof_groups(ordered, bp._WORKER["setup"].evm, True)
    load_s = time.monotonic() - t0 - discovery_s
    rows = []
    for pick in a.pick:
        if pick.startswith("BlockSpecialization("):  # an exact proof-instance repr (sample.py)
            match = [k for k in groups if repr(k) == pick]
        else:
            parts = pick.split(":")
            want = (int(parts[0]), int(parts[1])) + tuple(None if x == "None" else int(x) for x in parts[2:4])
            match = [k for k in groups if (k.pc, k.stack_depth) == want[:2]
                     and (len(want) == 2 or (k.memory_size, k.free_memory_pointer) == want[2:])]
        assert len(match) == 1, (pick, [repr(k) for k in match])
        spec, contexts = match[0], groups[match[0]]
        started = time.monotonic()
        r = bp.prove_instance(spec, a.node_seconds, time.time() + a.node_seconds, contexts, a.chain)
        rows.append(dict(pick=pick, spec=repr(spec), contexts=len(contexts), chain=a.chain,
                         wall=round(time.monotonic() - started, 2), proved=bool(r["proved"]),
                         closed=bool(r["proved"] and not r["reasons"]), proof_kind=r.get("proof_kind"),
                         chain_attempt=r.get("chain_attempt"), seconds=r["seconds"], queries=r["queries"],
                         reasons=[str(x)[:300] for x in r["reasons"]], failed=r.get("failed", [])[:20]))
        Path(a.out).write_text(json.dumps(dict(stem=a.stem, discovery_s=discovery_s, load_s=load_s,
                                               ordered=len(ordered), groups=len(groups), rows=rows), indent=1))
        print(json.dumps(rows[-1])[:400], flush=True)


if __name__ == "__main__":
    main()
