"""One proof instance of the discover-first schedule, in-process: its node proof AND its H2 edges
into the frozen instance set, as a block_parallel worker runs it (diagnostics only).

Usage (repo root, PYTHONPATH=.): h2_triage.py STEM 'BlockSpecialization(...)' OUT.json
    [--node-seconds N] [--memory-mb M]

Options are the server's 3G run (--gas-check full --timeout-ms 30000 --max-depth 400
--max-instances 8192 --max-parameter-values 32 --summaries --discover-first --constant-insensitive).
The frozen set is rediscovered (EVM only); the given proof instance k (or a context's k = π(c)) is proved with
all its contexts, under NodeMonitor. Every _check is logged (name, answer, seconds) with H2 parts.
"""
import json
import sys
import time
from pathlib import Path

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.block_program import BlockProgramResult
from verification.block_specialization import BlockSpecialization  # noqa: F401 (eval of the spec)

argv = sys.argv[1:]
stem, wanted, out = argv[0], eval(argv[1]), Path(argv[2])
node_seconds = float(argv[argv.index("--node-seconds") + 1]) if "--node-seconds" in argv else 3600
memory = float(argv[argv.index("--memory-mb") + 1]) if "--memory-mb" in argv else None
options = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=30000, node_seconds=node_seconds,
               first_pass_node_seconds=300, max_parameter_values=32, max_depth=400, max_instances=8192,
               wall_seconds=10 ** 6, summaries=True, constant_insensitive=True, node_memory_mb=memory)
T0 = time.monotonic()


def log(*a):
    print(f"[{time.monotonic() - T0:8.1f}s]", *a, flush=True)


orig_check = be.BlockEquivalenceProver._check


def check(self, name, formula, records, **kw):
    started = time.monotonic()
    ok = orig_check(self, name, formula, records, **kw)
    log(name, records[-1].answer if records else "-", f"{time.monotonic() - started:.1f}s")
    return ok


be.BlockEquivalenceProver._check = check
evm, x86, initial, verifier = bp.build_inputs(stem, options)
setup = verifier._setup(evm, x86, initial, BlockProgramResult(), time.monotonic(), [])
ordered, defects = bp.discover(verifier, setup, lambda: None)
log("discovered", len(ordered), "instances,", len(defects), "defects")
groups = bp.proof_groups(ordered, setup.evm, True)
k = wanted if wanted in groups else next((k for k, cs in groups.items() if wanted in cs), None)  # instance or context
if k is None:
    raise SystemExit(f"{wanted!r} is not in the frozen set; same pc: "
                     + "; ".join(f"{k!r} <- {list(map(repr, cs))}" for k, cs in groups.items() if k.pc == wanted.pc))
log("proof instance", k, "contexts", len(groups[k]))
bp.load_worker(stem, options, ordered)
node = bp.prove_instance(k, node_seconds, time.time() + 10 ** 6, groups[k])
summary = {key: node[key] for key in ("proved", "status", "reasons", "seconds", "queries", "failed", "pid",
                                      "peak_rss_mb", "memory_exceeded")}
summary.update(spec=repr(k), contexts=[repr(c) for c in groups[k]], edges=len(node["edges"]),
               open_edges=[(e.pair, e.obligation.answer) for e in node["edges"] if not e.obligation.proved])
log("result", summary)
out.write_text(json.dumps(summary, indent=2, default=str))
