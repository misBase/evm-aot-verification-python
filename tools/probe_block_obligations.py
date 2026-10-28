"""Directed block-local proof runner. LOCAL EVIDENCE ONLY — never a program certificate.

Usage: PYTHONPATH=. poetry run python tools/probe_block_obligations.py STEM NODES.json \
           --output /tmp/probe.json [--timeout-ms 5000] [--node-seconds 30] [--formula-dir DIR] \
           [--keep-going]

NODES.json is a JSON list of {"pc": int, "stack_depth": int, "memory_size": int|null,
"free_memory_pointer": int|null, "stack_constants": [[index, value], ...]}. null
memory_size/free_memory_pointer stay symbolic; an absent/empty stack_constants keeps the
stack unconstrained. Nodes are batched through ONE prover so summary templates are
discovered once; every application still replays and proves its own obligations.

Gas is symbolic FULL, the CALLDATALOAD offset domain is the full uint64 range, and the
authoritative pc->addr mapping is used unpruned: no inferred or narrowed jump domain.

--keep-going (or BLOCK_KEEP_GOING=1): a failing pair-phase obligation no longer stops
the node; every remaining row is still tried and the node is still reported
inconclusive. keep_going_failures lists each such failure (name, answer, seconds).
Off by default; the production verifier never enables it.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict
from datetime import datetime, timezone
from hashlib import sha256
import json
import math
import os
from pathlib import Path
import time

BANNER = ("LOCAL ONLY: block-local theorems under the declared entry relation. No program "
          "certificate is issued here; proved counts never mean the program is verified, and "
          "nodes absent from this batch are not unreachable.")

_KEYS = {"pc", "stack_depth", "memory_size", "free_memory_pointer", "stack_constants"}


def parse_nodes(raw):
    """Reject malformed input outright; BlockSpecialization enforces the value ranges."""
    from verification.block_specialization import BlockSpecialization

    if not isinstance(raw, list) or not raw:
        raise ValueError("node file must be a non-empty JSON list")
    specs = []
    for i, item in enumerate(raw):
        if not isinstance(item, dict) or not set(item) <= _KEYS or not {"pc", "stack_depth"} <= set(item):
            raise ValueError(f"node {i}: keys must include pc/stack_depth and stay within {sorted(_KEYS)}")
        for name in ("pc", "stack_depth"):
            if type(item[name]) is not int:
                raise ValueError(f"node {i}: {name} must be an integer")
        for name in ("memory_size", "free_memory_pointer"):
            if item.get(name) is not None and type(item[name]) is not int:
                raise ValueError(f"node {i}: {name} must be an integer or null (stays symbolic)")
        constants = item.get("stack_constants", [])
        if not isinstance(constants, list) or any(
                not isinstance(c, (list, tuple)) or len(c) != 2
                or any(type(v) is not int for v in c) for c in constants):
            raise ValueError(f"node {i}: stack_constants must be a list of [index, value] pairs")
        try:
            specs.append(BlockSpecialization(
                item["pc"], item["stack_depth"], item.get("memory_size"),
                item.get("free_memory_pointer"), tuple(tuple(c) for c in constants)))
        except ValueError as exc:
            raise ValueError(f"node {i}: {exc}") from exc
    return specs


def build_prover(stem, *, base_addr, timeout_ms, node_seconds, max_depth, summaries, keep_going=False):
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from tools.tag_align import build_block_alignment
    from verification.block_equivalence import BlockEquivalenceProver
    from verification.block_partition import split_at_cutpoints
    from x86_64.cfg import identify_basic_blocks
    from x86_64.program import X86Program
    from x86_64.summaries import X86SummaryConfig

    blocks = sorted(EVMProgram(load_ir_from_json(stem + ".json")).blocks, key=lambda b: b.pc)
    x86 = X86Program.from_hex(Path(stem + ".hex").read_text().strip(), base_addr=base_addr)
    basic_blocks = identify_basic_blocks(x86.instructions)
    alignment = build_block_alignment(blocks, x86.instructions, basic_blocks)
    config = X86SummaryConfig.enabled(calldataload="fallback", copy_loop="fallback",
                                      mul="fallback", div="fallback", memgas="fallback") if summaries else None
    return BlockEquivalenceProver(
        blocks, split_at_cutpoints(basic_blocks, alignment.pc_to_addr.values()),
        alignment.pc_to_addr, timeout_ms=timeout_ms, max_depth=max_depth, compare_gas=True,
        host_gas_uf_enabled=True, summary_config=config, node_timeout_seconds=node_seconds,
        keep_going=keep_going)


def probe_node(prover, spec, formula_dir=None, memory_budget=None):
    """One node's report. Under a NodeMonitor (common/node_monitor): pid, start / end
    time and RSS are recorded; over `memory_budget` bytes the node stops at its next
    solver call and is reported inconclusive (the remaining nodes still run)."""
    from common.node_monitor import NodeMemoryExceeded, NodeMonitor, release_memory
    from verification.block_parallel import forget_summary_failures, reset_node_caches
    started = time.monotonic()
    with NodeMonitor(repr(spec), memory_budget) as monitor:
        try:
            result = prover.prove(spec)
        except NodeMemoryExceeded as exc:
            return dict(spec=asdict(spec), scope="block-local", status="inconclusive",
                        seconds=time.monotonic() - started, wall_seconds=time.monotonic() - started,
                        reasons=[str(exc)], failed_obligations=[], keep_going_failures=[], summary_hits=0,
                        **monitor_info(monitor, forget_summary_failures, reset_node_caches, release_memory,
                                       prover))
    failed = []
    for obligation in result.obligations:
        if obligation.proved:
            continue
        record = dict(name=obligation.name, answer=obligation.answer,
                      expected=obligation.expected, seconds=obligation.elapsed_seconds)
        if formula_dir is not None:
            key = sha256(obligation.formula.encode()).hexdigest()[:16]
            path = formula_dir / f"pc{spec.pc}_d{spec.stack_depth}_{obligation.name}_{key}.sexpr"
            path.write_text(obligation.formula + "\n")
            record["formula_file"] = str(path)
        failed.append(record)
    return dict(spec=asdict(spec), scope="block-local", status="proved" if result.proved else "inconclusive",
                seconds=result.elapsed_seconds, wall_seconds=time.monotonic() - started,
                queries=result.queries, evm_paths=result.evm_paths, x86_paths=result.x86_paths,
                paired_transitions=result.paired_transitions, terminals_proved=result.terminals_proved,
                reasons=list(result.reasons), failed_obligations=failed,
                keep_going_failures=[dict(name=f["name"], answer=f["answer"], seconds=f["seconds"],
                                          where=f["where"])
                                     for f in getattr(result, "kept_failures", ())],
                summary_hits=len(result.theorem.summary_hits) if result.theorem else 0,
                **{k: v for k, v in monitor.info().items() if k not in ("finished_at", "end_rss_mb")})


def monitor_info(monitor, forget_summary_failures, reset_node_caches, release_memory, prover):
    # An over-budget node: drop what it left behind before the next one.
    forget_summary_failures()
    reset_node_caches(prover)
    release_memory()
    return {k: v for k, v in monitor.info().items() if k not in ("finished_at", "end_rss_mb")}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("stem", help="Program path without the .json/.hex extension")
    p.add_argument("nodes", type=Path, help="JSON list of node specifications")
    p.add_argument("--output", type=Path, required=True, help="Checkpoint written after every node")
    p.add_argument("--timeout-ms", type=int, default=5000, help="Per-SMT-query budget")
    p.add_argument("--node-seconds", type=float, default=30, help="Per-node soft budget")
    p.add_argument("--max-depth", type=int, default=400)
    p.add_argument("--base-addr", type=lambda v: int(v, 0), default=0x1000)
    p.add_argument("--no-summaries", dest="summaries", action="store_false")
    p.add_argument("--formula-dir", type=Path, help="Dump each failed obligation's formula here")
    p.add_argument("--node-memory-mb", type=float, default=None,
                   help="Per-node RSS budget: a node over it is stopped and reported inconclusive (common/node_monitor)")
    p.add_argument("--keep-going", action="store_true",
                   default=os.environ.get("BLOCK_KEEP_GOING", "") not in ("", "0"),
                   help="Diagnostics: try every pair-phase row after a failure (default: BLOCK_KEEP_GOING)")
    args = p.parse_args(argv)
    if (args.timeout_ms <= 0 or args.node_seconds <= 0 or args.max_depth <= 0
            or not math.isfinite(args.node_seconds)):
        p.error("budgets must be positive")
    specs = parse_nodes(json.loads(args.nodes.read_text()))
    if args.formula_dir is not None:
        args.formula_dir.mkdir(parents=True, exist_ok=True)
    report = dict(scope="block-local", disclaimer=BANNER, stem=args.stem,
                  started_at_utc=datetime.now(timezone.utc).isoformat(),
                  configuration={k: str(v) for k, v in vars(args).items() if k != "stem"},
                  program_sha256={s: sha256(Path(args.stem + s).read_bytes()).hexdigest()
                                  for s in (".json", ".hex")},
                  model_sources_sha256=sha256(b"".join(
                      str(path).encode() + path.read_bytes()
                      for root in ("verification", "state", "x86_64", "evm_ir", "common")
                      for path in sorted(Path(root).rglob("*.py")))).hexdigest(),
                  requested_nodes=len(specs), nodes=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    prover = build_prover(args.stem, base_addr=args.base_addr, timeout_ms=args.timeout_ms,
                          node_seconds=args.node_seconds, max_depth=args.max_depth,
                          summaries=args.summaries, keep_going=args.keep_going)
    for spec in specs:
        report["nodes"].append(probe_node(prover, spec, args.formula_dir,
                                          None if args.node_memory_mb is None else int(args.node_memory_mb * 2**20)))
        report["locally_proved"] = sum(n["status"] == "proved" for n in report["nodes"])
        report["ended_at_utc"] = datetime.now(timezone.utc).isoformat()
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
        print({k: v for k, v in report["nodes"][-1].items() if k != "failed_obligations"}, flush=True)
    print(BANNER, flush=True)
    return 0 if report.get("locally_proved") == len(specs) else 1


if __name__ == "__main__":
    raise SystemExit(main())
