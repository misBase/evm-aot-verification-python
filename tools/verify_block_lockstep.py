"""Reproducible block verifier report with an outer process wall limit.

Usage: poetry run python -m tools.verify_block_lockstep tests/data/mstore_return
       --gas-check full --summaries --output /tmp/result.json
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
import multiprocessing as mp
from pathlib import Path
import platform
import subprocess
import time


_BASIS = "Recorded diagnostics; only status=verified establishes a consumed program certificate."


def _progress_report(result):
    # Diagnostics are observations at proof time, not reusable certificates.
    instances = [instance for block in result.diagnostics.values()
                 for instance in block["instances"]]
    return dict(kind="progress", status="inconclusive",
        diagnostics=result.diagnostics, closure_checks=result.closure_checks, timings=result.timings,
        running=list(getattr(result, "running", ())),
        reasons=list(result.reasons), attempted_instances=len(instances),
        recorded_local_theorems=sum(n["status"] == "proved" for n in instances),
        local_statistics_basis=_BASIS)


def _interrupted_report(latest, reason):
    # Keep every local failure already reported; an abort adds a reason, and no
    # counter that would claim a certificate survives it.
    reasons = [*latest.get("reasons", ()), reason]
    return dict(latest, status="inconclusive", reasons=reasons,
        complete_local_theorems=0, entry_certificates=0, edge_certificates=0,
        message="INCONCLUSIVE: " + "; ".join(reasons))


def _message(result, verified, graph):
    """BlockProgramResult.message wording, derived from one consumer answer."""
    if not verified:
        return ("INCONCLUSIVE: " + "; ".join(result.reasons or ("incomplete certificate graph",))
                + ". " + result.scope)
    if graph is None:
        return "VERIFIED: independent full-program rerun certificate (no block results reused). " + result.scope
    return f"VERIFIED: closed block lockstep certificate ({len(result.nodes)} instances). {result.scope}"


def _final_report(result, evm_blocks):
    from verification.block_program import ProgramCertificate

    # Consume the complete certificate exactly once: `verified` rehashes every
    # node's path states against a freshly computed program identity. Nothing
    # below may re-enter it (`result.message` and `node.proved` both would), and
    # recorded statistics are never promoted to evidence.
    verified = result.verified
    graph = result.certificate if verified and isinstance(result.certificate, ProgramCertificate) else None
    report = _progress_report(result)
    report.pop("kind")
    report.update(status="verified" if verified else "inconclusive",
        message=_message(result, verified, graph),
        scope=result.scope, block_failure_reasons=list(result.block_failure_reasons),
        evm_blocks=evm_blocks,
        complete_local_theorems=len(graph.nodes) if graph else 0,
        entry_certificates=int(graph is not None),
        edge_certificates=len(graph.edges) if graph else 0,
        queries=result.queries, elapsed_seconds=result.elapsed_seconds,
        summary_hits=sum(len(n.theorem.summary_hits) for n in result.nodes if n.theorem),
        node_seconds=[n.elapsed_seconds for n in result.nodes])
    return report


def _verify(stem, options, channel):
    latest = {}
    try:
        from evm_ir.json_parser import load_ir_from_json
        from evm_ir.program import EVMProgram
        from x86_64.program import X86Program
        from x86_64.summaries import X86SummaryConfig
        from state.smt_state import SMTState
        from verification.block_program import BlockProgramVerifier
        from verification.program_verifier import GasCheck
        evm = EVMProgram(load_ir_from_json(str(stem) + ".json"))
        x86 = X86Program.from_hex(Path(str(stem) + ".hex").read_text().strip(), base_addr=0x1000)
        mode = GasCheck(options["gas_check"])
        state = SMTState.create_initial_state(num_inputs=options["num_inputs"],
            symbolic_gas=mode == GasCheck.FULL,
            gas_budget=None if mode == GasCheck.FULL else options["gas_budget"])
        state.assume_calldata_offset_no_overflow = False
        state.host_gas_uf_enabled = mode != GasCheck.OFF
        config = X86SummaryConfig.enabled(calldataload="fallback", copy_loop="fallback", mul="fallback", div="fallback", memgas="fallback") if options["summaries"] else None
        def progress(result):
            nonlocal latest
            latest = _progress_report(result)
            channel.send(latest)
        if options.get("discover_first"):
            from verification.block_parallel import verify_parallel
            r = verify_parallel(stem, options, workers=options["node_workers"],
                                pair_workers=options["pair_workers_per_node"],
                                results_dir=options["results_dir"], progress_callback=progress)
            channel.send(_final_report(r, len(evm.blocks)))
            return
        r = BlockProgramVerifier(gas_check=mode, timeout_ms=options["timeout_ms"],
            max_depth=options["max_depth"], max_instances=options["max_instances"],
            wall_timeout_seconds=options["wall_seconds"], summary_config=config,
            node_timeout_seconds=options["node_seconds"],
            max_parameter_values=options["max_parameter_values"],
            first_pass_node_seconds=options["first_pass_node_seconds"],
            fallback=options["fallback"], progress_callback=progress,
            pushed_code_return_tags=options["pushed_code_return_tags"],
            terminal_constant_projection=options["terminal_constant_projection"],
            context_constant_projection=options["context_constant_projection"]).verify_program_pair(evm, x86, state)
        channel.send(_final_report(r, len(evm.blocks)))
    except BaseException as exc:
        report = _interrupted_report(latest, f"{type(exc).__name__}: {exc}")
        report.pop("kind", None)
        channel.send(report)
    finally:
        channel.close()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("stem", type=Path, help="Path without .json/.hex extension")
    p.add_argument("--gas-check", choices=("off", "fixed_budget", "full"), default="fixed_budget")
    p.add_argument("--gas-budget", type=int, default=1_000_000_000)
    p.add_argument("--num-inputs", type=int, default=0, help="Initial EVM stack values, NOT calldata length; calldata length and contents remain symbolic")
    p.add_argument("--timeout-ms", type=int, default=3000)
    p.add_argument("--node-seconds", type=float, default=60, help="Per-node soft proof budget; global hard limit remains necessary")
    p.add_argument("--first-pass-node-seconds", type=float, default=None,
                   help="Short first-pass node budget; nodes that run out or get unknown are retried with --node-seconds after the queue drains")
    p.add_argument("--max-parameter-values", type=int, default=8, help="Concrete (msize, fmp) instances per context before widening to TOP")
    p.add_argument("--max-depth", type=int, default=400)
    p.add_argument("--max-instances", type=int, default=2048)
    p.add_argument("--wall-seconds", type=float, default=300)
    p.add_argument("--hard-wall-seconds", type=float, default=360)
    p.add_argument("--summaries", action="store_true")
    p.add_argument("--fallback", choices=("none", "full-program"), default="none")
    p.add_argument("--output", type=Path)
    p.add_argument("--discover-first", action="store_true",
                   help="EVM-only discovery of the whole instance set, then parallel node proofs (verification/block_parallel.py)")
    p.add_argument("--node-workers", type=int, default=4, help="--discover-first: node proofs in parallel")
    p.add_argument("--pair-workers-per-node", type=int, default=1, help="--discover-first: BLOCK_PAIR_WORKERS inside each node worker")
    p.add_argument("--results-dir", type=Path, help="--discover-first: persist finished nodes here and resume from them")
    p.add_argument("--node-memory-mb", type=float, default=None,
                   help="--discover-first: per-node RSS budget of a worker; a node over it is stopped and reported "
                        "inconclusive alone (common/node_monitor). Default: no budget")
    p.add_argument("--status-dir", type=Path, default=None,
                   help="--discover-first: worker status files (node, pid, start, RSS); default: a temporary directory")
    p.add_argument("--constant-insensitive", action="store_true",
                   help="--discover-first only: prove each block once per proof instance that drops the stack constants it never consumes (docs/块级实例常量去敏化方案.md)")
    p.add_argument("--pushed-code-return-tags", action="store_true",
                   help="Discovery hint: also keep pushed JUMPDEST constants (return addresses of JUMPs without an IR immediate_set) as return tags, never widened")
    p.add_argument("--terminal-constant-projection", action="store_true",
                   help="Discovery hint: a block ending in STOP/RETURN/REVERT/INVALID/SELFDESTRUCT is registered with only the stack constants it consumes")
    p.add_argument("--context-constant-projection", action="store_true",
                   help="Discovery hint (needs --pushed-code-return-tags): register each context with its return tags and only the other stack constants its block consumes")
    args = p.parse_args()
    if args.context_constant_projection and not args.pushed_code_return_tags:
        p.error("--context-constant-projection needs --pushed-code-return-tags")
    options = {k: v for k, v in vars(args).items() if k not in ("stem", "output")}
    for key in ("results_dir", "status_dir"):
        if options[key] is not None:
            options[key] = str(options[key])  # report metadata is JSON
    if args.constant_insensitive and not args.discover_first:
        p.error("--constant-insensitive needs --discover-first (the worklist discovers from proved exits)")
    if args.hard_wall_seconds <= 0:
        p.error("--hard-wall-seconds must be positive")
    started = time.monotonic()
    metadata = dict(started_at_utc=datetime.now(timezone.utc).isoformat(), stem=str(args.stem), configuration=options, host=platform.platform(),
        python=platform.python_version(), workers=1,
        program_sha256={suffix: sha256(Path(str(args.stem) + suffix).read_bytes()).hexdigest()
                        for suffix in (".json", ".hex")},
        revision=subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip(),
        worktree_sha256=sha256(subprocess.run(["git", "diff", "--", "verification", "state", "x86_64", "evm_ir"],
                                             capture_output=True, check=True).stdout).hexdigest())
    metadata["total_source_blocks"] = len(json.loads(Path(str(args.stem) + ".json").read_text())["control_frames"])
    metadata["unvisited_policy"] = "Missing local statistics never establish unreachability or a program proof."
    # Environment knobs that change how (not what) obligations are decided.
    metadata["pair_workers"] = int(os.environ.get("BLOCK_PAIR_WORKERS", "1"))
    metadata["proof_cache"] = os.environ.get("BLOCK_PROOF_CACHE") or None
    # Hash untracked/new implementation files too; git diff alone omits them.
    metadata["model_sources_sha256"] = sha256(b"".join(
        str(path).encode() + path.read_bytes() for root in ("verification", "state", "x86_64", "evm_ir", "common")
        for path in sorted(Path(root).rglob("*.py")))).hexdigest()
    context = mp.get_context("spawn")
    parent, child = context.Pipe(duplex=False)
    worker = context.Process(target=_verify, args=(args.stem, options, child))
    worker.start()
    child.close()
    deadline = started + args.hard_wall_seconds
    latest = {}
    result = None
    while time.monotonic() < deadline:
        if not parent.poll(min(1.0, max(0, deadline - time.monotonic()))):
            continue
        try:
            received = parent.recv()
        except EOFError:
            result = _interrupted_report(latest, "worker exited without a complete report")
            break
        if received.get("kind") == "progress":
            latest = received
            if args.output:
                partial = args.output.with_suffix(".partial.json")
                partial.parent.mkdir(parents=True, exist_ok=True)
                partial.write_text(json.dumps(dict(latest, **metadata), ensure_ascii=False, indent=2) + "\n")
            continue
        result = received
        break
    if result is None:
        result = _interrupted_report(latest, "outer process wall budget exhausted; no certificate issued")
        # SIGKILL, not SIGTERM: exit-time C++ teardown races a running z3 call
        # into SIGSEGV (macOS 'Python quit unexpectedly'). Nothing to flush here.
        worker.kill()
    worker.join(timeout=5)
    if worker.is_alive():
        worker.kill()
        worker.join()
    result.pop("kind", None)
    result.update(metadata)
    result["process_wall_seconds"] = time.monotonic() - started
    result["ended_at_utc"] = datetime.now(timezone.utc).isoformat()
    text = json.dumps(result, ensure_ascii=False, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n")
    print(text)
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
