"""Selector-domain measurements; missing whole/x86 evidence stays unvalidated.

Legacy positional interface: STEM SELECTOR_HEX CALLDATA_SIZE OUT.json.
SELECTOR_HEX=whole with size=None measures a separately budgeted baseline.
--whole-report only reads existing metadata; --include-x86 explicitly measures
that side. Run from the frozen snapshot under run_one.py's external guard.
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, os.getcwd())
sys.path.insert(1, str(HERE))
from slices import (EXPECTED_SOURCE_PIN, EXPECTED_SOURCE_FILES, dispatcher_matches, evaluate_validity,
                    fixture_receipt, pin_selector, validity_analysis_config)


def source_receipt(snapshot):
    digest, count = sha256(), 0
    snapshot = Path(snapshot).resolve()
    for package in ("verification", "state", "x86_64", "evm_ir", "common", "tools"):
        for path in sorted((snapshot / package).rglob("*.py")):
            digest.update(path.relative_to(snapshot).as_posix().encode())
            digest.update(path.read_bytes())
            count += 1
    return dict(sha256=digest.hexdigest(), files=count)


def write_outputs(payload, output):
    paths = {Path(output)}
    if os.environ.get("PAPER_WORKER_OUT"):
        paths.add(Path(os.environ["PAPER_WORKER_OUT"]))
    for path in paths:
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
        temporary.replace(path)


def collect(args, payload):
    # Only an explicitly executed measurement imports the model/native modules.
    from z3 import And, SolverFor
    from evm_ir.cfg_executor import SymbolicExecutor
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from state.smt_state import SMTState
    from x86_64.cfg_state import z3_memory_cap

    whole = args.selector.lower() in ("whole", "all")
    selector = None if whole else int(args.selector, 16)
    size = None if args.calldata_size == "None" else int(args.calldata_size)
    if whole and size is not None:
        raise ValueError("whole baseline requires symbolic calldata size (None)")
    profile = payload["analysis_config"]
    state = SMTState.create_initial_state(symbolic_gas=profile["symbolic_gas"], gas_budget=profile["gas_budget"],
        **({"calldata_size_max_bytes": (1 << 63) - 1} if whole else {"calldata_size_bytes": size}))
    state.host_gas_uf_enabled = profile["host_gas_uf_enabled"]
    state.assume_calldata_offset_no_overflow = profile["assume_calldata_offset_no_overflow"]
    state.abstract_calldataload_words = profile["abstract_calldataload_words"]
    payload.update(selector_binding=None if whole else pin_selector(state, selector, size), calldata_size=size)
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=args.sat_timeout_ms)
    with z3_memory_cap(256):
        solver.add(And(*(state.assumptions or [])))
        answer = str(solver.check())
    payload["domain"] = dict(answer=answer, timeout_ms=args.sat_timeout_ms,
        reason_unknown=solver.reason_unknown() if answer == "unknown" else None)
    if answer != "sat":
        return
    data = json.loads(Path(args.stem + ".json").read_bytes())
    payload["dispatcher_matches"] = [] if whole else dispatcher_matches(data, selector)
    if not whole and not payload["dispatcher_matches"]:
        payload["measurement_reason"] = "selector lacks a structural dispatcher comparison"
        return
    evm = EVMProgram(load_ir_from_json(args.stem + ".json"))
    visited, original = set(), SymbolicExecutor.execute_state

    def execute_state(executor, global_state):
        if global_state.node is not None:
            visited.add(global_state.node.block.pc)
        return original(executor, global_state)

    SymbolicExecutor.execute_state = execute_state
    phase = time.monotonic()
    try:
        finals, coverage, _ = evm._execute_paths(state.copy(), max_depth=args.max_depth)
    finally:
        SymbolicExecutor.execute_state = original
    payload["metrics"]["evm"] = dict(block_pcs=sorted(visited), terminal_paths=len(finals),
        coverage_complete=coverage.complete, coverage_reason=coverage.reason,
        measurement="execute_state block visits and terminal symbolic paths", wall_seconds=time.monotonic() - phase)
    payload["dispatcher_explored"] = any(row["dispatcher_pc"] in visited for row in payload["dispatcher_matches"])
    # These compatibility fields are measurements, never the admission verdict.
    payload.update(blocks=sorted(visited), total_blocks=len(evm.blocks), terminal_paths=len(finals),
                   coverage_complete=coverage.complete, coverage_reason=coverage.reason)
    if args.include_x86:
        from verification.call_site_mapping import build_call_site_mapping
        from x86_64.program import X86Program
        from x86_64.summaries import X86SummaryConfig
        summary = profile["x86_summary"]
        summary_config = X86SummaryConfig.enabled(**summary["builtin_modes"],
            **{key: value for key, value in summary.items() if key != "builtin_modes"})
        x86 = X86Program.from_hex(Path(args.stem + ".hex").read_text().strip(), base_addr=profile["x86_base_addr"])
        phase = time.monotonic()
        paths = x86.to_z3_paths(state.copy(), max_depth=args.max_depth, enable_merge=profile["x86_merge"],
            reachability_timeout_ms=profile["x86_reachability_timeout_ms"], call_site_mapping=build_call_site_mapping(evm, x86),
            summary_config=summary_config)
        payload["metrics"]["x86"] = dict(terminal_paths=len(paths.observations),
            coverage_complete=paths.coverage.complete if paths.coverage is not None else False,
            coverage_reason=paths.coverage.reason if paths.coverage is not None else "no coverage certificate",
            measurement="terminal symbolic observations", wall_seconds=time.monotonic() - phase)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("stem", "selector", "calldata_size", "output"):
        parser.add_argument(name)
    parser.add_argument("--whole-report", type=Path)
    parser.add_argument("--include-x86", action="store_true")
    parser.add_argument("--gas", choices=("off",), default="off")
    parser.add_argument("--max-depth", type=int, default=100000)
    parser.add_argument("--sat-timeout-ms", type=int, default=1000)
    parser.add_argument("--expected-source-pin", default=EXPECTED_SOURCE_PIN)
    args = parser.parse_args(argv)
    if args.max_depth < 1 or args.sat_timeout_ms < 1:
        parser.error("depth and SAT timeout must be positive")
    payload = dict(kind="slice-validity", schema="paper-slice-validity-v2", verified=False,
        result="N/A", stem=args.stem, metrics={"evm": None, "x86": None}, gas_check=args.gas,
        max_depth=args.max_depth, source_unchanged=False, whole_baseline=None,
        analysis_config=validity_analysis_config(),
        scope="sample admission measurements; no equivalence or program certificate")
    started = time.monotonic()
    before = source_receipt(Path.cwd())
    payload.update(source_pin=before["sha256"], source_files=before["files"])
    try:
        if before != dict(sha256=args.expected_source_pin, files=EXPECTED_SOURCE_FILES):
            raise ValueError("snapshot model pin mismatch")
        payload["input"] = fixture_receipt(args.stem)
        if args.whole_report:
            raw = args.whole_report.read_bytes()
            payload["whole_baseline"] = json.loads(raw)
            payload["whole_baseline_file"] = dict(path=str(args.whole_report.resolve()), sha256=sha256(raw).hexdigest())
        collect(args, payload)
    except Exception as error:
        payload["measurement_error"] = f"{type(error).__name__}: {error}"
    finally:
        after = source_receipt(Path.cwd())
        payload.update(source_after=after, source_unchanged=before == after,
                       measurement_wall_seconds=time.monotonic() - started)
        if args.selector.lower() in ("whole", "all"):
            ready = (not payload.get("measurement_error") and payload.get("domain", {}).get("answer") == "sat"
                     and payload["metrics"]["evm"] is not None and payload["source_unchanged"])
            payload["result"] = "WHOLE-METRICS" if ready else "N/A"
        else:
            payload["validation"] = evaluate_validity(payload, payload["whole_baseline"])
            payload["result"] = "SLICE-VALID" if payload["validation"]["accepted"] else "N/A"
        write_outputs(payload, args.output)
    print(payload["result"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
