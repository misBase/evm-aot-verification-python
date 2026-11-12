"""One fixed E2.2 cell; real model, scalar path observation, no extra solver call."""
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SNAP = HERE / "e25_snapshot_d213_baea"
HARNESS = ROOT / "tmp/recorded-runs/measurement-work/paper-v2-deploy/harness-off-01"


def summary_stats_json(stats):
    result = {}
    for kind, value in stats.items():
        copied = dict(value) if isinstance(value, dict) else value
        if isinstance(copied, dict) and isinstance(copied.get("hit_entries"), (set, frozenset)):
            copied["hit_entries"] = sorted(copied["hit_entries"])
        result[kind] = copied
    return result


def classify_completion(raw, truncated, metrics):
    status = "BOUND" if raw == "BOUNDED" else raw
    complete = (status == "VERIFIED" and not truncated and len(metrics) == 2
                and all(m["coverage_complete"] for m in metrics.values()))
    if status == "VERIFIED" and not complete:
        status = "BOUND" if truncated else "UNK"
    return status, complete


def main():
    prepared = json.loads((HERE / "e22_formal_PREPARED.json").read_bytes())
    point = next(p for p in prepared["points"] if p["name"] == sys.argv[1])
    output = Path(os.environ["PAPER_WORKER_OUT"])
    events = None
    row = dict(result="ERR", verified=False, point=point, counterexample=False,
               scope="E22 variable-SHR family only; timing has no owned observer, separate diagnostics have primary executor counters and partial formula observation")
    observer = adapter = None
    try:
        assert sys.executable == str(ROOT / ".venv/bin/python")
        assert all(sha256(Path(p).read_bytes()).hexdigest() == h for p, h in prepared["pins"].items())
        os.chdir(SNAP)
        sys.path[:0] = [str(SNAP), str(HARNESS)]
        for key in list(os.environ):
            if key.startswith(("BLOCK_", "E25_")):
                os.environ.pop(key)
        cache = output.with_suffix(".smt.sqlite3")
        assert not cache.exists()
        os.environ["BLOCK_PROOF_CACHE"] = str(cache)
        spec = importlib.util.spec_from_file_location("actual_frozen_e22_formal_adapter", HARNESS / "worker.py")
        adapter = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = adapter
        spec.loader.exec_module(adapter)
        assert Path(adapter.__file__).resolve() == HARNESS / "worker.py"
        assert adapter.source_pin(SNAP) == prepared["source_pin"]
        import z3
        assert sys.version_info[:3] == (3, 13, 7) and z3.get_version_string() == "4.15.4"
        from evm_ir.json_parser import load_ir_from_json
        from evm_ir.program import EVMProgram
        from state.smt_state import SMTState
        from verification.program_verifier import ProgramEquivalenceChecker
        from x86_64.program import X86Program
        from x86_64.summaries import X86SummaryConfig
        adapter.paper_modes.apply(["bounded"])
        adapter.install_query_cap()
        kinds = [k for k in adapter.PROGRAM_SUMMARY_KINDS if point["shift_summary"] or k != "shift"]
        summary = X86SummaryConfig.enabled(**dict.fromkeys(kinds, "fallback"))
        evm = EVMProgram(load_ir_from_json(point["stem"] + ".json"))
        x86 = X86Program.from_hex(Path(point["stem"] + ".hex").read_text().strip(), base_addr=0x1000)
        state = SMTState.create_initial_state(num_inputs=0, calldata_size_bytes=512,
            symbolic_gas=False, gas_budget=1_000_000_000)
        state.assume_calldata_offset_no_overflow = False
        state.abstract_calldataload_words = False
        state.host_gas_uf_enabled = False
        if point["phase"] == "diagnostic":
            from e25_observer_v2 import Observer
            from verification.equivalence_checker import EquivalenceChecker
            events = output.with_suffix(".events")
            events.mkdir()
            observer = Observer(events, shape=True).install(project=False)

            def paths(value):
                c = value.coverage
                return dict(terminal_paths=len(value.global_states), coverage_complete=c.complete,
                    coverage_reason=c.reason, coverage_details=list(c.details))

            for owner, target, label in ((EVMProgram, evm, "primary_evm_paths"), (X86Program, x86, "primary_x86_paths")):
                observer.hook(owner, "to_z3_paths", label,
                    before=lambda args, kwargs, actual=target: dict(primary_program=args[0] is actual), after=paths)
            observer.hook(EquivalenceChecker, "check_equivalence", "final_solver")
            observer.hook(EquivalenceChecker, "check_equivalence_paths", "final_solver_paths")
        else:
            assert point["phase"] == "timing" and "e25_observer_v2" not in sys.modules
        phase_ms = max(1, int(adapter.remaining_seconds() * 1000))
        checker = ProgramEquivalenceChecker(timeout_ms=phase_ms, verbose=False, gas_check="off")
        kwargs = dict(path_observations=True, path_pair_workers=1, enable_merge=False,
            max_depth=400, x86_reachability_timeout_ms=250, summary_config=summary)
        wall, cpu = time.monotonic(), time.process_time()
        if observer:
            good, message = observer._call(checker.verify_program_pair, "program_proof", (evm, x86, state), kwargs)
        else:
            good, message = checker.verify_program_pair(evm, x86, state, **kwargs)
        elapsed, process_cpu = time.monotonic() - wall, time.process_time() - cpu
        if observer:
            observer.close()
            observer = None
        calls = [json.loads(line) for p in events.glob("pid-*.jsonl") for line in p.read_text().splitlines()] if events else []
        assert not any(c.get("observation_error") for c in calls)
        metrics = {}
        for label in ("primary_evm_paths", "primary_x86_paths"):
            matches = [c for c in calls if c["label"] == label and c.get("primary_program")]
            assert len(matches) <= 1
            if matches:
                metrics[label] = matches[0]
        raw = adapter.classify(good, message)
        if point["phase"] == "diagnostic":
            status, complete = classify_completion(raw, adapter.paper_modes.TRUNCATED, metrics)
        else:
            status = "BOUND" if raw == "BOUNDED" else raw
            complete = status == "VERIFIED" and not adapter.paper_modes.TRUNCATED
        row.update(result=status, verified=complete, actual_verified=good, raw_classification=raw,
            message=message, truncated=adapter.paper_modes.TRUNCATED[:20], primary_path_metrics=metrics,
            summary_config=adapter.summary_config_info(summary), summary_stats=summary_stats_json(x86.last_summary_stats),
            program_call_wall_s=elapsed, program_call_process_cpu_s=process_cpu, events=str(events) if events else None,
            observer_enabled=point["phase"] == "diagnostic",
            shape_coverage_complete=all(c.get("shape", {}).get("complete", True) for c in calls) if events else None,
            state_contract=dict(symbolic_gas=False, gas_budget=1_000_000_000, host_gas_uf_enabled=False,
                calldata_size_bytes=512, assume_calldata_offset_no_overflow=False, abstract_calldataload_words=False),
            effective=dict(max_depth=400, query_cap_ms=300000, phase_budget_ms=phase_ms, gas_check="off",
                path_pair_workers=1, enable_merge=False, reachability_timeout_ms=250, x86_base_addr=0x1000),
            native_solver_call_count=sum(c["label"] == "native_solver_check" for c in calls) if events else None,
            shape_scope="diagnostic current-process Solver assertions/assumptions and Tactic goals only; direct C/isolated coverage not assumed" if events else None,
            native_memory_scope="no extra allocator cap; frozen cooperative reach caps and outer hard tree limit",
            timing_scope="program interval includes summary discovery/proofs/replay/final checking; path phases overlap; outer guard CPU includes imports and reaped descendants")
        if "COUNTEREXAMPLE" in (message or ""):
            row.update(raw_status="CEX", counterexample=True, verified=False)
    except Exception as error:
        status = adapter.exception_status(error) if adapter else "ERR"
        row.update(result=status, verified=False, error_type=type(error).__name__, error=str(error), traceback=traceback.format_exc())
    finally:
        if observer:
            observer.close()
        row["pins_after"] = {p: sha256(Path(p).read_bytes()).hexdigest() for p in prepared["pins"]}
        if adapter:
            row["source_after"] = adapter.source_pin(SNAP)
        if row["pins_after"] != prepared["pins"] or row.get("source_after") != prepared["source_pin"]:
            row.update(result="ERR", verified=False, reason="source_or_input_pin_changed")
        output.write_text(json.dumps(row, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
