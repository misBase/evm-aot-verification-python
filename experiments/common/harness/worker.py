"""One paper job from a frozen snapshot; only this external adapter is mutable."""
import dataclasses
from hashlib import sha256
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, os.getcwd())
sys.path.insert(1, str(Path(__file__).resolve().parent))
import paper_modes  # noqa: E402

V0_DEPTH = 1_000_000_000
DEFAULT_MAX_DEPTH = 400
SINGLE_SOLVER_MS = 300_000
CONFIG_EPOCH = "2026-11-12-v3-o1o2-mixed"
HARNESS_FILES = ("worker.py", "paper_modes.py", "run_one.py", "slices.py", "single_cfg_merge.py", "source_pin.py")
INITIAL_GAS_BUDGET = 1_000_000_000
from source_pin import SHA256 as EXPECTED_SOURCE_PIN, FILES as EXPECTED_SOURCE_FILES  # noqa: E402
PROGRAM_SUMMARY_KINDS = ("calldataload", "copy_loop", "mul", "div", "memgas", "shift", "sdiv", "smod")
PROGRAM_BASE_ADDR = 0x1000
B4_OFF = ["naive_arith_only", "no_div_bridge", "no_div64_hint"]
ALIVE2 = dict(path_observations=False, enable_merge=True, summary=False, modes=B4_OFF)
FULL = dict(path_observations=True, path_pair_workers=4, enable_merge=False, summary=True,
            x86_reachability_timeout_ms=250, modes=[])
PATHS_CONFIGS = {
    "V0": dict(ALIVE2, max_depth=V0_DEPTH),
    "V1": dict(ALIVE2, bounded=True),
    "V2": dict(FULL, bounded=True),
    "V2-B1B2": dict(FULL, bounded=True, path_observations=False, path_pair_workers=1, enable_merge=True),
    "V2-B3": dict(FULL, bounded=True, summary=False),
    "V2-B4": dict(FULL, bounded=True, modes=B4_OFF),
    "V2-O1": dict(FULL, bounded=True, path_observations=False, path_pair_workers=1, enable_merge=True),  # = B1+B2
    "V2-O2": dict(FULL, bounded=True, summary=False, modes=B4_OFF),  # = B3+B4
}
SINGLE_CONFIGS = {
    "V0": dict(modes=B4_OFF + ["no_path_ite"], summary=False, terminal_paths=False),
    "V1": dict(modes=B4_OFF + ["no_path_ite"], summary=False, terminal_paths=False),
    "V2": dict(modes=[]),
    "V2-B1B2": dict(modes=[], terminal_paths=False),
    "V2-B3": dict(modes=[], summary=False),
    "V2-B4": dict(modes=B4_OFF + ["no_path_ite"]),
    "V2-B4a": dict(modes=["naive_arith_only"]),
    "V2-B4b": dict(modes=["no_div_bridge"]),
    "V2-B4c": dict(modes=["no_div64_hint"]),
    "V2-B4d": dict(modes=["no_path_ite"]),
    "V2-O1": dict(modes=[], terminal_paths=False),  # = B1+B2
    "V2-O2": dict(modes=B4_OFF + ["no_path_ite"], summary=False),  # = B3+B4
}
LOCKSTEP_CONFIGS = {"V3": dict(summaries=True, cache=True, node_workers=4)}


def classify(verified, message):
    text = message or ""
    if verified:
        if not paper_modes.TRUNCATED:
            return "VERIFIED"
        feasible = re.search(r"(\d+)/\d+ feasible pair", text)
        return "N/A" if feasible and feasible.group(1) == "0" else "BOUNDED"
    if "UNSUPPORTED:" in text:
        return "N/A"
    if "COVERAGE INCOMPLETE" in text:
        reason = text.split("dropped paths (", 1)[-1]
        return "BOUND" if paper_modes.depth_only(reason.rstrip(")")) else "UNK"
    if "do not cover all inputs" in text:
        return "UNK"
    if "COUNTEREXAMPLE" in text or "solver_result=sat" in text:
        return "ERR"
    if re.search(r"(?:^|\n|: )\??\s*TIMEOUT:", text):
        return "TO"
    return "UNK"


def remaining_seconds(default=3600.0):
    value = os.environ.get("PAPER_DEADLINE_MONOTONIC")
    return max(0.001, float(value) - time.monotonic()) if value else default


def summary_config_info(config):
    if config is None:
        return None
    return dict(repr=repr(config), builtin_modes=dict(config.builtin_modes),
                prove_mul_hits=config.prove_mul_hits, prove_div_hits=config.prove_div_hits,
                mul_proof_timeout_ms=config.mul_proof_timeout_ms, div_proof_timeout_ms=config.div_proof_timeout_ms)


def summary_failure_status(module_name, class_name, answer, reason):
    known = ("SummaryPreconditionError", "MulProofError", "DivProofError", "MemGasProofError", "ShiftProofError", "SignedProofError")
    if module_name.startswith("x86_64.summaries.") and class_name in known:
        if reason == "timeout":
            return "TO"
        if answer == "unknown" or reason == "unknown":
            return "UNK"
    return "ERR"


def exception_status(error):
    answer = str(getattr(error, "solver_result", getattr(error, "result", "")))
    reason = str(getattr(error, "reason", ""))
    return summary_failure_status(type(error).__module__, type(error).__name__, answer, reason)


def cli_status_consistent(returncode, status):
    return returncode in (0, 1) and ((returncode == 0) == (status == "verified"))


def input_pair_info(stem):
    paths = {suffix:Path(stem + suffix) for suffix in (".json", ".hex")}
    missing = [suffix for suffix,path in paths.items() if not path.is_file()]
    hashes = {suffix:sha256(path.read_bytes()).hexdigest() for suffix,path in paths.items() if path.is_file()}
    alias = None
    if not missing and Path(stem).name == "jumpi_2block_err":
        original = Path(stem).with_name("jumpi_2block")
        pair = {suffix:Path(str(original)+suffix) for suffix in paths}
        if all(path.is_file() and sha256(path.read_bytes()).hexdigest()==hashes[suffix] for suffix,path in pair.items()):
            alias = "jumpi_2block"
    return dict(input_missing_pair=missing, input_pair_sha256=hashes, alias_of=alias)


def source_pin(snapshot):
    digest, count = sha256(), 0
    for package in ("verification", "state", "x86_64", "evm_ir", "common", "tools"):
        for path in sorted((snapshot / package).rglob("*.py")):
            digest.update(path.relative_to(snapshot).as_posix().encode())
            digest.update(path.read_bytes())
            count += 1
    return dict(sha256=digest.hexdigest(), files=count)


def loaded_sources(snapshot):
    sources = {}
    for name, module in list(sys.modules.items()):
        if name.split(".")[0] not in ("verification", "state", "x86_64", "evm_ir", "common", "tools", "utils", "tests"):
            continue
        filename = getattr(module, "__file__", None)
        if not filename:
            continue
        path = Path(filename).resolve()
        if not path.is_relative_to(snapshot):
            raise ValueError(f"runtime module outside snapshot: {name}: {path}")
        sources[name] = dict(path=str(path), sha256=sha256(path.read_bytes()).hexdigest())
    return sources


def install_query_cap(cap_ms=SINGLE_SOLVER_MS):
    """Keep the phase deadline, cap each context reset including private threads.

    These external runtime patches alter solver budgets, never predicates/gates.
    A shorter original subquery cap is preserved. No snapshot file is changed.
    """
    from verification.equivalence_context import _EquivalenceContext as context
    original = context.reset_solver_with_budget_for
    original_capped = context.reset_solver_with_capped_budget_for
    original_unknown = context.unknown_message_for_solver
    query_cap = cap_ms

    def reset(solver, timeout_ms, deadline):
        active = original(solver, timeout_ms, deadline)
        if active:
            remaining = cap_ms if deadline is None else max(1, int((deadline - time.time()) * 1000))
            solver.set("timeout", max(1, min(timeout_ms, cap_ms, remaining)))
        return active

    def capped(solver, timeout_ms, deadline, cap_ms):
        effective = query_cap if cap_ms is None or cap_ms <= 0 else min(cap_ms, query_cap)
        return original_capped(solver, min(timeout_ms, query_cap), deadline, effective)

    def unknown(solver, timeout_ms):
        return original_unknown(solver, min(timeout_ms, cap_ms))

    context.reset_solver_with_budget_for = staticmethod(reset)
    context.reset_solver_with_capped_budget_for = staticmethod(capped)
    context.unknown_message_for_solver = staticmethod(unknown)


def run_program(stem, config, selector=None, calldata_size=None, whole=False, max_depth=None, gas="off"):
    cfg = PATHS_CONFIGS[config]
    depth = V0_DEPTH if config == "V0" else (max_depth or DEFAULT_MAX_DEPTH)
    extra = dict(config_epoch=CONFIG_EPOCH, config_expanded=dict(cfg, max_depth=depth),
                 scope="program verifier paths or merged report; not a block certificate",
                 requested=dict(gas_check=gas, path_observations=cfg["path_observations"], max_depth=max_depth),
                 effective=dict(gas_check=gas, max_depth=depth, path_observations=cfg["path_observations"],
                    path_pair_workers=cfg.get("path_pair_workers", 1), enable_merge=cfg.get("enable_merge", True)),
                 single_solver_ms=SINGLE_SOLVER_MS, x86_base_addr=PROGRAM_BASE_ADDR)
    if gas != "off":
        extra.update(raw_status="UNSUPPORTED", reason="requested_gas_mode_not_supported")
        extra["effective"].update(execution_started=False, gas_check=None)
        return False, "UNSUPPORTED: paper V0-V2 require gas=off", extra
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from state.smt_state import SMTState
    from verification.program_verifier import ProgramEquivalenceChecker
    from x86_64.program import X86Program
    from x86_64.summaries import X86SummaryConfig
    paper_modes.apply(cfg["modes"] + (["bounded"] if cfg.get("bounded") else []))
    install_query_cap()
    summary_config = X86SummaryConfig.enabled(**{kind:"fallback" for kind in PROGRAM_SUMMARY_KINDS}) if cfg["summary"] else None
    extra["summary_config"] = summary_config_info(summary_config)
    if whole or selector is not None:
        from slices import fixture_receipt
        extra["fixture"] = fixture_receipt(stem)
    evm = EVMProgram(load_ir_from_json(stem + ".json"))
    x86 = X86Program.from_hex(Path(stem + ".hex").read_text().strip(), base_addr=PROGRAM_BASE_ADDR)
    initial = dict(symbolic_gas=False, gas_budget=INITIAL_GAS_BUDGET)
    initial.update(calldata_size_max_bytes=(1 << 63) - 1) if whole else initial.update(calldata_size_bytes=calldata_size)
    state = SMTState.create_initial_state(**initial)
    state.assume_calldata_offset_no_overflow = False
    state.abstract_calldataload_words = False
    state.host_gas_uf_enabled = False
    extra["state_contract"] = dict(symbolic_gas=False, gas_budget=INITIAL_GAS_BUDGET,
                                   assume_calldata_offset_no_overflow=False,
                                   abstract_calldataload_words=False, host_gas_uf_enabled=False)
    if selector is not None:
        from slices import pin_selector
        extra["selector_binding"] = pin_selector(state, selector, calldata_size)
    kwargs = {k: cfg[k] for k in ("path_observations", "path_pair_workers", "enable_merge", "x86_reachability_timeout_ms") if k in cfg}
    phase_ms = max(1, int(remaining_seconds() * 1000))
    checker = ProgramEquivalenceChecker(timeout_ms=phase_ms, verbose=False, gas_check="off")
    verified, message = checker.verify_program_pair(evm, x86, state, stack_check=None,
        summary_config=summary_config, max_depth=depth, **kwargs)
    stats = getattr(x86, "last_summary_stats", {}) or {}
    extra.update(phase_budget_ms=phase_ms, query_cap_scope="context reset methods including private-thread solvers; original shorter caps preserved",
                 summary_hits={k:v.get("hits") for k,v in stats.items() if isinstance(v, dict)})
    return verified, message, extra


def single_gas_off_case(case):
    """Keep normal core observations, pin both real initial gas sources to 1e9."""
    return dataclasses.replace(case, compare_gas=False,
        evm_context_values=tuple((name, value) for name, value in case.evm_context_values if name != "gas") + (("gas", INITIAL_GAS_BUDGET),),
        x86_callengine_limb_values=tuple((offset, value) for offset, value in case.x86_callengine_limb_values if offset != 0x70) + ((0x70, INITIAL_GAS_BUDGET),))


def run_single(name, config, max_depth=None, gas="off"):
    if gas != "off":
        return False, "UNSUPPORTED: paper V0-V2 require gas=off", {"requested": {"gas_check": gas}, "raw_status": "UNSUPPORTED", "reason": "requested_gas_mode_not_supported"}
    import tests.integration.test_single_ins_equivalence as suite
    import tests.support.instruction_equivalence as harness
    from single_cfg_merge import CoverageError, observe_single_core
    cfg = SINGLE_CONFIGS[config]
    paper_modes.apply(cfg["modes"])
    (case,) = [c for c in suite.INSTRUCTION_REFINEMENT_CASES if c.name == name]
    depth = V0_DEPTH if config == "V0" else (max_depth or DEFAULT_MAX_DEPTH)
    changes = dict(solver_timeout_ms=SINGLE_SOLVER_MS, x86_max_depth=depth)
    if cfg.get("summary") is False:
        changes["x86_summary_config"] = None
    if cfg.get("terminal_paths") is False:
        changes["x86_compare_terminal_paths"] = False
    case = single_gas_off_case(dataclasses.replace(case, **changes))
    unknowns = []
    original_factory = harness._make_equivalence_solver

    def factory(actual_case):
        solver = original_factory(actual_case)
        original_check = solver.check
        def check(*args, **kwargs):
            answer = original_check(*args, **kwargs)
            if str(answer) == "unknown":
                try:
                    unknowns.append(solver.reason_unknown())
                except Exception as exc:
                    unknowns.append(f"unavailable: {type(exc).__name__}")
            return answer
        solver.check = check
        return solver

    extra = dict(config_epoch=CONFIG_EPOCH, single_solver_ms=SINGLE_SOLVER_MS,
                 requested=dict(max_depth=max_depth, gas_check=gas),
                 effective=dict(max_depth=depth, gas_check="off",
                    case_execution_mode=case.x86_execution_mode,
                    compare_gas=case.compare_gas, terminal_paths=case.x86_compare_terminal_paths, base_addr=case.base_addr,
                    path_pair_workers=1, path_pair_parallelism_applicable=False),
                 gas_scope_reason="concrete seed 1e9 where the core harness constructs state; original core/GAS stack observations retained; final gas comparison disabled",
                 state_contract=dict(symbolic_gas=False, gas_budget=INITIAL_GAS_BUDGET, host_gas_uf_enabled=False,
                    evm_gas_state_scope="stateful cases use the concrete seed; pure stack operation_semantics has no gas-state instance",
                    gas_deduction_scope="existing frozen core/state semantics; no new gas prelude"),
                 scope="single-instruction core observables, not a full-program certificate", unknown_reasons=unknowns,
                 summary_config=summary_config_info(case.x86_summary_config), summary_hits=None,
                 summary_hits_scope="instruction harness does not export hits; enabled configuration is not a hit")
    harness._make_equivalence_solver = factory
    try:
        with observe_single_core(harness, config, terminal_paths=case.x86_compare_terminal_paths,
                                 execution_mode=case.x86_execution_mode) as core:
            extra["single_core"] = core
            harness.assert_instruction_equivalent(case)
        return True, "unsat on every core mismatch", extra
    except CoverageError as error:
        extra.update(raw_status="INCOMPLETE_CORE", reason=str(error), single_core=error.evidence)
        return False, f"{error.status}: {error}", extra
    except AssertionError as error:
        text = str(error)
        prefix = "ERR" if "solver_result=sat" in text else "TO" if unknowns and unknowns[-1] == "timeout" else "UNK" if "solver_result=unknown" in text else "ERR"
        if "solver_result=sat" in text:
            extra.update(raw_status="CEX", reason="core_counterexample")
        extra["raw_failure"] = text
        return False, f"{prefix}: {text}", extra
    except ValueError as error:
        text = str(error)
        prefix = "BOUND" if "depth_pruned_states=" in text else "UNK" if "cfg execution produced no terminal paths" in text else exception_status(error)
        if prefix in ("UNK", "TO"):
            extra.update(raw_status="SUMMARY_PROOF_UNKNOWN" if type(error).__module__.startswith("x86_64.summaries.") else "INCOMPLETE_CORE",
                         reason=str(getattr(error, "reason", "unavailable")))
        return False, f"{prefix}: {text}", extra
    finally:
        harness._make_equivalence_solver = original_factory
        if "single_core" in extra:
            extra["effective"].update(cfg_merge_actual=extra["single_core"]["cfg_merge_actual"],
                core_coverage_complete=extra["single_core"]["coverage_complete"])


def run_lockstep(stem, config, wall_seconds, max_depth=400, gas="full"):
    cfg = LOCKSTEP_CONFIGS[config]
    if gas != "full":
        return False, "UNSUPPORTED: V3 requires gas=full", {}
    from slices import fixture_receipt
    fixture = fixture_receipt(stem) if Path(stem).name in ("ENSRegistry", "Permit2", "Safe", "CErc20", "PoolManager", "Pool") else None
    work = Path(os.environ["PAPER_WORKER_OUT"]).with_suffix(".lockstep")
    work.mkdir(exist_ok=False)
    git = subprocess.run(["git", "rev-parse", "--is-inside-work-tree"], capture_output=True, text=True)
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    if (git.returncode or git.stdout.strip() != "true" or top.returncode
            or Path(top.stdout.strip()).resolve() != Path.cwd().resolve()):
        return False, "UNSUPPORTED: V3 CLI needs a separately provisioned git worktree; adapter never creates a scratch commit", {
            "work": str(work), "raw_status": "UNSUPPORTED", "reason": "cli_git_worktree_required",
            "requested": dict(gas_check=gas, max_depth=max_depth, wall_seconds=wall_seconds),
            "effective": dict(execution_started=False)}
    env = dict(os.environ, BLOCK_PROOF_CACHE=str(work / "cache.sqlite3"), BLOCK_PAIR_WORKERS="1", BLOCK_SUMMARY_LEMMAS="1")
    for name in ("BLOCK_TRACE_OBLIGATIONS", "BLOCK_ROUTE_ORDER", "BLOCK_MERGE_DIAMONDS", "BLOCK_KEEP_SUMMARY_TEXT"):
        env.pop(name, None)
    remaining = min(wall_seconds, remaining_seconds(wall_seconds))
    report_path = work / "report.json"
    # V3 = mixed mode: the codegen trace of this input as instruction hints (PAPER_HINTS_DIR/trace-<name>.json).
    # A complete contract without its trace would silently run block-only: refuse instead.
    hints_dir = os.environ.get("PAPER_HINTS_DIR")
    trace = Path(hints_dir) / f"trace-{Path(stem).name}.json" if hints_dir else None
    if trace is None or not trace.is_file():
        if fixture is not None:
            return False, f"ERR: V3 mixed mode needs {trace} for a complete contract", dict(
                work=str(work), raw_status="ERR", reason="missing_instruction_hints")
        trace = None
    hint_args = ["--instruction-hints", str(trace)] if trace is not None else []
    command = [sys.executable, "-m", "tools.verify_block_lockstep", stem,
        "--gas-check", "full", "--gas-budget", "1000000000", "--num-inputs", "0",
        "--timeout-ms", "30000", "--node-seconds", "14400", "--first-pass-node-seconds", "300",
        "--max-parameter-values", "32", "--max-depth", str(max_depth), "--max-instances", "8192",
        "--wall-seconds", str(remaining), "--hard-wall-seconds", str(remaining),
        "--summaries", "--fallback", "none", "--discover-first", "--constant-insensitive",
        "--node-workers", "4", "--pair-workers-per-node", "1", "--node-memory-mb", "2000",
        "--status-dir", str(work / "workers"), "--results-dir", str(work / "results"), "--output", str(report_path),
        *hint_args]
    completed = subprocess.run(command, env=env, check=False)  # inherit the outer guard's process group
    extra = dict(cli_command=command, cli_returncode=completed.returncode, work=str(work), fixture=fixture,
                 instruction_hints=None if trace is None else dict(
                     path=str(trace), sha256=sha256(trace.read_bytes()).hexdigest()),
                 cli_proof_cache=env["BLOCK_PROOF_CACHE"],
                 requested=dict(gas_check=gas, max_depth=max_depth, wall_seconds=wall_seconds),
                 effective=dict(gas_check="full", max_depth=max_depth, wall_seconds=remaining),
                 experimental_run=True, formal_release_certificate=False)
    if not report_path.exists():
        return False, "ERR: V3 CLI exited without a complete report", extra
    report = json.loads(report_path.read_text())
    instances = [i for b in report.get("diagnostics", {}).values() for i in b["instances"]]
    extra.update(lockstep_status=report["status"], timings=report.get("timings", {}),
        instances=len(instances), proved_instances=sum(i["status"] == "proved" for i in instances),
        blocks_proved=sum(b["status"] == "proved" for b in report["diagnostics"].values()),
        blocks_total=len(report["diagnostics"]), lockstep_config=cfg, cli_report=str(report_path),
        cli_revision=report.get("revision"), cli_model_sources_sha256=report.get("model_sources_sha256"),
        cli_report_proof_cache=report.get("proof_cache"),
        closure=dict(complete_local_theorems=report.get("complete_local_theorems"), entry_certificates=report.get("entry_certificates"), edge_certificates=report.get("edge_certificates")))
    verified = completed.returncode == 0 and report["status"] == "verified"
    if not cli_status_consistent(completed.returncode, report["status"]):
        return False, "ERR: V3 CLI exit status disagrees with its report", extra
    return verified, report["message"], extra


def main():
    kind, target, config, *rest = sys.argv[1:]
    out = Path(os.environ["PAPER_WORKER_OUT"])
    started = time.monotonic()
    snapshot = Path.cwd().resolve()
    before = source_pin(snapshot)
    payload = dict(kind=kind, target=target, config=config, verified=False, result="ERR", counterexample=False,
                   snapshot=str(snapshot), source_before=before)
    try:
        expected = EXPECTED_SOURCE_PIN
        if os.environ.get("PAPER_SOURCE_PIN", expected) != expected:
            raise ValueError("jobs require the pinned validator source (source_pin.py)")
        if before != dict(sha256=expected, files=EXPECTED_SOURCE_FILES):
            raise ValueError(f"unexpected snapshot pin: {before}")
        import z3
        if sys.version_info[:2] != (3, 13) or z3.get_version_string() != "4.15.4":  # paper runs: 3.13.7
            raise ValueError("artifact runtime requires Python 3.13.x and Z3 4.15.4")
        payload.update(python_version=sys.version, z3_version=z3.get_version_string(),
                       harness_sha256={name:sha256((Path(__file__).parent/name).read_bytes()).hexdigest()
                           for name in HARNESS_FILES})
        gas = rest[rest.index("--gas") + 1] if "--gas" in rest else ("full" if kind == "lockstep" else "off")
        depth = int(rest[rest.index("--max-depth") + 1]) if "--max-depth" in rest else None
        if depth is not None and depth <= 0:
            raise ValueError("max-depth must be positive")
        pair = input_pair_info(target) if kind in ("program", "lockstep") else {}
        payload.update(pair)
        if pair.get("input_missing_pair"):
            verified, message, extra = False, "N/A: input IR/HEX pair is incomplete", dict(
                raw_status="INPUT_MISSING_PAIR", reason="input_missing_pair", requested=dict(gas_check=gas, max_depth=depth),
                effective=dict(execution_started=False))
            result_class = "N/A"
        else:
            cache = out.with_suffix(".smt.sqlite3")
            if cache.exists():
                raise FileExistsError(f"fresh proof cache required: {cache}")
            os.environ["BLOCK_PROOF_CACHE"] = str(cache)
        if pair.get("input_missing_pair"):
            pass
        elif kind == "lockstep":
            wall = float(rest[rest.index("--wall") + 1]) if "--wall" in rest else 3600.0
            verified, message, extra = run_lockstep(target, config, wall, depth or 400, gas)
            result_class = "VERIFIED" if verified else "ERR" if message.startswith("ERR:") else classify(False, message)
        elif kind == "program":
            selector = int(rest[rest.index("--selector") + 1], 16) if "--selector" in rest else None
            size = int(rest[rest.index("--calldata-size") + 1]) if "--calldata-size" in rest else None
            verified, message, extra = run_program(target, config, selector, size, "--whole" in rest, depth, gas)
            result_class = classify(verified, message)
        elif kind == "single":
            verified, message, extra = run_single(target, config, depth, gas)
            result_class = "VERIFIED" if verified else message.split(":", 1)[0]
        else:
            raise ValueError(f"unknown job kind {kind}")
        if result_class == "UNSUPPORTED":
            result_class = "N/A"
        payload.update(verified=verified, result=result_class, message=message or "", truncated=paper_modes.TRUNCATED[:20],
                       modes=paper_modes.APPLIED, **extra)
        if result_class == "N/A" and "raw_status" not in payload:
            payload.update(raw_status="UNSUPPORTED" if "UNSUPPORTED:" in (message or "") else "VACUOUS",
                           reason="unsupported_execution" if "UNSUPPORTED:" in (message or "") else "vacuous_bounded_intersection")
        if result_class == "N/A":
            payload["verified"] = False
        if (not verified and "do not cover all inputs" not in (message or "")
                and ("COUNTEREXAMPLE" in (message or "") or "solver_result=sat" in (message or ""))):
            payload.update(raw_status="BOUNDED-CEX" if paper_modes.TRUNCATED else "CEX", counterexample=True,
                           counterexample_scope=payload.get("scope", "original verifier reported counterexample"))
        payload["runtime_sources"] = loaded_sources(snapshot)
    except Exception as exc:
        status = exception_status(exc)
        payload.update(result=status, verified=False, message=f"{type(exc).__name__}: {exc}", exception_type=type(exc).__name__)
        if status in ("UNK", "TO"):
            payload.update(raw_status="SUMMARY_PROOF_UNKNOWN", reason=str(getattr(exc, "reason", "unavailable")))
    payload.update(inner_wall_seconds=time.monotonic() - started, source_after=source_pin(snapshot),
                   proof_cache=os.environ.get("BLOCK_PROOF_CACHE"), python=sys.executable,
                   worker_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    if kind == "lockstep":
        payload["proof_cache_scope"] = "parent harness path; CLI effective cache is cli_proof_cache"
    payload["harness_source_after"] = {name:sha256((Path(__file__).parent/name).read_bytes()).hexdigest()
        for name in HARNESS_FILES}
    if payload["source_after"] != before:
        payload.update(result="ERR", verified=False, message="source changed during job")
    if "harness_sha256" in payload and payload["harness_sha256"] != payload["harness_source_after"]:
        payload.update(result="ERR", verified=False, message="harness source changed during job")
    temporary = out.with_suffix(out.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=1))
    temporary.replace(out)


if __name__ == "__main__":
    main()
