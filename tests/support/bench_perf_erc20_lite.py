"""Benchmark harness for test_verify_perf_erc20_lite_program_pair.

Runs the full-symbolic verification (calldatasize symbolic) with explicit
phase timings.  Used during the perf-investigation; not part of pytest.

Usage:
    poetry run python -m tests.support.bench_perf_erc20_lite \
        --timeout-ms 600000 [--path-observations] [--workers N]
"""
from __future__ import annotations

import argparse
import os
import sys
import time

from evm_ir.program import EVMProgram
from evm_ir.json_parser import load_ir_from_json
from state.smt_state import SMTState
from verification.program_verifier import ProgramEquivalenceChecker
from x86_64.program import X86Program


def _flush_print(*args, **kwargs):
    print(*args, **kwargs)
    sys.stdout.flush()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=600_000)
    parser.add_argument("--path-observations", action="store_true")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--calldata-size", type=int, default=None,
                        help="fix calldatasize to this many bytes; default = symbolic")
    parser.add_argument("--no-verbose", action="store_true",
                        help="suppress phase prints and z3 verbose")
    parser.add_argument("--no-reachability", action="store_true",
                        help="disable x86 reachability check (faster build, more paths)")
    parser.add_argument("--reach-timeout-ms", type=int, default=50,
                        help="reachability check per-call timeout (default 50)")
    parser.add_argument("--calldatasize-max", type=lambda x: int(x, 0), default=None,
                        help="add precondition calldatasize <= N (e.g. 0xFFFFFFFF)")
    parser.add_argument("--enable-merge", action="store_true",
                        help="enable x86 confluence-point state merging (CFG path explosion)")
    parser.add_argument("--skip-feasibility", action="store_true",
                        help="skip path-pair feasibility precheck (sound, refinement check fast-fails on infeasible pairs)")
    parser.add_argument("--profile-subchecks", action="store_true",
                        help="enable verbose subcheck timing on the refinement checker")
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    ir_path = os.path.join(repo_root, "tests/data/perf_erc20_lite.json")
    x86_path = os.path.join(repo_root, "tests/data/perf_erc20_lite.hex")

    compiler_result = load_ir_from_json(ir_path)
    evm_program = EVMProgram(compiler_result)

    with open(x86_path, "r", encoding="utf-8") as f:
        x86_hex_sequence = f.read().strip()
    x86_program = X86Program.from_hex(x86_hex_sequence, base_addr=0)

    # IMPORTANT: ProgramEquivalenceChecker(verbose=True) implies
    # z3.set_option(verbose=10), which dumps the z3 tactic chatter to stdout
    # and drowns out our phase prints.  Keep verbose=False and emit our own
    # timing markers via the helpers below.
    checker = ProgramEquivalenceChecker(
        timeout_ms=args.timeout_ms, verbose=args.profile_subchecks,
    )
    initial_state = SMTState.create_initial_state(
        calldata_size_bytes=args.calldata_size,
    )

    # Optional global precondition: bound symbolic calldatasize.  Stored on
    # the initial_state so downstream solvers (reachability + final refinement)
    # see it as part of the assertion set.
    if args.calldatasize_max is not None:
        from z3 import BitVecVal, ULE
        bound = BitVecVal(args.calldatasize_max, 64)
        initial_state.assumptions = list(initial_state.assumptions or []) + [
            ULE(initial_state.calldatasize, bound)
        ]
        _flush_print(f"[bench] added precondition: calldatasize <= {hex(args.calldatasize_max)}")

    _flush_print(
        f"--- bench start: timeout_ms={args.timeout_ms} "
        f"path_observations={args.path_observations} workers={args.workers} "
        f"calldata_size={args.calldata_size}"
    )

    # Manually walk the two construction phases so we can record their wall
    # times even in non-path-observation mode.
    from verification.call_site_mapping import build_call_site_mapping

    t0 = time.time()
    evm_state, evm_result = evm_program.to_z3(initial_state)
    t_evm = time.time() - t0
    _flush_print(f"[phase] EVM to_z3 build wall: {t_evm:.3f}s")

    t1 = time.time()
    call_site_mapping = build_call_site_mapping(evm_program, x86_program)
    # Wire instrumentation: monkey-patch executor to capture totals.
    import x86_64.cfg_executor as _ce
    stats_holder = {}
    orig_execute = _ce.X86SymbolicExecutor.execute
    def _wrapped_execute(self, *a, **kw):
        out = orig_execute(self, *a, **kw)
        stats_holder["reachability_call_count"] = self.reachability_call_count
        stats_holder["reachability_total_wall"] = self.reachability_total_wall
        stats_holder["reachability_pruned_count"] = self.reachability_pruned_count
        stats_holder["total_states"] = self.total_states
        stats_holder["final_state_count"] = len(self.final_states)
        return out
    _ce.X86SymbolicExecutor.execute = _wrapped_execute
    try:
        x86_state, x86_result = x86_program.to_z3(
            initial_state,
            call_site_mapping=call_site_mapping,
            use_reachability_check=not args.no_reachability,
            reachability_timeout_ms=args.reach_timeout_ms,
            enable_merge=args.enable_merge,
        )
    finally:
        _ce.X86SymbolicExecutor.execute = orig_execute
    t_x86 = time.time() - t1
    _flush_print(
        f"[phase] x86 to_z3 build wall: {t_x86:.3f}s  (call_site={len(call_site_mapping)})"
    )
    if stats_holder:
        _flush_print(
            "[phase]   reachability stats: "
            f"calls={stats_holder.get('reachability_call_count', 0)} "
            f"total_wall={stats_holder.get('reachability_total_wall', 0.0):.3f}s "
            f"pruned={stats_holder.get('reachability_pruned_count', 0)} "
            f"total_states={stats_holder.get('total_states', 0)} "
            f"finals={stats_holder.get('final_state_count', 0)}"
        )

    if args.path_observations:
        # path_observations mode: rebuild via to_z3_paths so we have per-path
        # observations (the previous to_z3 call was only for stats). With
        # enable_merge=True this is just another ~16s.
        t2_pre = time.time()
        evm_paths = evm_program.to_z3_paths(initial_state)
        x86_paths = x86_program.to_z3_paths(
            initial_state,
            call_site_mapping=call_site_mapping,
            use_reachability_check=not args.no_reachability,
            reachability_timeout_ms=args.reach_timeout_ms,
            enable_merge=args.enable_merge,
        )
        _flush_print(
            f"[phase] path_obs build wall: {time.time()-t2_pre:.3f}s "
            f"(evm finals={len(evm_paths.observations)}, x86 finals={len(x86_paths.observations)})"
        )
        # Inject assumptions into each observation's path condition.
        from dataclasses import replace as _dc_replace
        from z3 import And as _And
        assumptions_list = list(initial_state.assumptions or [])
        for paths in (evm_paths, x86_paths):
            for gs in getattr(paths, 'global_states', None) or []:
                for a in getattr(gs.mstate, 'assumptions', None) or []:
                    assumptions_list.append(a)
        seen = set()
        dedup = []
        for a in assumptions_list:
            k = a.hash()
            if k in seen:
                continue
            seen.add(k)
            dedup.append(a)
        evm_obs = evm_paths.observations
        x86_obs = x86_paths.observations
        if dedup:
            evm_obs = [_dc_replace(o, condition=_And(o.condition, *dedup)) for o in evm_obs]
            x86_obs = [_dc_replace(o, condition=_And(o.condition, *dedup)) for o in x86_obs]
        t2 = time.time()
        if args.workers == 1:
            verified, msg = checker.refinement_checker.check_refinement_paths(
                evm_obs, x86_obs,
                skip_feasibility=args.skip_feasibility,
            )
        else:
            verified, msg = checker.refinement_checker.check_refinement_paths(
                evm_obs, x86_obs,
                path_pair_workers=args.workers,
                skip_feasibility=args.skip_feasibility,
            )
        t_check = time.time() - t2
        _flush_print(
            f"[phase] refinement_paths check wall: {t_check:.3f}s "
            f"(workers={args.workers})"
        )
    else:
        t2 = time.time()
        assumptions_list = initial_state.assumptions or []
        # 也把 final state 上累积的 assumption（CALLDATALOAD 处追加的）取出来一并加进
        # 顶层 precondition；evm_state/x86_state.assumptions 在各自 program.to_z3
        # 结尾被合并到 merged_state.assumptions。
        for st in (evm_state, x86_state):
            for a in getattr(st, 'assumptions', None) or []:
                assumptions_list.append(a)
        # de-dup
        seen = set()
        dedup = []
        for a in assumptions_list:
            k = a.hash()
            if k in seen:
                continue
            seen.add(k)
            dedup.append(a)
        if dedup:
            from z3 import And, BoolVal
            precondition = And(BoolVal(True), *dedup)
        else:
            precondition = None
        verified, msg = checker.refinement_checker.check_refinement(
            evm_result, x86_result, assumptions=precondition,
        )
        t_check = time.time() - t2
        _flush_print(f"[phase] refinement check wall: {t_check:.3f}s")

    total = t_evm + t_x86 + t_check
    _flush_print(f"--- bench done: verified={verified} total={total:.3f}s")
    _flush_print(f"--- message: {msg}")
    return 0 if verified else 1


if __name__ == "__main__":
    raise SystemExit(main())
