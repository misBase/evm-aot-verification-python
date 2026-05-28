"""Terminal path-pair refinement orchestration."""

import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from typing import Optional, Tuple

from z3 import (
    And,
    BoolVal,
    Context,
    Not,
    Or,
    SolverFor,
    sat,
    unsat,
)


_Z3_TRANSLATE_LOCK = threading.Lock()
_PATH_RESULT_KEYS = (
    "condition",
    "offset",
    "length",
    "memory",
    "base_addr",
    "has_return_data",
    "storage",
    "transient_storage",
)


@dataclass
class _PathPairChunkCheckResult:
    checked_pair_count: int
    verified: bool
    message: Optional[str]
    logs: list[str] = field(default_factory=list)


class PathRefinementChecks:
    def check_refinement_paths(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        path_pair_workers: int = 1,
        skip_feasibility: bool = False,
    ) -> Tuple[bool, Optional[str]]:
        """Check refinement directly over terminal path observations.

        This avoids first merging whole terminal memory/storage arrays.  For each
        feasible EVM/x86 terminal-path intersection, it proves the same
        observable properties as ``check_refinement``.

        Args:
            skip_feasibility: 跳过 ``_check_path_pair_may_be_feasible`` 预检查。
                在符号 calldata 等场景下，feasibility precheck 自身也要 bit-blast
                完整 path 谓词但很少能剪枝；跳过它能少做大约 pair_count 次 SAT 调用。
                refinement check 在 path_condition 为 UNSAT 时返回 unsat（vacuously
                refined），仍 sound——只是会把统计的 "feasible pair(s)" 计成全部
                pair_count。
        """
        if path_pair_workers <= 0:
            raise ValueError("path_pair_workers must be a positive integer")

        deadline = time.time() + (self.timeout_ms / 1000.0)

        if not evm_results:
            return False, "✗ NO TERMINAL PATHS: EVM program produced no terminal state"
        if not x86_results:
            return False, "✗ NO TERMINAL PATHS: x86 program produced no terminal state"

        verified, msg = self._check_path_coverage(evm_results, "EVM", deadline)
        if not verified:
            return False, msg
        verified, msg = self._check_path_coverage(x86_results, "x86", deadline)
        if not verified:
            return False, msg

        if path_pair_workers == 1:
            checked_pair_count, pair_count, failure = self._check_path_pairs_sequential(
                evm_results,
                x86_results,
                deadline,
                skip_feasibility=skip_feasibility,
            )
        else:
            checked_pair_count, pair_count, failure = self._check_path_pairs_parallel(
                evm_results,
                x86_results,
                deadline,
                path_pair_workers,
                skip_feasibility=skip_feasibility,
            )
        if failure is not None:
            return False, failure

        msg = (
            "✓ VERIFIED: x86 refines EVM over terminal path observations "
            f"({len(evm_results)} EVM path(s), {len(x86_results)} x86 path(s), "
            f"{checked_pair_count}/{pair_count} feasible pair(s))"
        )
        if self.verbose:
            print(f"    └─ {msg}")
        return True, msg

    def _check_path_pairs_sequential(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        deadline: Optional[float],
        skip_feasibility: bool = False,
    ) -> tuple[int, int, Optional[str]]:
        pair_count = 0
        checked_pair_count = 0
        for evm_index, evm_result in enumerate(evm_results):
            evm_condition = evm_result.get("condition", BoolVal(True))
            for x86_index, x86_result in enumerate(x86_results):
                x86_condition = x86_result.get("condition", BoolVal(True))
                path_condition = And(evm_condition, x86_condition)
                pair_count += 1
                if not skip_feasibility:
                    may_be_feasible, msg = self._check_path_pair_may_be_feasible(
                        path_condition,
                        deadline,
                        f"evm[{evm_index}], x86[{x86_index}]",
                    )
                    if msg is not None:
                        return checked_pair_count, pair_count, msg
                    if not may_be_feasible:
                        continue
                checked_pair_count += 1
                verified, msg = self._check_refinement_direct_memory(
                    evm_result,
                    x86_result,
                    deadline,
                    path_condition=path_condition,
                    context=f"path pair evm[{evm_index}], x86[{x86_index}]",
                )
                if not verified:
                    return checked_pair_count, pair_count, msg
        return checked_pair_count, pair_count, None

    def _check_path_pairs_parallel(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        deadline: Optional[float],
        path_pair_workers: int,
        skip_feasibility: bool = False,
    ) -> tuple[int, int, Optional[str]]:
        pair_specs = [
            (evm_index, x86_index)
            for evm_index, evm_result in enumerate(evm_results)
            for x86_index, x86_result in enumerate(x86_results)
        ]
        pair_count = len(pair_specs)
        checked_pair_count = 0
        max_workers = min(path_pair_workers, pair_count)
        chunks = [
            pair_specs[worker_index::max_workers]
            for worker_index in range(max_workers)
        ]

        if self.verbose:
            print(
                f"    ├─ Checking {pair_count} path pair(s) with "
                f"{max_workers} worker thread(s)"
            )

        failure_message = None
        cancel_event = threading.Event()
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [
                executor.submit(
                    self._check_path_pair_chunk,
                    chunk,
                    evm_results,
                    x86_results,
                    deadline,
                    cancel_event,
                    skip_feasibility,
                )
                for chunk in chunks
            ]
            for future in as_completed(futures):
                result = future.result()
                if self.verbose:
                    for line in result.logs:
                        print(line)
                checked_pair_count += result.checked_pair_count
                if not result.verified:
                    if failure_message is None:
                        failure_message = result.message
                        cancel_event.set()
                    continue

        return checked_pair_count, pair_count, failure_message

    def _check_path_pair_chunk(
        self,
        pair_specs: list[tuple[int, int]],
        evm_results: list[dict],
        x86_results: list[dict],
        deadline: Optional[float],
        cancel_event: threading.Event,
        skip_feasibility: bool = False,
    ) -> _PathPairChunkCheckResult:
        ctx = Context()
        solver = SolverFor("QF_AUFBV", ctx=ctx)
        evm_cache = {}
        x86_cache = {}
        checked_pair_count = 0
        logs: list[str] = []

        for evm_index, x86_index in pair_specs:
            if cancel_event.is_set():
                return _PathPairChunkCheckResult(checked_pair_count, True, None, logs)

            evm_result = evm_cache.get(evm_index)
            if evm_result is None:
                evm_result = self._translate_path_result(evm_results[evm_index], ctx)
                evm_cache[evm_index] = evm_result
            x86_result = x86_cache.get(x86_index)
            if x86_result is None:
                x86_result = self._translate_path_result(x86_results[x86_index], ctx)
                x86_cache[x86_index] = x86_result

            label = f"evm[{evm_index}], x86[{x86_index}]"
            path_condition = And(BoolVal(True, ctx=ctx), evm_result["condition"], x86_result["condition"])

            if not skip_feasibility:
                may_be_feasible, msg = self._check_path_pair_may_be_feasible_with_solver(
                    solver,
                    path_condition,
                    deadline,
                    label,
                    logs,
                )
                if msg is not None:
                    return _PathPairChunkCheckResult(checked_pair_count, False, msg, logs)
                if not may_be_feasible:
                    continue

            checked_pair_count += 1
            verified, msg = self._check_refinement_direct_memory_with_solver(
                solver,
                evm_result,
                x86_result,
                deadline,
                path_condition=path_condition,
                context=f"path pair {label}",
                logs=logs,
                ctx=ctx,
            )
            if not verified:
                return _PathPairChunkCheckResult(checked_pair_count, False, msg, logs)

        return _PathPairChunkCheckResult(checked_pair_count, True, None, logs)

    @classmethod
    def _translate_path_result(cls, result, ctx):
        translated = {}
        with _Z3_TRANSLATE_LOCK:
            for key in _PATH_RESULT_KEYS:
                try:
                    value = result[key]
                except KeyError:
                    continue
                translated[key] = cls._translate_z3_value(value, ctx)
        if "condition" not in translated:
            translated["condition"] = BoolVal(True, ctx=ctx)
        return translated

    @staticmethod
    def _translate_z3_value(value, ctx):
        if value is None:
            return None
        translate = getattr(value, "translate", None)
        if translate is None:
            return value
        return translate(ctx)

    def _check_path_coverage(
        self,
        path_results: list[dict],
        label: str,
        deadline: Optional[float],
    ) -> Tuple[bool, Optional[str]]:
        if not self._reset_solver_with_budget(deadline):
            msg = self._timeout_message()
            if self.verbose:
                print(f"    └─ {msg}")
            return False, msg

        conditions = [result.get("condition", BoolVal(True)) for result in path_results]
        self.solver.add(Not(Or(*conditions)))

        start_time = time.time()
        result = self.solver.check()
        solve_time = time.time() - start_time

        if self.verbose:
            print(f"    ├─ {label} terminal path coverage check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            return True, None
        if result == sat:
            return False, f"✗ COUNTEREXAMPLE: {label} terminal paths do not cover all inputs"
        return False, self._unknown_message()

    def _check_path_pair_may_be_feasible(
        self,
        path_condition,
        deadline: Optional[float],
        label: str,
    ) -> tuple[bool, Optional[str]]:
        return self._check_path_pair_may_be_feasible_with_solver(
            self.solver,
            path_condition,
            deadline,
            label,
            logs=None,
        )

    def _check_path_pair_may_be_feasible_with_solver(
        self,
        solver,
        path_condition,
        deadline: Optional[float],
        label: str,
        logs: Optional[list[str]],
    ) -> tuple[bool, Optional[str]]:
        if not self._reset_solver_with_capped_budget_for(
            solver,
            self.timeout_ms,
            deadline,
            self._tuning.path_pair_feasibility_timeout_ms,
        ):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return True, msg

        solver.add(path_condition)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        self._emit_solver_log(
            logs,
            f"    ├─ Path pair feasibility {label}: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return False, None
        if result == sat:
            return True, None
        # UNKNOWN is handled conservatively: do not prune the pair.
        return True, None
