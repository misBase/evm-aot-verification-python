"""终止路径 pair 级 等价性检查编排。"""

import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from typing import Optional, Tuple

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Context,
    Goal,
    Not,
    Or,
    Select,
    SolverFor,
    Tactic,
    Then,
    simplify,
    substitute,
    UGE,
    sat,
    unsat,
)

from common.path_observation import PathCoverageCertificate

from utils.z3_helpers import expr_mentions_symbol, get_simplified_bv_const_value

from .equivalence_context import _EquivalenceContext
from .equivalence_outputs import OutputEquivalenceChecks


_Z3_TRANSLATE_LOCK = threading.Lock()
_PATH_FEASIBILITY_RESCUE_LOCK = threading.Lock()
_PATH_FEASIBILITY_RESCUE_ATTEMPTS = 1
_PATH_RESULT_KEYS = (
    "condition",
    "offset",
    "length",
    "memory",
    "base_addr",
    "has_return_data",
    "storage",
    "transient_storage",
    # worker 私有 Context 只翻译这里列出的键，漏键会让 status/gas 比较静默失效。
    "status_code",
    "gas",
)


def _preprocess_partition_query(query, ctx):
    """对具体 partition 查询做轻量预处理。"""
    try:
        goal = Goal(ctx=ctx) if ctx is not None else Goal()
        goal.add(query)
        tactic = (
            Then(
                Tactic("simplify", ctx=ctx),
                Tactic("propagate-values", ctx=ctx),
                Tactic("solve-eqs", ctx=ctx),
            )
            if ctx is not None
            else Then("simplify", "propagate-values", "solve-eqs")
        )
        subgoals = tactic(goal)
        if len(subgoals) != 1:
            return query
        formulas = list(subgoals[0])
        return simplify(And(BoolVal(True, ctx=ctx), *formulas))
    except Exception:
        return query


@dataclass
class _PathPairChunkCheckResult:
    checked_pair_count: int
    verified: bool
    message: Optional[str]
    logs: list[str] = field(default_factory=list)


class PathEquivalenceChecks:
    """终止路径 pair 的编排层：决定走哪条检查路径。

    状态 observable（storage / transient / gas）一律经 outputs 走同一份实现，不再
    各自持有 checker，免得两层各留一套清单。唯一自带的检查是
    ``_check_evm_path_return_memory_against_x86_union``——它把 return/memory 改写成
    对全体 x86 路径的联合坏查询，是 pair 编排特有的对偶问题。
    """

    def __init__(
        self,
        ctx: _EquivalenceContext,
        outputs: OutputEquivalenceChecks,
    ):
        self._ctx = ctx
        self._outputs = outputs

    def check_equivalence_paths(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        path_pair_workers: int = 1,
        skip_feasibility: bool = False,
        evm_coverage: Optional[PathCoverageCertificate] = None,
        x86_coverage: Optional[PathCoverageCertificate] = None,
        coverage_precondition=None,
    ) -> Tuple[bool, Optional[str]]:
        """直接在终止路径 observations 上检查等价性。

        该模式避免先合并完整 terminal memory/storage Array。对每个可行的
        EVM/x86 终止路径交集，证明与 ``check_equivalence`` 相同的 observable
        等价性质。

        Args:
            skip_feasibility: 跳过 ``_check_path_pair_may_be_feasible`` 预检查。
                在符号 calldata 等场景下，feasibility precheck 自身也要 bit-blast
                完整 path 谓词但很少能剪枝；跳过它能少做大约 pair_count 次 SAT 调用。
                等价性检查在 path_condition 为 UNSAT 时返回 unsat（vacuously
                equivalent），仍 sound——只是会把统计的 "feasible pair(s)" 计成全部
                pair_count。
        """
        if path_pair_workers <= 0:
            raise ValueError("path_pair_workers must be a positive integer")

        deadline = time.time() + (self._ctx.timeout_ms / 1000.0)

        if not evm_results:
            return False, "✗ NO TERMINAL PATHS: EVM program produced no terminal state"
        if not x86_results:
            return False, "✗ NO TERMINAL PATHS: x86 program produced no terminal state"

        # 先确认各自的 terminal path 条件覆盖所有输入，再做 pairwise 等价性检查。
        verified, msg = self._check_path_coverage(
            evm_results,
            "EVM",
            deadline,
            evm_coverage,
            coverage_precondition,
        )
        if not verified:
            return False, msg
        verified, msg = self._check_path_coverage(
            x86_results,
            "x86",
            deadline,
            x86_coverage,
            coverage_precondition,
        )
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
            # 并行模式按 EVM path 分批；每个 worker 内复用自己的 Z3 Context/Solver。
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
            "✓ VERIFIED: x86 ≡ EVM over terminal path observations "
            f"({len(evm_results)} EVM path(s), {len(x86_results)} x86 path(s), "
            f"{checked_pair_count}/{pair_count} feasible pair(s))"
        )
        if self._ctx.verbose:
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
        aggregate_memory_verified_evm_paths: set[int] = set()
        for evm_index, evm_result in enumerate(evm_results):
            evm_condition = evm_result.get("condition", BoolVal(True))
            for x86_index, x86_result in enumerate(x86_results):
                x86_condition = x86_result.get("condition", BoolVal(True))
                path_condition = And(evm_condition, x86_condition)
                pair_count += 1
                # 先用 SAT 查询剪掉明显不可行的 path 交集；可选跳过以减少重查询。
                if not skip_feasibility:
                    may_be_feasible, msg = self._check_path_pair_may_be_feasible(
                        path_condition,
                        deadline,
                        f"evm[{evm_index}], x86[{x86_index}]",
                        ctx=None,
                    )
                    if msg is not None:
                        return checked_pair_count, pair_count, msg
                    if not may_be_feasible:
                        continue
                checked_pair_count += 1
                context = f"path pair evm[{evm_index}], x86[{x86_index}]"
                if evm_index in aggregate_memory_verified_evm_paths:
                    # return/memory 已由 aggregate fallback 证明；status 与状态
                    # observable 不在其覆盖范围内，剩余 pair 仍要逐对查。
                    verified, msg = self._check_path_pair_status_and_state_observables(
                        evm_result,
                        x86_result,
                        deadline,
                        path_condition,
                        context,
                    )
                else:
                    verified, msg = self._outputs.check_observables(
                        evm_result,
                        x86_result,
                        deadline,
                        path_condition=path_condition,
                        context=context,
                    )
                if not verified:
                    aggregate_verified = self._check_evm_path_return_memory_against_x86_union(
                        evm_result,
                        x86_results,
                        deadline,
                        f"evm[{evm_index}]",
                    )
                    if aggregate_verified:
                        aggregate_memory_verified_evm_paths.add(evm_index)
                        if self._ctx.verbose:
                            print(
                                f"    ├─ EVM path evm[{evm_index}] aggregate "
                                "x86 return/memory fallback succeeded"
                            )
                        verified, msg = self._check_path_pair_status_and_state_observables(
                            evm_result,
                            x86_result,
                            deadline,
                            path_condition,
                            context,
                        )
                        if verified:
                            continue
                    return checked_pair_count, pair_count, msg
        return checked_pair_count, pair_count, None

    def _check_path_pair_status_and_state_observables(
        self,
        evm_result,
        x86_result,
        deadline: Optional[float],
        path_condition,
        context: str,
    ) -> tuple[bool, Optional[str]]:
        return self._check_path_pair_status_and_state_observables_with_solver(
            self._ctx.solver,
            evm_result,
            x86_result,
            deadline,
            path_condition,
            context,
            logs=None,
            ctx=None,
        )

    def _check_path_pair_status_and_state_observables_with_solver(
        self,
        solver,
        evm_result,
        x86_result,
        deadline: Optional[float],
        path_condition,
        context: str,
        logs: Optional[list[str]] = None,
        ctx=None,
    ) -> tuple[bool, Optional[str]]:
        """检查 path pair 的 status code 与状态 observable（storage / transient / gas）。

        aggregate return/memory fallback 命中后由这条分支接管所有后续 pair，而它只证
        return-presence/length/memory。这两项必须在这里独立再证一遍，否则「pairwise 因
        status 或 gas 失败 → aggregate 成功 → 失败被吞掉」就是假绿（return 长度为 0 时
        aggregate 必然成功，等于什么都没证）。
        """
        verified, msg = self._outputs._check_status_code_with_solver(
            solver,
            evm_result,
            x86_result,
            deadline,
            path_condition,
            context,
            logs,
            ctx,
        )
        if not verified:
            return False, msg

        return self._outputs._check_state_observables_with_solver(
            solver,
            evm_result,
            x86_result,
            deadline,
            path_condition,
            context,
            logs,
            ctx,
        )

    def _check_evm_path_return_memory_against_x86_union(
        self,
        evm_result,
        x86_results: list[dict],
        deadline: Optional[float],
        label: str,
        logs: Optional[list[str]] = None,
        ctx=None,
    ) -> bool:
        """用所有 x86 路径联合证明单条 EVM 终止路径的 fallback。

        pairwise 检查会证明每个可行的 ``evm_i ∧ x86_j`` 交集。部分不可行交集
        会很难判，因为 x86 路径条件含有较大的 merge-origin ``Or/If`` 项。
        这个 fallback 改问对偶问题：在一条 EVM 路径下，是否存在任意 x86
        终止路径产生坏 observable？如果所有这类存在性坏查询都是 UNSAT，则该
        EVM 路径已被完整的 x86 终止路径集合 等价性检查，剩余 pairwise 检查可省略。
        """
        evm_condition = evm_result.get("condition", BoolVal(True, ctx=ctx))
        evm_has_return_data = evm_result.get(
            "has_return_data",
            evm_result["length"] != BitVecVal(0, 64, ctx=ctx),
        )
        evm_length = evm_result["length"]

        def _x86_bad_disjunction(build_bad):
            bad_cases = []
            for x86_result in x86_results:
                x86_condition = x86_result.get("condition", BoolVal(True, ctx=ctx))
                x86_has_return_data = x86_result.get(
                    "has_return_data",
                    x86_result["length"] != BitVecVal(0, 64, ctx=ctx),
                )
                bad_cases.append(And(x86_condition, build_bad(x86_result, x86_has_return_data)))
            return And(evm_condition, Or(*bad_cases))

        if not self._check_union_bad_query_unsat(
            _x86_bad_disjunction(
                lambda _x86_result, x86_has_return_data: (
                    evm_has_return_data != x86_has_return_data
                )
            ),
            deadline,
            f"{label} aggregate return-presence",
            logs=logs,
            ctx=ctx,
        ):
            return False

        if not self._check_union_bad_query_unsat(
            _x86_bad_disjunction(
                lambda x86_result, x86_has_return_data: And(
                    evm_has_return_data,
                    x86_has_return_data,
                    evm_length != x86_result["length"],
                )
            ),
            deadline,
            f"{label} aggregate return-length",
            logs=logs,
            ctx=ctx,
        ):
            return False

        # aggregate fallback 只处理小具体长度 return data；其它情况回到 pairwise。
        concrete_length = get_simplified_bv_const_value(evm_length)
        if concrete_length is None:
            return False
        if concrete_length > self._ctx.tuning.memory_unroll_byte_limit:
            return False

        for byte_index in range(concrete_length):
            index = BitVecVal(byte_index, 64, ctx=ctx)
            evm_byte = Select(evm_result["memory"], evm_result["offset"] + index)
            if not self._check_union_bad_query_unsat(
                _x86_bad_disjunction(
                    lambda x86_result, x86_has_return_data, index=index, evm_byte=evm_byte: And(
                        evm_has_return_data,
                        x86_has_return_data,
                        evm_length == x86_result["length"],
                        evm_byte != Select(
                            x86_result["memory"],
                            x86_result["base_addr"] + x86_result["offset"] + index,
                        ),
                    )
                ),
                deadline,
                f"{label} aggregate memory byte {byte_index}",
                logs=logs,
                ctx=ctx,
            ):
                return False

        return True

    def _check_union_bad_query_unsat(
        self,
        query,
        deadline: Optional[float],
        label: str,
        *,
        timeout_cap_ms: Optional[int] = None,
        logs: Optional[list[str]] = None,
        ctx=None,
    ) -> bool:
        """查询某个 aggregate 坏事件是否不可满足。"""
        solver = SolverFor("QF_AUFBV", ctx=ctx) if ctx is not None else SolverFor("QF_AUFBV")
        cap = (
            self._ctx.tuning.storage_calldatasize_tail_partition_timeout_ms
            if timeout_cap_ms is None
            else timeout_cap_ms
        )
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            cap,
        ):
            return False

        solver.add(query)
        start = time.time()
        result = solver.check()
        solve_time = time.time() - start
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {label}: {solve_time:.3f}s, result={result}",
        )
        return result == unsat

    def _check_path_pairs_parallel(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        deadline: Optional[float],
        path_pair_workers: int,
        skip_feasibility: bool = False,
    ) -> tuple[int, int, Optional[str]]:
        """并行检查 path pairs，按 EVM path 分批提交给 worker。"""
        evm_indices = list(range(len(evm_results)))
        pair_count = len(evm_results) * len(x86_results)
        checked_pair_count = 0
        max_workers = min(path_pair_workers, len(evm_indices))
        target_chunk_count = max_workers * 16
        chunk_size = max(1, (len(evm_indices) + target_chunk_count - 1) // target_chunk_count)
        chunks = [
            evm_indices[start:start + chunk_size]
            for start in range(0, len(evm_indices), chunk_size)
        ]

        if self._ctx.verbose:
            print(
                f"    ├─ Checking {pair_count} path pair(s) with "
                f"{max_workers} worker thread(s), {len(chunks)} EVM-path batch(es)"
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
                if self._ctx.verbose:
                    for line in result.logs:
                        print(line)
                checked_pair_count += result.checked_pair_count
                if not result.verified:
                    if failure_message is None:
                        failure_message = result.message
                        # 一个 worker 找到失败后通知其它 worker 尽快停止后续 pair。
                        cancel_event.set()
                    continue

        return checked_pair_count, pair_count, failure_message

    def _check_path_pair_chunk(
        self,
        evm_indices: list[int],
        evm_results: list[dict],
        x86_results: list[dict],
        deadline: Optional[float],
        cancel_event: threading.Event,
        skip_feasibility: bool = False,
    ) -> _PathPairChunkCheckResult:
        """单个 worker 的 path-pair 批处理逻辑。"""
        ctx = Context()
        solver = SolverFor("QF_AUFBV", ctx=ctx)
        # 多线程下每个 worker 使用独立 Z3 Context；先把 x86 observations 翻译过去。
        evm_cache = {}
        x86_cache = [
            self._translate_path_result(x86_result, ctx)
            for x86_result in x86_results
        ]
        checked_pair_count = 0
        logs: list[str] = []

        for evm_index in evm_indices:
            if cancel_event.is_set():
                return _PathPairChunkCheckResult(checked_pair_count, True, None, logs)

            evm_result = evm_cache.get(evm_index)
            if evm_result is None:
                evm_result = self._translate_path_result(evm_results[evm_index], ctx)
                evm_cache[evm_index] = evm_result

            aggregate_memory_verified = False
            evm_condition = evm_result.get("condition", BoolVal(True, ctx=ctx))
            for x86_index, x86_result in enumerate(x86_cache):
                if cancel_event.is_set():
                    return _PathPairChunkCheckResult(checked_pair_count, True, None, logs)

                label = f"evm[{evm_index}], x86[{x86_index}]"
                x86_condition = x86_result.get("condition", BoolVal(True, ctx=ctx))
                path_condition = And(BoolVal(True, ctx=ctx), evm_condition, x86_condition)

                # worker 内的 feasibility precheck 与串行路径保持同一语义。
                if not skip_feasibility:
                    may_be_feasible, msg = self._check_path_pair_may_be_feasible_with_solver(
                        solver,
                        path_condition,
                        deadline,
                        label,
                        logs,
                        ctx=ctx,
                    )
                    if msg is not None:
                        return _PathPairChunkCheckResult(checked_pair_count, False, msg, logs)
                    if not may_be_feasible:
                        continue

                checked_pair_count += 1
                context = f"path pair {label}"
                if aggregate_memory_verified:
                    # aggregate fallback 覆盖 return/memory 后，status 与状态
                    # observable 仍要逐对查。
                    verified, msg = self._check_path_pair_status_and_state_observables_with_solver(
                        solver,
                        evm_result,
                        x86_result,
                        deadline,
                        path_condition,
                        context,
                        logs=logs,
                        ctx=ctx,
                    )
                else:
                    verified, msg = self._outputs.check_observables_with_solver(
                        solver,
                        evm_result,
                        x86_result,
                        deadline,
                        path_condition=path_condition,
                        context=context,
                        logs=logs,
                        ctx=ctx,
                    )
                if not verified:
                    aggregate_verified = self._check_evm_path_return_memory_against_x86_union(
                        evm_result,
                        x86_cache,
                        deadline,
                        f"evm[{evm_index}]",
                        logs=logs,
                        ctx=ctx,
                    )
                    if aggregate_verified:
                        aggregate_memory_verified = True
                        self._ctx.emit_solver_log(
                            logs,
                            f"    ├─ EVM path evm[{evm_index}] aggregate "
                            "x86 return/memory fallback succeeded",
                        )
                        verified, msg = self._check_path_pair_status_and_state_observables_with_solver(
                            solver,
                            evm_result,
                            x86_result,
                            deadline,
                            path_condition,
                            context,
                            logs=logs,
                            ctx=ctx,
                        )
                        if verified:
                            continue
                    return _PathPairChunkCheckResult(checked_pair_count, False, msg, logs)

        return _PathPairChunkCheckResult(checked_pair_count, True, None, logs)

    @classmethod
    def _translate_path_result(cls, result, ctx):
        """把 observation 中的 Z3 表达式翻译到 worker 私有 Context。"""
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
        coverage: Optional[PathCoverageCertificate] = None,
        precondition=None,
    ) -> Tuple[bool, Optional[str]]:
        """检查 terminal path 条件是否覆盖 precondition 下的所有输入。"""
        if coverage is not None and coverage.complete:
            if self._ctx.verbose:
                source = f" ({coverage.source})" if coverage.source else ""
                print(
                    f"    ├─ {label} terminal path coverage check: "
                    f"0.000s, by-construction{source}: {coverage.reason}"
                )
            return True, None
        if coverage is not None and self._ctx.verbose:
            print(
                f"    ├─ {label} terminal path coverage certificate incomplete: "
                f"{coverage.reason}; falling back to SMT"
            )

        if not self._ctx.reset_solver_with_budget(deadline):
            msg = self._ctx.timeout_message()
            if self._ctx.verbose:
                print(f"    └─ {msg}")
            return False, msg

        conditions = [result.get("condition", BoolVal(True)) for result in path_results]
        if precondition is not None:
            self._ctx.solver.add(precondition)
        # 反例查询：是否存在一个输入不落入任何 terminal path。
        self._ctx.solver.add(Not(Or(*conditions)))

        start_time = time.time()
        result = self._ctx.solver.check()
        solve_time = time.time() - start_time

        if self._ctx.verbose:
            print(f"    ├─ {label} terminal path coverage check: {solve_time:.3f}s, result={result}")

        if result == unsat:
            return True, None
        if result == sat:
            detail = ""
            if coverage is not None and not coverage.complete:
                detail_parts = []
                if coverage.reason:
                    detail_parts.append(f"coverage certificate incomplete: {coverage.reason}")
                if coverage.details:
                    details = ", ".join(
                        f"{key}={value}" for key, value in coverage.details
                    )
                    detail_parts.append(f"details: {details}")
                if detail_parts:
                    detail = " (" + "; ".join(detail_parts) + ")"
            return False, (
                f"✗ COUNTEREXAMPLE: {label} terminal paths do not cover all inputs"
                f"{detail}"
            )
        return False, self._ctx.unknown_message()

    def _check_path_pair_may_be_feasible(
        self,
        path_condition,
        deadline: Optional[float],
        label: str,
        ctx=None,
    ) -> tuple[bool, Optional[str]]:
        return self._check_path_pair_may_be_feasible_with_solver(
            self._ctx.solver,
            path_condition,
            deadline,
            label,
            logs=None,
            ctx=ctx,
        )

    def _check_path_pair_may_be_feasible_with_solver(
        self,
        solver,
        path_condition,
        deadline: Optional[float],
        label: str,
        logs: Optional[list[str]],
        ctx=None,
    ) -> tuple[bool, Optional[str]]:
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            self._ctx.tuning.path_pair_feasibility_timeout_ms,
        ):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return True, msg

        solver.add(path_condition)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ Path pair feasibility {label}: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return False, None
        if result == sat:
            return True, None

        # UNKNOWN 时，换一个全新 Context/Solver 低预算重试，绕开偶发 solver 状态问题。
        for attempt in range(_PATH_FEASIBILITY_RESCUE_ATTEMPTS):
            rescue_ctx = Context()
            rescue_condition = path_condition.translate(rescue_ctx)
            rescue_solver = (
                SolverFor("QF_AUFBV", ctx=rescue_ctx)
            )
            if not self._ctx.reset_solver_with_capped_budget_for(
                rescue_solver,
                self._ctx.timeout_ms,
                deadline,
                self._ctx.tuning.path_pair_feasibility_rescue_timeout_ms,
            ):
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return True, msg

            rescue_solver.add(rescue_condition)
            start_time = time.time()
            with _PATH_FEASIBILITY_RESCUE_LOCK:
                rescue_result = rescue_solver.check()
            solve_time = time.time() - start_time

            retry = f" retry {attempt + 1}" if attempt else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ Path pair feasibility rescue{retry} {label}: "
                f"{solve_time:.3f}s, result={rescue_result}",
            )

            if rescue_result == unsat:
                return False, None
            if rescue_result == sat:
                return True, None
        # rescue 仍不确定时，若依赖 CallDataSize，尝试按 calldata size 分区证明 UNSAT。
        partition_result, msg = self._check_path_pair_calldatasize_partition_unsat(
            path_condition,
            deadline,
            label,
            logs,
        )
        if msg is not None:
            return True, msg
        if partition_result:
            return False, None
        # UNKNOWN 保守处理：不剪掉这个 pair。
        return True, None

    def _check_path_pair_calldatasize_partition_unsat(
        self,
        path_condition,
        deadline: Optional[float],
        label: str,
        logs: Optional[list[str]],
    ) -> tuple[bool, Optional[str]]:
        """对难解可行性查询尝试按 calldata size 穷举切分。"""
        # 不含 CallDataSize 时没有可分区变量，直接放弃该优化。
        if not expr_mentions_symbol(path_condition, "CallDataSize"):
            return False, None

        partition_ctx = Context()
        condition = path_condition.translate(partition_ctx)
        calldata_size = BitVec("CallDataSize", 64, ctx=partition_ctx)
        exact_limit = self._ctx.tuning.path_pair_calldatasize_exact_partition_limit
        exact_timeout_ms = (
            self._ctx.tuning.path_pair_calldatasize_exact_partition_timeout_ms
        )
        tail_timeout_ms = (
            self._ctx.tuning.path_pair_calldatasize_tail_partition_timeout_ms
        )
        total_solve_time = 0.0
        start = time.time()

        def _check_query(query_condition, timeout_ms):
            query_condition = _preprocess_partition_query(
                query_condition,
                partition_ctx,
            )
            solver = SolverFor("QF_AUFBV", ctx=partition_ctx)
            if not self._ctx.reset_solver_with_capped_budget_for(
                solver,
                self._ctx.timeout_ms,
                deadline,
                timeout_ms,
            ):
                return None, 0.0
            solver.add(query_condition)
            query_start = time.time()
            with _PATH_FEASIBILITY_RESCUE_LOCK:
                result = solver.check()
            solve_time = time.time() - query_start
            return result, solve_time

        # 先枚举小的精确 calldata size。
        for i in range(exact_limit):
            size_value = BitVecVal(i, 64, ctx=partition_ctx)
            exact_condition = simplify(
                substitute(condition, (calldata_size, size_value))
            )
            result, solve_time = _check_query(
                exact_condition,
                exact_timeout_ms,
            )
            total_solve_time += solve_time
            if result is None:
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            if result == unsat:
                continue
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ Path pair feasibility calldata-size split {label} "
                f"size={i}: {solve_time:.3f}s, result={result}",
            )
            return False, None

        # 剩余较大的 calldata size 合并成一个尾部分区。
        tail_condition = UGE(
            calldata_size,
            BitVecVal(exact_limit, 64, ctx=partition_ctx),
        )
        result, solve_time = _check_query(
            And(condition, tail_condition),
            tail_timeout_ms,
        )
        total_solve_time += solve_time
        if result is None:
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ Path pair feasibility calldata-size split {label} "
                f"size>={exact_limit}: {solve_time:.3f}s, result={result}",
            )
            return False, None

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ Path pair feasibility calldata-size partition {label}: "
            f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
            "all partitions unsat",
        )
        return True, None
