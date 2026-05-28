"""
用于验证x86和EVM语义之间精化关系的精化检查器。

验证x86精化EVM：对所有输入，x86_output = EVM_output。
"""

import threading
import time
from typing import Optional

from z3 import SolverFor, set_option

from .refinement_outputs import OutputRefinementChecks
from .refinement_paths import PathRefinementChecks, _PathPairChunkCheckResult
from .refinement_storage import StorageEquivalenceChecks, _RefinementCheckTuning


class RefinementChecker(
    PathRefinementChecks,
    OutputRefinementChecks,
    StorageEquivalenceChecks,
):
    """检查x86和EVM语义之间的精化关系。

    验证x86精化EVM：对所有输入，x86_output = EVM_output。
    """

    def __init__(
        self,
        timeout_ms: int = 60000,
        verbose: bool = False,
        z3_verbose: bool = False,
    ):
        """初始化精化检查器。

        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用应用层详细输出（subcheck 时间、path-pair 进度等）
            z3_verbose: 是否同时打开 z3 自身的 verbose（极吵；默认关，避免淹没
                应用层日志）。perf 调试用 verbose=True, z3_verbose=False。
        """
        self.timeout_ms = timeout_ms
        self.verbose = verbose
        self._tuning = _RefinementCheckTuning.for_timeout(timeout_ms)

        # NOTE: Z3 set_option 是全局设置。这里显式在每个实例中设置，避免
        # 前一个 verbose=True 的测试污染后续 verbose=False 的测试。
        set_option(verbose=10 if z3_verbose else 0)
        set_option(proof=bool(z3_verbose))

        # 使用QF_AUFBV（数组、未解释函数、位向量）以支持Array比较
        # QF_BV不支持Arrays，所以我们需要QF_AUFBV
        self.solver = SolverFor("QF_AUFBV")
        self.solver.set("timeout", timeout_ms)

        # path-aware structural fast path 用的小型结果缓存。key 包含 context
        # identity 和 expr.hash()；hash 只用于分桶，复用结果前必须再用 z3.eq
        # 确认是同一个 AST，避免 hash collision 或 cross-context AST 混用。
        self._unsat_oracle_cache: dict[tuple[int, int], list[tuple[object, bool]]] = {}
        self._unsat_oracle_cache_lock = threading.Lock()

        # Backward-compatible aliases for tests or ad-hoc debug scripts that
        # inspect these knobs directly.  New code should read from _tuning.
        self.path_pair_feasibility_timeout_ms = (
            self._tuning.path_pair_feasibility_timeout_ms
        )
        self.storage_quick_timeout_ms = self._tuning.storage_quick_timeout_ms
        self.storage_calldatasize_exact_partition_limit = (
            self._tuning.storage_calldatasize_exact_partition_limit
        )
        self.storage_calldatasize_exact_partition_timeout_ms = (
            self._tuning.storage_calldatasize_exact_partition_timeout_ms
        )
        self.storage_calldatasize_tail_partition_timeout_ms = (
            self._tuning.storage_calldatasize_tail_partition_timeout_ms
        )

    @staticmethod
    def _timeout_message_for(timeout_ms: int) -> str:
        return f"? TIMEOUT: Solver exceeded overall timeout ({timeout_ms} ms)"

    def _timeout_message(self) -> str:
        return self._timeout_message_for(self.timeout_ms)

    @staticmethod
    def _unknown_message_for_solver(solver, timeout_ms: int) -> str:
        reason = solver.reason_unknown()
        if reason == "timeout":
            return RefinementChecker._timeout_message_for(timeout_ms)
        if reason:
            return f"? UNKNOWN: Solver could not determine refinement (reason: {reason})"
        return "? UNKNOWN: Solver could not determine refinement"

    def _unknown_message(self) -> str:
        return self._unknown_message_for_solver(self.solver, self.timeout_ms)

    @staticmethod
    def _reset_solver_with_budget_for(
        solver,
        timeout_ms: int,
        deadline: Optional[float],
    ) -> bool:
        now = time.time()
        if deadline is not None and now >= deadline:
            return False

        solver.reset()
        if deadline is None:
            solver_timeout_ms = timeout_ms
        else:
            solver_timeout_ms = int((deadline - now) * 1000)
            solver_timeout_ms = max(solver_timeout_ms, 1)
        solver.set("timeout", solver_timeout_ms)
        return True

    @staticmethod
    def _reset_solver_with_capped_budget_for(
        solver,
        timeout_ms: int,
        deadline: Optional[float],
        cap_ms: Optional[int],
    ) -> bool:
        if not RefinementChecker._reset_solver_with_budget_for(solver, timeout_ms, deadline):
            return False
        if cap_ms is not None and cap_ms > 0:
            now = time.time()
            if deadline is None:
                effective = min(timeout_ms, cap_ms)
            else:
                remaining_ms = max(int((deadline - now) * 1000), 1)
                effective = min(timeout_ms, remaining_ms, cap_ms)
            solver.set("timeout", max(effective, 1))
        return True

    def _reset_solver_with_budget(self, deadline: Optional[float]) -> bool:
        """重置求解器并为本次 check 设置剩余预算。"""
        return self._reset_solver_with_budget_for(self.solver, self.timeout_ms, deadline)

    @staticmethod
    def _context_prefix(context: str) -> str:
        return f"{context}: " if context else ""

    @staticmethod
    def _observable_counterexample_message(
        observable_name: str,
        context: str = "",
        detail: str = "",
    ) -> str:
        msg = (
            f"✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
            f"({observable_name} differs)"
        )
        qualifiers = [part for part in (context, detail) if part]
        if qualifiers:
            msg = f"{msg} ({', '.join(qualifiers)})"
        return msg

    def _emit_solver_log(self, logs: Optional[list[str]], line: str) -> None:
        if not self.verbose:
            return
        if logs is None:
            print(line)
        else:
            logs.append(line)


__all__ = ["RefinementChecker", "_PathPairChunkCheckResult"]
