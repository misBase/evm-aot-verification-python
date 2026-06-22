"""Shared infrastructure for refinement sub-checks.

``_RefinementContext`` 持有所有 refinement check 共用的状态（solver、预算、
verbose、tuning、oracle 缓存）以及消息格式化、求解器预算管理和日志 helper。

三个 check 类（storage / outputs / paths）通过组合持有同一个 context 实例，
而不是经由多继承共享这些方法——依赖因此变得显式且可独立测试。

这里的方法和字段都是**协作接口**：它们刻意以公开名字（无下划线前缀）暴露，
因为 storage / outputs / paths 都直接调用它们。真正的私有实现细节才用下划线。
"""

import threading
import time
from typing import Optional

from z3 import SolverFor, set_option

from common.div_bridge import verified_div_bridges

from .refinement_tuning import _RefinementCheckTuning


class _RefinementContext:
    """三个 refinement check 类共享的状态与协作 helper。"""

    def __init__(
        self,
        timeout_ms: int = 60000,
        verbose: bool = False,
        z3_verbose: bool = False,
    ):
        self.timeout_ms = timeout_ms
        self.verbose = verbose
        self.tuning = _RefinementCheckTuning.for_timeout(timeout_ms)

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
        self.unsat_oracle_cache: dict[tuple[int, int], list[tuple[object, bool]]] = {}
        self.unsat_oracle_cache_lock = threading.Lock()

    # --- 消息格式化 ---

    @staticmethod
    def timeout_message_for(timeout_ms: int) -> str:
        return f"? TIMEOUT: Solver exceeded overall timeout ({timeout_ms} ms)"

    def timeout_message(self) -> str:
        return self.timeout_message_for(self.timeout_ms)

    @staticmethod
    def unknown_message_for_solver(solver, timeout_ms: int) -> str:
        reason = solver.reason_unknown()
        if reason == "timeout":
            return _RefinementContext.timeout_message_for(timeout_ms)
        if reason:
            return f"? UNKNOWN: Solver could not determine refinement (reason: {reason})"
        return "? UNKNOWN: Solver could not determine refinement"

    def unknown_message(self) -> str:
        return self.unknown_message_for_solver(self.solver, self.timeout_ms)

    @staticmethod
    def context_prefix(context: str) -> str:
        return f"{context}: " if context else ""

    @staticmethod
    def observable_counterexample_message(
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

    # --- 求解器预算管理 ---

    @staticmethod
    def reset_solver_with_budget_for(
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
    def reset_solver_with_capped_budget_for(
        solver,
        timeout_ms: int,
        deadline: Optional[float],
        cap_ms: Optional[int],
    ) -> bool:
        if not _RefinementContext.reset_solver_with_budget_for(solver, timeout_ms, deadline):
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

    def reset_solver_with_budget(self, deadline: Optional[float]) -> bool:
        """重置共享求解器并为本次 check 设置剩余预算。"""
        return self.reset_solver_with_budget_for(self.solver, self.timeout_ms, deadline)

    # --- SDIV/SMOD 除法桥接（refinement 提速，soundness 中性） ---

    def add_div_bridges(
        self,
        solver,
        evm_exprs,
        x86_exprs,
        constraint,
        assumptions=(),
        ctx=None,
    ) -> None:
        """把已验证的 EVM↔x86 除法桥接 add 到 solver（fail-closed，纯提速）。

        SDIV/SMOD（先取负再除）的路径里，EVM 与 x86 对同一无符号除法的建模 AST 不同，
        要证两个 256-bit bvudiv 相等会 bit-blast 而 unknown。这里逐对配对两侧除法子
        表达式、先证实参在 constraint 下恒等，再注入 `evm_div == x86_div`（恒真）让
        solver 跳过 bit-blast。验证 fail-closed：未证实参恒等的对绝不注入。

        与单指令测试侧 (_path_observation_mismatches) 用同一 common.div_bridge 实现，
        保证生产合约级验证与测试同源受益。
        """
        bridges = verified_div_bridges(
            evm_exprs,
            x86_exprs,
            constraint,
            assumptions=assumptions,
            ctx=ctx,
        )
        for bridge in bridges:
            solver.add(bridge)

    # --- 日志 ---

    def emit_solver_log(self, logs: Optional[list[str]], line: str) -> None:
        if not self.verbose:
            return
        if logs is None:
            print(line)
        else:
            logs.append(line)
