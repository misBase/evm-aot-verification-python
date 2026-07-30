"""
用于验证x86和EVM语义之间精化关系的精化检查器。

验证x86精化EVM：对所有输入，x86_output = EVM_output。

``RefinementChecker`` 本身是一个薄门面：它装配共享的 ``_RefinementContext``
以及四个按职责拆分的 check 对象（storage / memory / outputs / paths），并把
对外的公共方法委托给它们。check 对象之间通过构造期注入显式声明依赖
（outputs→{storage,memory}，paths→{outputs,storage,memory}），而不是经由
多继承隐式共享方法。
"""

from typing import Optional, Tuple

from .refinement_context import _RefinementContext
from .refinement_gas import GasEquivalenceChecks
from .refinement_memory import MemoryContentChecks
from .refinement_outputs import OutputRefinementChecks
from .refinement_paths import PathRefinementChecks, _PathPairChunkCheckResult
from .refinement_storage import StorageEquivalenceChecks


class RefinementChecker:
    """检查x86和EVM语义之间的精化关系。

    验证x86精化EVM：对所有输入，x86_output = EVM_output。
    """

    def __init__(
        self,
        timeout_ms: int = 60000,
        verbose: bool = False,
        z3_verbose: bool = False,
        check_gas: bool = False,
    ):
        """初始化精化检查器。

        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用应用层详细输出（subcheck 时间、path-pair 进度等）
            z3_verbose: 是否同时打开 z3 自身的 verbose（极吵；默认关，避免淹没
                应用层日志）。perf 调试用 verbose=True, z3_verbose=False。
            check_gas: 是否启用 gas 终值一致性检查（阶段 0）。默认 False：
                gas 检查只覆盖静态 gas，对含动态 gas 指令（MSTORE/RETURN/CALL
                等）的程序会 SAT；且许多测试桩 hex 不含 gas codegen。需显式
                开启（配合纯静态 gas fixture），避免破坏既有功能等价验证。
        """
        self._ctx = _RefinementContext(timeout_ms, verbose, z3_verbose)
        self._storage = StorageEquivalenceChecks(self._ctx)
        self._memory = MemoryContentChecks(self._ctx)
        # gas 检查默认关闭：check_gas=False 时 _gas=None，所有 gas 检查点
        # （均写了 `if self._gas is not None`）静默跳过。
        self._gas = GasEquivalenceChecks(self._ctx) if check_gas else None
        self._outputs = OutputRefinementChecks(
            self._ctx, self._storage, self._memory, self._gas
        )
        self._paths = PathRefinementChecks(
            self._ctx,
            self._outputs,
            self._storage,
            self._memory,
            self._gas,
        )

    # --- 共享状态的只读转发（外部代码与测试直接读取这些 knob）---

    @property
    def timeout_ms(self) -> int:
        return self._ctx.timeout_ms

    @property
    def verbose(self) -> bool:
        return self._ctx.verbose

    @property
    def solver(self):
        return self._ctx.solver

    @property
    def path_pair_feasibility_timeout_ms(self) -> int:
        return self._ctx.tuning.path_pair_feasibility_timeout_ms

    @property
    def storage_quick_timeout_ms(self) -> int:
        return self._ctx.tuning.storage_quick_timeout_ms

    @property
    def storage_calldatasize_exact_partition_limit(self) -> int:
        return self._ctx.tuning.storage_calldatasize_exact_partition_limit

    @property
    def storage_calldatasize_exact_partition_timeout_ms(self) -> int:
        return self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms

    @property
    def storage_calldatasize_tail_partition_timeout_ms(self) -> int:
        return self._ctx.tuning.storage_calldatasize_tail_partition_timeout_ms

    def _timeout_message(self) -> str:
        return self._ctx.timeout_message()

    # --- 对外公共检查方法（委托给各职责对象）---

    def check_refinement(self, evm_result, x86_result, assumptions=None):
        return self._outputs.check_refinement(evm_result, x86_result, assumptions)

    def check_stack_equivalence(
        self,
        evm_state,
        x86_state,
        initial_state,
        n_elements: int = 2,
        deadline: Optional[float] = None,
    ) -> Tuple[bool, Optional[str]]:
        return self._outputs.check_stack_equivalence(
            evm_state, x86_state, initial_state, n_elements, deadline,
        )

    def check_refinement_paths(
        self,
        evm_results,
        x86_results,
        path_pair_workers: int = 1,
        skip_feasibility: bool = False,
        evm_coverage=None,
        x86_coverage=None,
        coverage_precondition=None,
    ) -> Tuple[bool, Optional[str]]:
        return self._paths.check_refinement_paths(
            evm_results,
            x86_results,
            path_pair_workers,
            skip_feasibility,
            evm_coverage=evm_coverage,
            x86_coverage=x86_coverage,
            coverage_precondition=coverage_precondition,
        )

    def _check_storage_equivalence(
        self,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        return self._storage._check_storage_equivalence(
            evm_storage, x86_storage, deadline, path_condition, context,
        )

    def _check_transient_storage_equivalence(
        self,
        evm_ts,
        x86_ts,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        return self._storage._check_transient_storage_equivalence(
            evm_ts, x86_ts, deadline, path_condition, context,
        )


__all__ = ["RefinementChecker", "_PathPairChunkCheckResult"]
