"""Gas 消耗一致性检查（阶段 0:终值逐路径等式）。

与 storage/transient 检查平级（组合注入到 RefinementChecker / PathRefinementChecks），
证明同一符号初始 gas G 下，EVM 侧 evm_gas.Gas 与 x86 侧 callengine_gas_remaining
在每条终止路径上相等。

比较语义 = 等式（bisimulation）:反例查询 `evm_gas != x86_gas` 求 UNSAT。
- UNSAT  → gas 等价
- SAT    → 反例（两侧 gas 不同）
- UNKNOWN→ fail-closed（超时/求解器复杂度，按失败处理，保证 soundness）

为将来 status code 一致性检查留平行结构（参见计划「不要做的简化」）。
"""

from typing import Optional

from z3 import sat, unsat, BoolVal


class GasEquivalenceChecks:
    """EVM↔x86 gas 终值等价检查。

    用组合：接收共享的 _RefinementContext（solver/timeout/日志 helper）。
    """

    def __init__(self, ctx):
        self._ctx = ctx

    def _check_gas_equivalence(
        self,
        evm_gas,
        x86_gas,
        deadline: Optional[float] = None,
        path_condition=None,
        context: str = "",
        logs: Optional[list] = None,
    ):
        """用共享 ctx solver 检查 gas 终值等价（门面/串行路径）。"""
        return self._check_gas_equivalence_with_solver(
            self._ctx.solver,
            evm_gas,
            x86_gas,
            deadline,
            path_condition,
            context,
            logs,
            ctx=None,
        )

    def _check_gas_equivalence_with_solver(
        self,
        solver,
        evm_gas,
        x86_gas,
        deadline: Optional[float] = None,
        path_condition=None,
        context: str = "",
        logs: Optional[list] = None,
        ctx=None,
    ):
        """在给定 solver 上检查 gas 终值等价（支持并行 worker 的私有 solver）。

        缺一侧 gas（None）则视为「无 gas 观测」直接通过——让不携带 gas 的旧
        observation（单测 dummy 等）不触发检查，而非误报。
        """
        if evm_gas is None or x86_gas is None:
            return True, "Gas not observed (skipped)"

        prefix = self._ctx.context_prefix(context)

        # 共享 solver 时用 ctx 的预算重置;并行 worker 传入私有 solver，
        # 由 caller 负责其生命周期，这里只 push/pop 局部断言。
        use_shared = solver is self._ctx.solver
        if use_shared:
            if not self._ctx.reset_solver_with_budget_for(
                solver, self._ctx.timeout_ms, deadline
            ):
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg

        solver.push()
        try:
            if path_condition is not None:
                solver.add(path_condition)
            # 动态 gas（内存扩展二次项）两侧都含 128-bit UDiv：x86 是 `div r64`
            # 建模的 UDiv(Concat(RDX,RAX), ZeroExt(64,divisor))，EVM 是
            # UDiv(ZeroExt(64,square), 512)。两者 AST 不同，直接比较会 bit-blast
            # 而 unknown。注入已验证除法桥接（fail-closed，soundness 中性）让 Z3
            # 跳过 bit-blast。constraint 用 path_condition（含 scope assumption，
            # 保证 memWords 实参在两侧可证相等）。
            bridge_constraint = path_condition if path_condition is not None else BoolVal(True)
            self._ctx.add_div_bridges(
                solver,
                evm_gas,
                x86_gas,
                bridge_constraint,
                ctx=ctx,
            )
            # 反例查询：存在一组输入使两侧 gas 终值不同？
            solver.add(evm_gas != x86_gas)
            result = solver.check()
        finally:
            solver.pop()

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Gas equivalence check: result={result}",
        )

        if result == unsat:
            return True, "Gas equivalent"
        if result == sat:
            msg = self._ctx.observable_counterexample_message("gas", context)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        # UNKNOWN → fail-closed
        msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
        self._ctx.emit_solver_log(logs, f"    └─ {msg}")
        return False, msg
