"""Observable refinement checks for return data, memory, and debug stack slots."""

import time
from typing import TYPE_CHECKING, Optional, Tuple

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Select,
    UGE,
    ULT,
    sat,
    unsat,
)

from state.smt_state import MemoryDomain

from utils.z3_helpers import get_simplified_bv_const_value

from .refinement_context import _RefinementContext
from .refinement_memory import MemoryContentChecks
from .refinement_storage import StorageEquivalenceChecks

if TYPE_CHECKING:
    from state.smt_state import SMTState


class OutputRefinementChecks:
    def __init__(
        self,
        ctx: _RefinementContext,
        storage: StorageEquivalenceChecks,
        memory: MemoryContentChecks,
    ):
        self._ctx = ctx
        self._storage = storage
        self._memory = memory

    def check_refinement(
        self,
        evm_result: dict,
        x86_result: dict,
        assumptions=None,
    ) -> Tuple[bool, Optional[str]]:
        """检查x86是否精化EVM（对所有输入，x86_result = evm_result）。

        此方法验证精化关系：
          ∀ inputs. x86_output(inputs) = evm_output(inputs)

        Args:
            evm_result: 包含 offset, length, memory, base_addr, has_return_data, storage, transient_storage 的字典
            x86_result: 同上格式的字典
            assumptions: 可选 Z3 BoolRef，作为顶层 precondition 注入 solver
                （例如 calldatasize 上界约束）

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        # 将 timeout_ms 作为整个 refine 检查流程的总预算（而不是每次 check 的预算）。
        deadline = time.time() + (self._ctx.timeout_ms / 1000.0)

        return self.check_observables(
            evm_result, x86_result, deadline,
            path_condition=assumptions,
        )

    def _check_return_metadata_with_solver(
        self,
        solver,
        evm_has_return_data,
        x86_has_return_data,
        evm_length,
        x86_length,
        deadline: Optional[float],
        path_condition,
        context: str,
        logs: Optional[list[str]],
        ctx,
    ) -> Tuple[bool, Optional[str]]:
        if not self._ctx.reset_solver_with_budget_for(solver, self._ctx.timeout_ms, deadline):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data != x86_has_return_data)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Non-empty return-data condition check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data conditions differ"
            if context:
                msg = f"{msg} ({context})"
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        if not self._ctx.reset_solver_with_budget_for(solver, self._ctx.timeout_ms, deadline):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data)
        solver.add(x86_has_return_data)
        solver.add(evm_length != x86_length)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Length equality check: {solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data lengths differ"
            if context:
                msg = f"{msg} ({context})"
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        return True, None

    def check_observables_with_solver(
        self,
        solver,
        evm_result: dict,
        x86_result: dict,
        deadline: Optional[float] = None,
        path_condition=None,
        context: str = "",
        logs: Optional[list[str]] = None,
        ctx=None,
    ) -> Tuple[bool, Optional[str]]:
        """Check return data, memory, storage, and transient storage observables."""
        evm_offset = evm_result['offset']
        evm_length = evm_result['length']
        evm_memory = evm_result['memory']
        evm_has_return_data = evm_result.get(
            'has_return_data',
            evm_length != BitVecVal(0, 64, ctx=ctx),
        )

        x86_offset = x86_result['offset']
        x86_length = x86_result['length']
        x86_memory = x86_result['memory']
        x86_base_addr = x86_result['base_addr']
        x86_has_return_data = x86_result.get(
            'has_return_data',
            x86_length != BitVecVal(0, 64, ctx=ctx),
        )
        path_condition = path_condition if path_condition is not None else BoolVal(True, ctx=ctx)

        concrete_length = get_simplified_bv_const_value(evm_length)
        if (
            concrete_length is not None
            and concrete_length <= self._ctx.tuning.memory_unroll_byte_limit
        ):
            verified, msg = self._check_return_metadata_with_solver(
                solver,
                evm_has_return_data,
                x86_has_return_data,
                evm_length,
                x86_length,
                deadline,
                path_condition,
                context,
                logs,
                ctx,
            )
            if not verified:
                return False, msg
            unrolled = self._memory.check_concrete_length_memory_with_solver(
                solver,
                evm_memory,
                x86_memory,
                evm_offset,
                x86_offset,
                x86_base_addr,
                evm_has_return_data,
                x86_has_return_data,
                evm_length,
                x86_length,
                concrete_length,
                deadline,
                path_condition,
                context,
                logs,
                ctx,
            )
            if unrolled is not None:
                verified, msg = unrolled
                if not verified:
                    return False, msg
                evm_storage = evm_result.get('storage')
                x86_storage = x86_result.get('storage')
                if evm_storage is not None and x86_storage is not None:
                    verified, msg = self._storage._check_storage_equivalence_with_solver(
                        solver,
                        evm_storage,
                        x86_storage,
                        deadline,
                        path_condition,
                        context,
                        logs,
                        ctx,
                    )
                    if not verified:
                        return False, msg

                evm_ts = evm_result.get('transient_storage')
                x86_ts = x86_result.get('transient_storage')
                if evm_ts is not None and x86_ts is not None:
                    verified, msg = self._storage._check_transient_storage_equivalence_with_solver(
                        solver,
                        evm_ts,
                        x86_ts,
                        deadline,
                        path_condition,
                        context,
                        logs,
                        ctx,
                    )
                    if not verified:
                        return False, msg

                msg = (
                    "✓ VERIFIED: x86 refines EVM (non-empty return-data conditions, "
                    "lengths, memory contents, storage, and transient storage are "
                    "equivalent for all inputs)"
                )
                if not context:
                    self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return True, msg

        if not self._ctx.reset_solver_with_budget_for(solver, self._ctx.timeout_ms, deadline):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data != x86_has_return_data)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Non-empty return-data condition check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data conditions differ"
            if context:
                msg = f"{msg} ({context})"
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        if not self._ctx.reset_solver_with_budget_for(solver, self._ctx.timeout_ms, deadline):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data)
        solver.add(x86_has_return_data)
        solver.add(evm_length != x86_length)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Length equality check: {solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data lengths differ"
            if context:
                msg = f"{msg} ({context})"
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        if not self._ctx.reset_solver_with_budget_for(solver, self._ctx.timeout_ms, deadline):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data)
        solver.add(x86_has_return_data)
        solver.add(evm_length == x86_length)

        i = BitVec('return_data_index', 64, ctx=ctx)
        index_in_range = And(BoolVal(True, ctx=ctx), UGE(i, BitVecVal(0, 64, ctx=ctx)), ULT(i, evm_length))
        evm_addr = evm_offset + i
        x86_addr = x86_base_addr + x86_offset + i
        evm_byte = Select(evm_memory, evm_addr)
        x86_byte = Select(x86_memory, x86_addr)
        solver.add(index_in_range)
        solver.add(evm_byte != x86_byte)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Memory content check: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            pass
        elif result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (memory contents differ)"
            if context:
                msg = f"{msg} ({context})"
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        else:
            msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        evm_storage = evm_result.get('storage')
        x86_storage = x86_result.get('storage')
        if evm_storage is not None and x86_storage is not None:
            verified, msg = self._storage._check_storage_equivalence_with_solver(
                solver,
                evm_storage,
                x86_storage,
                deadline,
                path_condition,
                context,
                logs,
                ctx,
            )
            if not verified:
                return False, msg

        evm_ts = evm_result.get('transient_storage')
        x86_ts = x86_result.get('transient_storage')
        if evm_ts is not None and x86_ts is not None:
            verified, msg = self._storage._check_transient_storage_equivalence_with_solver(
                solver,
                evm_ts,
                x86_ts,
                deadline,
                path_condition,
                context,
                logs,
                ctx,
            )
            if not verified:
                return False, msg

        msg = (
            "✓ VERIFIED: x86 refines EVM (non-empty return-data conditions, lengths, "
            "memory contents, storage, and transient storage are equivalent for all inputs)"
        )
        if not context:
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
        return True, msg

    def check_observables(
        self,
        evm_result: dict,
        x86_result: dict,
        deadline: Optional[float] = None,
        path_condition=None,
        context: str = "",
    ) -> Tuple[bool, Optional[str]]:
        """通过直接比较 return data 内容检查精化关系。"""
        return self.check_observables_with_solver(
            self._ctx.solver,
            evm_result,
            x86_result,
            deadline,
            path_condition=path_condition,
            context=context,
            logs=None,
            ctx=None,
        )

    def check_stack_equivalence(
        self,
        evm_state: 'SMTState',
        x86_state: 'SMTState',
        initial_state: 'SMTState',
        n_elements: int = 2,
        deadline: Optional[float] = None,
    ) -> Tuple[bool, Optional[str]]:
        """检查 EVM 栈和 x86 预置栈窗口中固定槽位的一致性（调试用）。"""
        if deadline is None:
            deadline = time.time() + (self._ctx.timeout_ms / 1000.0)

        stack_base = initial_state.stack_base  # 原始 R14_stack_base 纯变量
        evm_stack = evm_state.evm_stack.Stack

        # 固定槽位坐标系的起点由初始预置窗口底部决定：
        # i=0 对应最底部预置槽位，i 递增时向上移动。
        # 若 n_elements 超过初始预置槽位数，则继续比较更高的固定槽位；
        # 这些槽位允许是未预填的符号内容，由调用方手工控制检查范围。
        bottom_offset = -evm_state.stack_num_inputs * 0x20

        for i in range(n_elements):
            if not self._ctx.reset_solver_with_budget(deadline):
                msg = self._ctx.timeout_message()
                if self._ctx.verbose:
                    print(f"    └─ {msg}")
                return False, msg

            # 从固定槽位坐标系底部向上第 i 个 32-byte 槽位：
            #   x86: load_256bit(stack_base - initial_num_inputs*0x20 + i*0x20)
            #   EVM: Stack[i]
            rel_offset = bottom_offset + i * 0x20
            x86_val = x86_state.x86_memory.load_256bit(
                stack_base + BitVecVal(rel_offset, 64),
                domain=MemoryDomain.STACK,
            )
            evm_val = Select(evm_stack, i)

            if self._ctx.verbose:
                print(f"    ├─ Checking fixed stack slot {i} (x86 addr: stack_base {rel_offset:+#x})")

            self._ctx.solver.add(evm_val != x86_val)

            start_time = time.time()
            result = self._ctx.solver.check()
            solve_time = time.time() - start_time

            if self._ctx.verbose:
                print(f"    ├─ Stack slot {i} check: {solve_time:.3f}s, result={result}")

            if result == sat:
                msg = f"✗ COUNTEREXAMPLE: Fixed stack slot {i} differs between EVM and x86"
                if self._ctx.verbose:
                    print(f"    └─ {msg}")
                return False, msg
            elif result != unsat:
                msg = self._ctx.unknown_message()
                if self._ctx.verbose:
                    print(f"    └─ {msg}")
                return False, msg

        msg = f"✓ VERIFIED: {n_elements} fixed stack slot(s) are equivalent"

        if self._ctx.verbose:
            print(f"    └─ {msg}")
        return True, msg
