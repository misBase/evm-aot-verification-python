"""
用于验证x86和EVM语义之间精化关系的精化检查器。

验证x86精化EVM：对所有输入，x86_output = EVM_output。
"""

import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Context,
    Not,
    Or,
    Select,
    SolverFor,
    UGE,
    ULT,
    sat,
    set_option,
    unsat,
)
from typing import TYPE_CHECKING, Tuple, Optional

from state.smt_state import MemoryDomain

if TYPE_CHECKING:
    from state.smt_state import SMTState


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


class RefinementChecker:
    """检查x86和EVM语义之间的精化关系。
    
    验证x86精化EVM：对所有输入，x86_output = EVM_output。
    """
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False):
        """初始化精化检查器。
        
        Args:
            timeout_ms: SMT求解器超时（毫秒）
            verbose: 启用详细输出
        """
        self.timeout_ms = timeout_ms
        self.verbose = verbose

        # NOTE: Z3 set_option 是全局设置。这里显式在每个实例中设置，避免
        # 前一个 verbose=True 的测试污染后续 verbose=False 的测试。
        set_option(verbose=10 if verbose else 0)
        set_option(proof=bool(verbose))
        
        # 使用QF_AUFBV（数组、未解释函数、位向量）以支持Array比较
        # QF_BV不支持Arrays，所以我们需要QF_AUFBV
        self.solver = SolverFor("QF_AUFBV")
        self.solver.set("timeout", timeout_ms)

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
    def _reset_solver_with_budget_for(solver, timeout_ms: int, deadline: Optional[float]) -> bool:
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

    def _reset_solver_with_budget(self, deadline: Optional[float]) -> bool:
        """重置求解器并为本次 check 设置剩余预算。"""
        return self._reset_solver_with_budget_for(self.solver, self.timeout_ms, deadline)

    def _emit_solver_log(self, logs: Optional[list[str]], line: str) -> None:
        if not self.verbose:
            return
        if logs is None:
            print(line)
        else:
            logs.append(line)
    
    def check_refinement(self, evm_result: dict, x86_result: dict) -> Tuple[bool, Optional[str]]:
        """检查x86是否精化EVM（对所有输入，x86_result = evm_result）。

        此方法验证精化关系：
          ∀ inputs. x86_output(inputs) = evm_output(inputs)

        Args:
            evm_result: 包含 offset, length, memory, base_addr, has_return_data, storage, transient_storage 的字典
            x86_result: 同上格式的字典

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        # 将 timeout_ms 作为整个 refine 检查流程的总预算（而不是每次 check 的预算）。
        deadline = time.time() + (self.timeout_ms / 1000.0)

        return self._check_refinement_direct_memory(evm_result, x86_result, deadline)

    def check_refinement_paths(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        path_pair_workers: int = 1,
    ) -> Tuple[bool, Optional[str]]:
        """Check refinement directly over terminal path observations.

        This avoids first merging whole terminal memory/storage arrays.  For each
        feasible EVM/x86 terminal-path intersection, it proves the same
        observable properties as ``check_refinement``.
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
            )
        else:
            checked_pair_count, pair_count, failure = self._check_path_pairs_parallel(
                evm_results,
                x86_results,
                deadline,
                path_pair_workers,
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
    ) -> tuple[int, int, Optional[str]]:
        pair_count = 0
        checked_pair_count = 0
        for evm_index, evm_result in enumerate(evm_results):
            evm_condition = evm_result.get("condition", BoolVal(True))
            for x86_index, x86_result in enumerate(x86_results):
                x86_condition = x86_result.get("condition", BoolVal(True))
                path_condition = And(evm_condition, x86_condition)
                pair_count += 1
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
        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
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

    def _check_refinement_direct_memory_with_solver(
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
        """``_check_refinement_direct_memory`` variant for worker-local solvers."""
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

        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data != x86_has_return_data)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Non-empty return-data condition check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data conditions differ"
            if context:
                msg = f"{msg} ({context})"
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._unknown_message_for_solver(solver, self.timeout_ms)
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        solver.add(path_condition)
        solver.add(evm_has_return_data)
        solver.add(x86_has_return_data)
        solver.add(evm_length != x86_length)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Length equality check: {solve_time:.3f}s, result={result}",
        )

        if result == sat:
            msg = "✗ COUNTEREXAMPLE: Non-empty return-data lengths differ"
            if context:
                msg = f"{msg} ({context})"
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        if result != unsat:
            msg = self._unknown_message_for_solver(solver, self.timeout_ms)
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
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
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Memory content check: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            pass
        elif result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (memory contents differ)"
            if context:
                msg = f"{msg} ({context})"
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg
        else:
            msg = self._unknown_message_for_solver(solver, self.timeout_ms)
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        evm_storage = evm_result.get('storage')
        x86_storage = x86_result.get('storage')
        if evm_storage is not None and x86_storage is not None:
            verified, msg = self._check_storage_equivalence_with_solver(
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
            verified, msg = self._check_transient_storage_equivalence_with_solver(
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
            self._emit_solver_log(logs, f"    └─ {msg}")
        return True, msg

    def _check_refinement_direct_memory(
        self,
        evm_result: dict,
        x86_result: dict,
        deadline: Optional[float] = None,
        path_condition=None,
        context: str = "",
    ) -> Tuple[bool, Optional[str]]:
        """通过直接比较 return data 内容检查精化关系。

        当前抽象只比较“是否暴露非空 return data”以及对应的字节内容，
        不区分 RETURN、REVERT、STOP 等 halt 语义。

        这里通过搜索“存在一个范围内字节不同的反例”，等价地验证：
          ForAll i. (0 <= i < length) =>
            EVM_memory[evm_offset + i] == x86_memory[x86_base_addr + x86_offset + i]

        Args:
            evm_result: 包含以下键的字典：
                - 'offset': EVM内存中的64位BitVec偏移量
                - 'length': 64位BitVec长度（0 表示当前抽象下不暴露非空 return data）
                - 'memory': Array[BitVec[64], BitVec[8]] - EVM内存
                - 'base_addr': None（EVM使用直接偏移量，None表示直接寻址）
                - 'has_return_data': Z3 BoolRef（由 length != 0 构造）
            x86_result: 包含以下键的字典：
                - 'offset': 64位BitVec偏移量
                - 'length': 64位BitVec长度（0 表示当前抽象下不暴露非空 return data）
                - 'memory': Array[BitVec[64], BitVec[8]] - x86内存
                - 'base_addr': 64位BitVec（R15寄存器值，EVM内存基址指针）
                - 'has_return_data': Z3 BoolRef（由 length != 0 构造）

        注意：
            x86_64/semantics.py 中的 status_code_has_return_data 是 status-derived；
            这里读取的 has_return_data 是对外结果层的 length-derived 条件。

        Returns:
            (verified, message)，如果精化关系成立则verified为True
        """
        return self._check_refinement_direct_memory_with_solver(
            self.solver,
            evm_result,
            x86_result,
            deadline,
            path_condition=path_condition,
            context=context,
            logs=None,
            ctx=None,
        )

    def _check_storage_equivalence(
        self,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        """检查EVM和x86的Storage是否等价。

        反证法：是否存在key使得 Select(evm_storage, key) != Select(x86_storage, key)
        如果UNSAT，则storage等价。

        Args:
            evm_storage: EVM侧的Storage Z3 Array
            x86_storage: x86侧的Storage Z3 Array
            deadline: 超时截止时间

        Returns:
            (verified, message)
        """
        return self._check_storage_equivalence_with_solver(
            self.solver,
            evm_storage,
            x86_storage,
            deadline,
            path_condition,
            context,
            logs=None,
            ctx=None,
        )

    def _check_storage_equivalence_with_solver(
        self,
        solver,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=None,
        context: str = "",
        logs: Optional[list[str]] = None,
        ctx=None,
    ):
        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        key = BitVec('storage_check_key', 256, ctx=ctx)
        if path_condition is not None:
            solver.add(path_condition)
        solver.add(Select(evm_storage, key) != Select(x86_storage, key))

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage equivalence check: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Storage equivalent"
        if result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (storage differs)"
            if context:
                msg = f"{msg} ({context})"
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        msg = self._unknown_message_for_solver(solver, self.timeout_ms)
        self._emit_solver_log(logs, f"    └─ {msg}")
        return False, msg

    def check_stack_equivalence(
        self,
        evm_state: 'SMTState',
        x86_state: 'SMTState',
        initial_state: 'SMTState',
        n_elements: int = 2,
        deadline: Optional[float] = None,
    ) -> Tuple[bool, Optional[str]]:
        """检查 EVM 栈和 x86 预置栈窗口中固定槽位的一致性（调试用）。

        注意：这里**不是**按执行后逻辑栈顶/当前 SP 去取值，而是比较
        以 create_initial_state() 建立的固定槽位约定为基准的前 N 个 32-byte 槽位。
        也就是说，它验证的是：
        - x86 侧：以原始 stack_base 为基址的固定相对偏移
        - EVM 侧：Stack[0], Stack[1], ...

        对 num_inputs=2 的初始布局，这对应于：
        - slot 0 -> [stack_base - 0x40, stack_base - 0x20)
        - slot 1 -> [stack_base - 0x20, stack_base + 0x00)

        `n_elements` 可以大于 create_initial_state() 预置的输入槽位数。
        这种情况下，检查会继续沿固定槽位坐标系向上比较额外槽位；
        这些槽位可能是执行过程中写入的值，也可能仍然是空理论/未预填的符号内容。
        这是一个调试接口，允许调用方手工控制检查范围。

        Args:
            evm_state: EVM to_z3() 执行后的 SMTState
            x86_state: x86 to_z3() 执行后的 SMTState
            initial_state: create_initial_state() 返回的初始状态（提供原始 stack_base）
            n_elements: 要检查的槽数（默认 2）

        Returns:
            (verified, message)
        """
        from z3 import simplify, is_int_value

        if deadline is None:
            deadline = time.time() + (self.timeout_ms / 1000.0)

        stack_base = initial_state.stack_base  # 原始 R14_stack_base 纯变量
        evm_stack = evm_state.evm_stack.Stack

        # 固定槽位坐标系的起点由初始预置窗口底部决定：
        # i=0 对应最底部预置槽位，i 递增时向上移动。
        # 若 n_elements 超过初始预置槽位数，则继续比较更高的固定槽位；
        # 这些槽位允许是未预填的符号内容，由调用方手工控制检查范围。
        bottom_offset = -evm_state.stack_num_inputs * 0x20

        for i in range(n_elements):
            if not self._reset_solver_with_budget(deadline):
                msg = self._timeout_message()
                if self.verbose:
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

            if self.verbose:
                print(f"    ├─ Checking fixed stack slot {i} (x86 addr: stack_base {rel_offset:+#x})")

            self.solver.add(evm_val != x86_val)

            start_time = time.time()
            result = self.solver.check()
            solve_time = time.time() - start_time

            if self.verbose:
                print(f"    ├─ Stack slot {i} check: {solve_time:.3f}s, result={result}")

            if result == sat:
                msg = f"✗ COUNTEREXAMPLE: Fixed stack slot {i} differs between EVM and x86"
                if self.verbose:
                    print(f"    └─ {msg}")
                return False, msg
            elif result != unsat:
                msg = self._unknown_message()
                if self.verbose:
                    print(f"    └─ {msg}")
                return False, msg

        msg = f"✓ VERIFIED: {n_elements} fixed stack slot(s) are equivalent"

        if self.verbose:
            print(f"    └─ {msg}")
        return True, msg

    def _check_transient_storage_equivalence(
        self,
        evm_ts,
        x86_ts,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        """检查EVM和x86的Transient Storage是否等价。

        反证法：是否存在key使得 Select(evm_ts, key) != Select(x86_ts, key)
        如果UNSAT，则transient storage等价。

        Args:
            evm_ts: EVM侧的TransientStorage Z3 Array
            x86_ts: x86侧的TransientStorage Z3 Array
            deadline: 超时截止时间

        Returns:
            (verified, message)
        """
        return self._check_transient_storage_equivalence_with_solver(
            self.solver,
            evm_ts,
            x86_ts,
            deadline,
            path_condition,
            context,
            logs=None,
            ctx=None,
        )

    def _check_transient_storage_equivalence_with_solver(
        self,
        solver,
        evm_ts,
        x86_ts,
        deadline=None,
        path_condition=None,
        context: str = "",
        logs: Optional[list[str]] = None,
        ctx=None,
    ):
        if not self._reset_solver_with_budget_for(solver, self.timeout_ms, deadline):
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        key = BitVec('transient_storage_check_key', 256, ctx=ctx)
        if path_condition is not None:
            solver.add(path_condition)
        solver.add(Select(evm_ts, key) != Select(x86_ts, key))

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = f"{context}: " if context else ""
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Transient storage equivalence check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Transient storage equivalent"
        if result == sat:
            msg = "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM (transient storage differs)"
            if context:
                msg = f"{msg} ({context})"
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        msg = self._unknown_message_for_solver(solver, self.timeout_ms)
        self._emit_solver_log(logs, f"    └─ {msg}")
        return False, msg
