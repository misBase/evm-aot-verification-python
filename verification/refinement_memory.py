"""return-data memory 内容等价检查辅助函数。"""

import time
from typing import Optional, Tuple

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Concat,
    eq as z3_eq,
    Goal,
    is_true,
    Select,
    simplify,
    SolverFor,
    substitute,
    Tactic,
    Then,
    UGE,
    sat,
    unsat,
)

from utils.z3_helpers import (
    collect_and_conjuncts,
    decompose_store_chain,
    expr_has_uninterpreted_decl,
    expr_mentions_symbol,
)

from .refinement_context import _RefinementContext


class MemoryContentChecks:
    """小具体长度 return-data memory 等价检查。"""

    def __init__(self, ctx: _RefinementContext):
        self._ctx = ctx

    @staticmethod
    def _expr_mentions_storage_dependency(expr) -> bool:
        return expr_has_uninterpreted_decl(
            expr,
            lambda decl, _node: (
                decl.name() in ("Storage", "TransientStorage")
                or decl.name().startswith("sha3")
            ),
        )

    def _storage_independent_condition(self, path_condition, ctx):
        """返回去掉 storage-only 分支事实后的较弱路径条件。"""
        if path_condition is None:
            return None
        conjuncts = collect_and_conjuncts(path_condition)
        kept = [
            conjunct
            for conjunct in conjuncts
            if not self._expr_mentions_storage_dependency(conjunct)
        ]
        if len(kept) == len(conjuncts):
            return None
        return And(BoolVal(True, ctx=ctx), *kept)

    @staticmethod
    def _cached_store_chain(memory, select_cache: dict):
        """缓存 Store 链拆解结果，供 Select(Store(...), key) 快速命中。"""
        try:
            memory_hash = memory.hash()
        except Exception:
            return None

        entries = select_cache.setdefault(memory_hash, [])
        for cached_memory, cached_entry in entries:
            try:
                if z3_eq(cached_memory, memory):
                    return cached_entry
            except Exception:
                continue

        base, stores = decompose_store_chain(memory)
        newest_to_oldest = []
        for key, value in reversed(stores):
            try:
                simplified_key = simplify(key)
            except Exception:
                simplified_key = key
            newest_to_oldest.append((simplified_key, value))
        entry = (base, tuple(newest_to_oldest))
        entries.append((memory, entry))
        return entry

    @staticmethod
    def memory_select_expr(memory, index, select_cache: Optional[dict] = None):
        """读取一个 memory byte，并尽量直接化简精确命中的 Store 链。"""
        if select_cache is not None:
            entry = MemoryContentChecks._cached_store_chain(
                memory,
                select_cache,
            )
            if entry is not None:
                base, newest_to_oldest = entry
                try:
                    simplified_index = simplify(index)
                except Exception:
                    simplified_index = index
                for key, value in newest_to_oldest:
                    try:
                        if z3_eq(key, simplified_index) or is_true(
                            simplify(key == simplified_index)
                        ):
                            return simplify(value)
                        if is_true(simplify(key != simplified_index)):
                            continue
                    except Exception:
                        pass
                    # 较新的符号 Store 可能 alias 当前下标；这里交回 Z3 保持
                    # 原生 latest-write 语义，避免自行猜测。
                    return Select(memory, index)
                return simplify(Select(base, index))

        return Select(memory, index)

    @staticmethod
    def _memory_chunk_expr(memory, base, start: int, size: int, ctx, select_cache=None):
        """从 Array memory 拼出一个 big-endian byte chunk 表达式。"""
        if size <= 0:
            raise ValueError("memory chunk size must be positive")
        bytes_list = [
            MemoryContentChecks.memory_select_expr(
                memory,
                base + BitVecVal(start + i, 64, ctx=ctx),
                select_cache,
            )
            for i in range(size)
        ]
        return simplify(bytes_list[0] if size == 1 else Concat(*bytes_list))

    @staticmethod
    def _return_memory_mismatch_query(
        condition,
        evm_has_return_data,
        x86_has_return_data,
        evm_length,
        x86_length,
        mismatch,
        ctx,
    ):
        """组装 return memory 反例查询的公共约束。"""
        return And(
            BoolVal(True, ctx=ctx),
            condition,
            evm_has_return_data,
            x86_has_return_data,
            evm_length == x86_length,
            mismatch,
        )

    def _check_return_memory_mismatch_with_solver(
        self,
        solver,
        condition,
        mismatch,
        evm_has_return_data,
        x86_has_return_data,
        evm_length,
        x86_length,
        deadline: Optional[float],
        timeout_ms: int,
        logs: Optional[list[str]],
        ctx,
    ):
        """带预算查询是否存在 return memory mismatch 反例。"""
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            timeout_ms,
        ):
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return None, 0.0, msg

        solver.add(
            self._return_memory_mismatch_query(
                condition,
                evm_has_return_data,
                x86_has_return_data,
                evm_length,
                x86_length,
                mismatch,
                ctx,
            )
        )

        query_start = time.time()
        result = solver.check()
        solve_time = time.time() - query_start
        return result, solve_time, None

    @staticmethod
    def _memory_counterexample_message(context: str, detail: Optional[str] = None):
        """构造 memory 内容不一致的反例消息。"""
        msg = (
            "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
            "(memory contents differ)"
        )
        if context:
            suffix = context if detail is None else f"{context}, {detail}"
            msg = f"{msg} ({suffix})"
        return msg

    def _check_memory_content_chunked_with_solver(
        self,
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
        length: int,
        deadline: Optional[float],
        path_condition,
        storage_independent_condition,
        context: str,
        logs: Optional[list[str]],
        ctx,
    ) -> Tuple[Optional[bool], Optional[str], set[int], float]:
        """用较粗的 byte chunk 证明 return memory 内容一致。

        逐 byte fallback 仍是最终基准；这里仅记录 chunk mismatch 查询已
        UNSAT 的 byte 范围，难解的 chunk 会回退到逐 byte 检查。
        """
        # 优先尝试大块，剩余长度不足时逐步降到 4 byte。
        chunk_sizes = (32, 16, 8, 4)
        if length < chunk_sizes[-1]:
            return None, None, set(), 0.0

        chunk_timeout_ms = self._ctx.tuning.memory_chunk_timeout_ms
        fallback_streak_limit = self._ctx.tuning.memory_chunk_fallback_streak_limit
        total_solve_time = 0.0
        verified_indices: set[int] = set()
        start = 0
        fallback_streak = 0
        select_cache = {}

        while start < length:
            size = next((s for s in chunk_sizes if s <= length - start), 0)
            if size == 0:
                break

            evm_chunk = self._memory_chunk_expr(
                evm_memory,
                evm_offset,
                start,
                size,
                ctx,
                select_cache,
            )
            x86_chunk = self._memory_chunk_expr(
                x86_memory,
                x86_base_addr + x86_offset,
                start,
                size,
                ctx,
                select_cache,
            )
            mismatch = simplify(evm_chunk != x86_chunk)

            # 先尝试更弱的 storage-independent 条件；失败再用完整条件确认。
            conditions = []
            if storage_independent_condition is not None:
                conditions.append(("storage-independent", storage_independent_condition))
            conditions.append(("full", path_condition))

            proved = False
            for condition_kind, condition in conditions:
                result, solve_time, error_msg = self._check_return_memory_mismatch_with_solver(
                    solver,
                    condition,
                    mismatch,
                    evm_has_return_data,
                    x86_has_return_data,
                    evm_length,
                    x86_length,
                    deadline,
                    chunk_timeout_ms,
                    logs,
                    ctx,
                )
                total_solve_time += solve_time
                if error_msg is not None:
                    return False, error_msg, verified_indices, total_solve_time

                if result == unsat:
                    verified_indices.update(range(start, start + size))
                    proved = True
                    break
                if result == sat and condition_kind == "full":
                    # 只有完整 path_condition 下 SAT 才是真实内存反例。
                    msg = self._memory_counterexample_message(
                        context,
                        f"bytes {start}..{start + size - 1}",
                    )
                    self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                    return False, msg, verified_indices, total_solve_time

            if not proved:
                fallback_streak += 1
                prefix = f"{context}: " if context else ""
                self._ctx.emit_solver_log(
                    logs,
                    f"    ├─ {prefix}Memory chunk bytes {start}"
                    f"..{start + size - 1} fallback to byte checks",
                )
            else:
                fallback_streak = 0
            start += size
            if fallback_streak >= fallback_streak_limit and start < length:
                # 连续多个 chunk 都难以证明时，停止 chunk 尝试，交给逐 byte 检查。
                prefix = f"{context}: " if context else ""
                self._ctx.emit_solver_log(
                    logs,
                    f"    ├─ {prefix}Memory chunk checks abandoned after "
                    f"{fallback_streak} consecutive fallback(s)",
                )
                break

        if len(verified_indices) == length:
            return (
                True,
                "Memory contents equivalent (chunked)",
                verified_indices,
                total_solve_time,
            )
        return None, None, verified_indices, total_solve_time

    def _check_memory_byte_mismatch_by_calldatasize_partition(
        self,
        mismatch_query,
        deadline: Optional[float],
        context: str,
        byte_index: int,
        logs: Optional[list[str]],
        ctx,
    ) -> Optional[Tuple[bool, Optional[str], float]]:
        """按 CallDataSize 穷举切分难解的 byte mismatch 查询。"""
        # 只有查询真的依赖 CallDataSize 时，分区才可能带来化简收益。
        if not expr_mentions_symbol(mismatch_query, "CallDataSize"):
            return None

        calldata_size = BitVec("CallDataSize", 64, ctx=ctx)
        exact_limit = self._ctx.tuning.path_pair_calldatasize_exact_partition_limit
        exact_timeout_ms = self._ctx.tuning.path_pair_calldatasize_exact_partition_timeout_ms
        tail_timeout_ms = self._ctx.tuning.memory_unroll_byte_timeout_ms
        total_solve_time = 0.0
        start = time.time()

        # 每个分区先轻量化简，消掉替换 CallDataSize 后的分支条件。
        def _preprocess_query(query):
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

        def _check_query(query, timeout_ms):
            query = _preprocess_query(query)
            partition_solver = (
                SolverFor("QF_AUFBV", ctx=ctx)
                if ctx is not None
                else SolverFor("QF_AUFBV")
            )
            if not self._ctx.reset_solver_with_capped_budget_for(
                partition_solver,
                self._ctx.timeout_ms,
                deadline,
                timeout_ms,
            ):
                return None, 0.0
            partition_solver.add(query)
            query_start = time.time()
            result = partition_solver.check()
            return result, time.time() - query_start

        # 先枚举小的精确 calldata size。
        for size in range(exact_limit):
            size_value = BitVecVal(size, 64, ctx=ctx)
            exact_query = simplify(
                substitute(mismatch_query, (calldata_size, size_value))
            )
            result, solve_time = _check_query(exact_query, exact_timeout_ms)
            total_solve_time += solve_time
            if result is None:
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg, total_solve_time
            if result == unsat:
                continue
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory byte {byte_index} calldata-size split "
                f"size={size}: {solve_time:.3f}s, result={result}",
            )
            if result == sat:
                msg = self._memory_counterexample_message(
                    context,
                    f"byte {byte_index}, size={size}",
                )
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg, total_solve_time
            return None

        # 剩余较大的 calldata size 合并成一个尾部分区。
        tail_query = And(
            mismatch_query,
            UGE(calldata_size, BitVecVal(exact_limit, 64, ctx=ctx)),
        )
        result, solve_time = _check_query(tail_query, tail_timeout_ms)
        total_solve_time += solve_time
        if result is None:
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg, total_solve_time
        if result == unsat:
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory byte {byte_index} calldata-size partition: "
                f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
                "all partitions unsat",
            )
            return True, None, total_solve_time
        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Memory byte {byte_index} calldata-size split "
            f"size>={exact_limit}: {solve_time:.3f}s, result={result}",
        )
        if result == sat:
            msg = self._memory_counterexample_message(
                context,
                f"byte {byte_index}, size>={exact_limit}",
            )
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg, total_solve_time
        return None

    def check_concrete_length_memory_with_solver(
        self,
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
        length: int,
        deadline: Optional[float],
        path_condition,
        context: str,
        logs: Optional[list[str]],
        ctx,
    ) -> Optional[Tuple[bool, Optional[str]]]:
        """证明小具体长度 return data 的 memory 内容一致。

        返回 None 表示快路径不适用，调用方应退回符号下标的通用 memory 检查。
        """
        # 只处理可安全展开的小长度；更长的返回数据交给通用路径。
        if length > self._ctx.tuning.memory_unroll_byte_limit:
            return None

        total_solve_time = 0.0
        start = time.time()
        # 空返回区间没有 byte 需要比较；return metadata 已由调用方先证明。
        if length == 0:
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory content check: "
                "0.000s wall / 0.000s solve, unrolled 0 byte(s)",
            )
            return True, "Memory contents equivalent (unrolled)"

        # 如果路径条件里混有 storage-only 事实，先尝试用更弱、更容易求解的条件
        # 证明 memory byte 相等；证明不了再回到完整 path_condition。
        storage_independent_condition = self._storage_independent_condition(
            path_condition,
            ctx,
        )
        # 先用 32/16/8/4-byte chunk 做粗粒度反例查询，能一次证明一段就跳过
        # 后续逐 byte 检查。
        chunk_status, chunk_msg, chunk_verified_indices, chunk_solve_time = (
            self._check_memory_content_chunked_with_solver(
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
                length,
                deadline,
                path_condition,
                storage_independent_condition,
                context,
                logs,
                ctx,
            )
        )
        total_solve_time += chunk_solve_time
        if chunk_status is False:
            return False, chunk_msg
        if chunk_status is True:
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory content check: "
                f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
                f"chunked {length} byte(s)",
            )
            return True, chunk_msg

        # chunk 未覆盖的部分退回逐 byte 检查；每个查询仍然按“找反例”写。
        byte_select_cache = {}
        for byte_index in range(length):
            if byte_index in chunk_verified_indices:
                continue
            index = BitVecVal(byte_index, 64, ctx=ctx)
            evm_byte = self.memory_select_expr(
                evm_memory,
                evm_offset + index,
                byte_select_cache,
            )
            x86_byte = self.memory_select_expr(
                x86_memory,
                x86_base_addr + x86_offset + index,
                byte_select_cache,
            )
            mismatch = simplify(evm_byte != x86_byte)
            if storage_independent_condition is not None:
                # 弱条件下 UNSAT 已足以证明完整路径下也不会有该 byte 的反例。
                result, solve_time, error_msg = self._check_return_memory_mismatch_with_solver(
                    solver,
                    storage_independent_condition,
                    mismatch,
                    evm_has_return_data,
                    x86_has_return_data,
                    evm_length,
                    x86_length,
                    deadline,
                    self._ctx.tuning.memory_unroll_byte_timeout_ms,
                    logs,
                    ctx,
                )
                total_solve_time += solve_time
                if error_msg is not None:
                    return False, error_msg
                if result == unsat:
                    continue

            # 弱条件证明不了时，用完整 path_condition 确认是否真有反例。
            result, solve_time, error_msg = self._check_return_memory_mismatch_with_solver(
                solver,
                path_condition,
                mismatch,
                evm_has_return_data,
                x86_has_return_data,
                evm_length,
                x86_length,
                deadline,
                self._ctx.tuning.memory_unroll_byte_timeout_ms,
                logs,
                ctx,
            )
            total_solve_time += solve_time
            if error_msg is not None:
                return False, error_msg

            if result == unsat:
                continue
            # 带 CallDataSize 的查询有时整体难解；按具体 calldata size 分区后，
            # 很多边界 ITE 可以被化简掉。
            mismatch_query = self._return_memory_mismatch_query(
                path_condition,
                evm_has_return_data,
                x86_has_return_data,
                evm_length,
                x86_length,
                mismatch,
                ctx,
            )
            partition_result = self._check_memory_byte_mismatch_by_calldatasize_partition(
                mismatch_query,
                deadline,
                context,
                byte_index,
                logs,
                ctx,
            )
            if partition_result is not None:
                partition_verified, partition_msg, partition_solve_time = partition_result
                total_solve_time += partition_solve_time
                if partition_verified:
                    continue
                if partition_msg is not None:
                    return False, partition_msg
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory byte {byte_index} check: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == sat:
                msg = self._memory_counterexample_message(
                    context,
                    f"byte {byte_index}",
                )
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            msg = self._ctx.unknown_message_for_solver(
                solver,
                self._ctx.tuning.memory_unroll_byte_timeout_ms,
            )
            self._ctx.emit_solver_log(logs, f"    └─ {msg} (byte {byte_index})")
            return False, msg

        # 所有未被 chunk 覆盖的 byte 都已逐个证明不存在 mismatch。
        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Memory content check: "
            f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
            f"chunked {len(chunk_verified_indices)} byte(s), "
            f"unrolled {length - len(chunk_verified_indices)} byte(s)",
        )
        return True, "Memory contents equivalent (unrolled)"
