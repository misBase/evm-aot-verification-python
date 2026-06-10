"""Return-data memory content equivalence helpers."""

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
    """Concrete-length return-data memory equivalence checks."""

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
        """Return a cache entry for Select(Store(...), key) lookups."""
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
        """Select one memory byte, cheaply resolving exact Store-chain hits."""
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
                    # A newer symbolic Store may alias this index; keep Z3's
                    # native latest-write semantics instead of guessing.
                    return Select(memory, index)
                return simplify(Select(base, index))

        return Select(memory, index)

    @staticmethod
    def _memory_chunk_expr(memory, base, start: int, size: int, ctx, select_cache=None):
        """Return a big-endian byte chunk expression from an Array memory."""
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
        """Prove return memory equality in coarse byte chunks.

        The byte fallback below is still the ground truth.  This helper only
        records byte ranges whose concatenated mismatch query is UNSAT; unknown
        chunk queries fall back to the original per-byte checks.
        """
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

            conditions = []
            if storage_independent_condition is not None:
                conditions.append(("storage-independent", storage_independent_condition))
            conditions.append(("full", path_condition))

            proved = False
            for condition_kind, condition in conditions:
                if not self._ctx.reset_solver_with_capped_budget_for(
                    solver,
                    self._ctx.timeout_ms,
                    deadline,
                    chunk_timeout_ms,
                ):
                    msg = self._ctx.timeout_message()
                    self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                    return False, msg, verified_indices, total_solve_time

                solver.add(condition)
                solver.add(evm_has_return_data)
                solver.add(x86_has_return_data)
                solver.add(evm_length == x86_length)
                solver.add(mismatch)

                query_start = time.time()
                result = solver.check()
                solve_time = time.time() - query_start
                total_solve_time += solve_time

                if result == unsat:
                    verified_indices.update(range(start, start + size))
                    proved = True
                    break
                if result == sat and condition_kind == "full":
                    msg = (
                        "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
                        "(memory contents differ)"
                    )
                    if context:
                        msg = (
                            f"{msg} ({context}, bytes {start}"
                            f"..{start + size - 1})"
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
        if not expr_mentions_symbol(mismatch_query, "CallDataSize"):
            return None

        calldata_size = BitVec("CallDataSize", 64, ctx=ctx)
        exact_limit = self._ctx.tuning.path_pair_calldatasize_exact_partition_limit
        exact_timeout_ms = self._ctx.tuning.path_pair_calldatasize_exact_partition_timeout_ms
        tail_timeout_ms = self._ctx.tuning.memory_unroll_byte_timeout_ms
        total_solve_time = 0.0
        start = time.time()

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
                msg = (
                    "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
                    "(memory contents differ)"
                )
                if context:
                    msg = f"{msg} ({context}, byte {byte_index}, size={size})"
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg, total_solve_time
            return None

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
            msg = (
                "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
                "(memory contents differ)"
            )
            if context:
                msg = f"{msg} ({context}, byte {byte_index}, size>={exact_limit})"
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
        if length > self._ctx.tuning.memory_unroll_byte_limit:
            return None

        total_solve_time = 0.0
        start = time.time()
        if length == 0:
            prefix = f"{context}: " if context else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Memory content check: "
                "0.000s wall / 0.000s solve, unrolled 0 byte(s)",
            )
            return True, "Memory contents equivalent (unrolled)"
        storage_independent_condition = self._storage_independent_condition(
            path_condition,
            ctx,
        )
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
                if not self._ctx.reset_solver_with_capped_budget_for(
                    solver,
                    self._ctx.timeout_ms,
                    deadline,
                    self._ctx.tuning.memory_unroll_byte_timeout_ms,
                ):
                    msg = self._ctx.timeout_message()
                    self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                    return False, msg
                solver.add(storage_independent_condition)
                solver.add(evm_has_return_data)
                solver.add(x86_has_return_data)
                solver.add(evm_length == x86_length)
                solver.add(mismatch)

                query_start = time.time()
                result = solver.check()
                solve_time = time.time() - query_start
                total_solve_time += solve_time
                if result == unsat:
                    continue

            if not self._ctx.reset_solver_with_capped_budget_for(
                solver,
                self._ctx.timeout_ms,
                deadline,
                self._ctx.tuning.memory_unroll_byte_timeout_ms,
            ):
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg

            solver.add(path_condition)
            solver.add(evm_has_return_data)
            solver.add(x86_has_return_data)
            solver.add(evm_length == x86_length)
            solver.add(mismatch)

            query_start = time.time()
            result = solver.check()
            solve_time = time.time() - query_start
            total_solve_time += solve_time

            if result == unsat:
                continue
            mismatch_query = And(
                path_condition,
                evm_has_return_data,
                x86_has_return_data,
                evm_length == x86_length,
                mismatch,
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
                msg = (
                    "✗ COUNTEREXAMPLE FOUND: x86 does not refine EVM "
                    "(memory contents differ)"
                )
                if context:
                    msg = f"{msg} ({context}, byte {byte_index})"
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            msg = self._ctx.unknown_message_for_solver(
                solver,
                self._ctx.tuning.memory_unroll_byte_timeout_ms,
            )
            self._ctx.emit_solver_log(logs, f"    └─ {msg} (byte {byte_index})")
            return False, msg

        prefix = f"{context}: " if context else ""
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Memory content check: "
            f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
            f"chunked {len(chunk_verified_indices)} byte(s), "
            f"unrolled {length - len(chunk_verified_indices)} byte(s)",
        )
        return True, "Memory contents equivalent (unrolled)"
