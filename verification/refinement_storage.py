"""Storage and transient-storage equivalence helpers for refinement checks."""

import time
from typing import Optional

from z3 import (
    And,
    BitVec,
    BitVecVal,
    Select,
    SolverFor,
    UGE,
    sat,
    unsat,
)

from .refinement_context import _RefinementContext


def _storage_arrays_structurally_equal(a, b) -> bool:
    """快速结构等价检查（同一 Z3 AST 实例或 hash 相等）。"""
    if a is None or b is None:
        return False
    try:
        if a is b:
            return True
        # eq() 是 z3 Python API 的 syntactic equality（AST 同结构同地址）。
        from z3 import eq as _z3_eq
        return _z3_eq(a, b)
    except Exception:
        return False


def _decompose_store_chain(arr):
    """将一个 Z3 Array 表达式分解为 (base_array, [(key, value), ...]) 形式。"""
    from z3 import Z3_OP_STORE
    stores = []
    cur = arr
    try:
        while True:
            if not hasattr(cur, "decl"):
                break
            decl_kind = cur.decl().kind()
            if decl_kind != Z3_OP_STORE:
                break
            args = cur.children()  # [base, key, value]
            if len(args) != 3:
                break
            stores.append((args[1], args[2]))
            cur = args[0]
    except Exception:
        return arr, []
    stores.reverse()  # 顺序从最早到最近
    return cur, stores


def _storage_arrays_syntactically_equal(a, b) -> bool:
    """递归地按 AST 结构判断两个 Z3 Array 表达式是否等价。"""
    from z3 import eq as _z3_eq
    try:
        if a is b or _z3_eq(a, b):
            return True
    except Exception:
        return False
    # AST 不直接相等：仅在 Store / If 这类 *组合* 节点上才递归 children。
    # 对叶节点（BitVecVal/Const 等）和其他 declkinds，require z3.eq 已为
    # syntactic 等价的唯一判据；上面已经 fail 过了，直接返回 False。
    try:
        if not (hasattr(a, "decl") and hasattr(b, "decl")):
            return False
        from z3 import Z3_OP_STORE, Z3_OP_ITE
        ka = a.decl().kind()
        kb = b.decl().kind()
        if ka != kb:
            return False
        if ka not in (Z3_OP_STORE, Z3_OP_ITE):
            # 非 Store/If 节点：z3.eq 已 fail，无递归收益，直接 False。
            return False
        children_a = a.children()
        children_b = b.children()
        if len(children_a) != len(children_b):
            return False
        for ca, cb in zip(children_a, children_b):
            if not _storage_arrays_syntactically_equal(ca, cb):
                return False
        return True
    except Exception:
        return False


def _collect_and_conjuncts(expr):
    """把一个 BoolRef 展平成它的 And-conjunct 列表（递归穿透嵌套 And）。"""
    from z3 import Z3_OP_AND
    out = []
    stack = [expr]
    while stack:
        cur = stack.pop()
        if cur is None:
            continue
        try:
            if hasattr(cur, "decl") and cur.decl().kind() == Z3_OP_AND:
                stack.extend(cur.children())
                continue
        except Exception:
            pass
        out.append(cur)
    return out


def _bool_implied_by_conjuncts(conjuncts, target) -> bool:
    """如果 target syntactic 出现在 conjuncts 中，返回 True；否则 False。"""
    from z3 import eq as _z3_eq
    for c in conjuncts:
        try:
            if _z3_eq(c, target):
                return True
        except Exception:
            continue
    return False


def _negate_syntactic(expr):
    """构造 Not(expr)，但如果 expr 本身是 Not(x)，返回 x。"""
    from z3 import Not, Z3_OP_NOT
    try:
        if hasattr(expr, "decl") and expr.decl().kind() == Z3_OP_NOT:
            children = expr.children()
            if len(children) == 1:
                return children[0]
    except Exception:
        pass
    try:
        return Not(expr)
    except Exception:
        return None


def _resolve_if_branch_under_path_condition(if_expr, path_conjuncts, solver_check):
    """对一个 ITE 节点 `If(C, then, else)`，在给定 path_condition 下判断选支。"""
    children = if_expr.children()
    if len(children) != 3:
        return None
    cond, then_branch, else_branch = children

    # 1) syntactic: C ∈ conjuncts? then-branch active.
    if _bool_implied_by_conjuncts(path_conjuncts, cond):
        return 0
    # 2) syntactic: ¬C ∈ conjuncts? else-branch active.
    neg_cond = _negate_syntactic(cond)
    if neg_cond is not None and _bool_implied_by_conjuncts(path_conjuncts, neg_cond):
        return 1

    # 3) solver-assisted: 试两个方向，oracle 内部做 equality-confirmed cache。
    if solver_check is None:
        return None
    try:
        from z3 import And as _And
        # path_condition ∧ ¬C unsat -> path 强制 C 为真 -> then 分支 active.
        pc_then_expr = _And(*path_conjuncts, neg_cond) if neg_cond is not None else None
        if pc_then_expr is not None and solver_check(pc_then_expr):
            return 0
        # path_condition ∧ C unsat -> path 强制 ¬C -> else 分支 active.
        pc_else_expr = _And(*path_conjuncts, cond)
        if solver_check(pc_else_expr):
            return 1
    except Exception:
        return None
    return None


def _storage_arrays_eq_under_path(
    a,
    b,
    path_conjuncts,
    solver_check,
    *,
    max_depth: int = 32,
):
    """path-condition-aware 版本的 Storage AST 等价比较。"""
    from z3 import eq as _z3_eq, Z3_OP_STORE, Z3_OP_ITE
    if a is None or b is None:
        return False
    if max_depth <= 0:
        return False
    # Direct AST equality short-circuit.
    try:
        if a is b or _z3_eq(a, b):
            return True
    except Exception:
        return False

    a_is_ite = False
    b_is_ite = False
    try:
        a_is_ite = hasattr(a, "decl") and a.decl().kind() == Z3_OP_ITE
    except Exception:
        pass
    try:
        b_is_ite = hasattr(b, "decl") and b.decl().kind() == Z3_OP_ITE
    except Exception:
        pass

    # 单侧 ITE：在 path_condition 下消解 If 守卫，再递归。
    if a_is_ite and not b_is_ite:
        return _eq_under_path_ite_one_sided(
            a, b, path_conjuncts, solver_check, max_depth,
        )
    if b_is_ite and not a_is_ite:
        return _eq_under_path_ite_one_sided(
            b, a, path_conjuncts, solver_check, max_depth,
        )

    # 双侧同形（Store/ITE 类组合节点）：递归 children。
    try:
        if not (hasattr(a, "decl") and hasattr(b, "decl")):
            return False
        ka = a.decl().kind()
        kb = b.decl().kind()
        if ka != kb:
            return False
        if ka not in (Z3_OP_STORE, Z3_OP_ITE):
            return False
        children_a = a.children()
        children_b = b.children()
        if len(children_a) != len(children_b):
            return False
        for ca, cb in zip(children_a, children_b):
            if not _storage_arrays_eq_under_path(
                ca, cb, path_conjuncts, solver_check, max_depth=max_depth - 1,
            ):
                return False
        return True
    except Exception:
        return False


def _eq_under_path_ite_one_sided(ite_side, other, path_conjuncts, solver_check, max_depth):
    """处理单侧 ITE：先尝试 entailment 选支，否则 case-split."""
    children = ite_side.children()
    if len(children) != 3:
        return False
    cond, then_branch, else_branch = children

    idx = _resolve_if_branch_under_path_condition(ite_side, path_conjuncts, solver_check)
    if idx == 0:
        # path ⇒ cond，only then-branch reachable
        return _storage_arrays_eq_under_path(
            then_branch, other, path_conjuncts, solver_check, max_depth=max_depth - 1,
        )
    if idx == 1:
        # path ⇒ ¬cond，only else-branch reachable
        return _storage_arrays_eq_under_path(
            else_branch, other, path_conjuncts, solver_check, max_depth=max_depth - 1,
        )
    # 守卫无法被 entail。case-split：要求 then 在 path∧C 下等价，else 在
    # path∧¬C 下也等价。
    neg_cond = _negate_syntactic(cond)
    conjuncts_then = list(path_conjuncts) + [cond]
    if not _storage_arrays_eq_under_path(
        then_branch, other, conjuncts_then, solver_check, max_depth=max_depth - 1,
    ):
        return False
    conjuncts_else = list(path_conjuncts)
    if neg_cond is not None:
        conjuncts_else = conjuncts_else + [neg_cond]
    return _storage_arrays_eq_under_path(
        else_branch, other, conjuncts_else, solver_check, max_depth=max_depth - 1,
    )


def _storage_store_chains_equal(a, b) -> bool:
    """更深一层结构性等价：递归走 Store / If 节点比较 AST 形态。"""
    if a is None or b is None:
        return False
    return _storage_arrays_syntactically_equal(a, b)


class StorageEquivalenceChecks:
    def __init__(self, ctx: _RefinementContext):
        self._ctx = ctx

    def _make_unsat_oracle(self, _parent_solver, deadline: Optional[float], ctx):
        """返回一个闭包 oracle(expr) -> bool 用于 path-aware structural fast path。"""
        # 这是 path-aware fast path 内部的 implication 探测预算，不影响外层
        # storage fallback 的完整 solver budget。
        local_budget_ms = self._ctx.tuning.path_structural_oracle_timeout_ms
        cache_miss = object()

        def _cache_key(expr):
            try:
                return (id(expr.ctx), expr.hash())
            except Exception:
                return None

        def _lookup_cached(expr, key):
            from z3 import eq as _z3_eq

            with self._ctx.unsat_oracle_cache_lock:
                for cached_expr, cached_result in self._ctx.unsat_oracle_cache.get(key, []):
                    try:
                        if _z3_eq(cached_expr, expr):
                            return cached_result
                    except Exception:
                        continue
            return cache_miss

        def _remember_result(expr, key, result: bool) -> None:
            from z3 import eq as _z3_eq

            with self._ctx.unsat_oracle_cache_lock:
                bucket = self._ctx.unsat_oracle_cache.setdefault(key, [])
                for index, (cached_expr, cached_result) in enumerate(bucket):
                    try:
                        if _z3_eq(cached_expr, expr):
                            # Prefer a later proven-unsat result over an earlier
                            # conservative False from UNKNOWN.
                            if result and not cached_result:
                                bucket[index] = (expr, result)
                            return
                    except Exception:
                        continue
                bucket.append((expr, result))

        def _oracle(expr) -> bool:
            key = _cache_key(expr)
            if key is None:
                return False
            cached = _lookup_cached(expr, key)
            if cached is not cache_miss:
                return cached
            budget_ms = local_budget_ms
            if deadline is not None:
                remaining_ms = int((deadline - time.time()) * 1000)
                if remaining_ms <= 0:
                    return False
                budget_ms = min(local_budget_ms, max(remaining_ms, 1))
            try:
                if ctx is not None:
                    probe = SolverFor("QF_AUFBV", ctx=ctx)
                else:
                    probe = SolverFor("QF_AUFBV")
                probe.set("timeout", budget_ms)
                probe.add(expr)
                result = probe.check()
            except Exception:
                return False
            is_unsat = result == unsat
            if is_unsat or result == sat or budget_ms >= local_budget_ms:
                _remember_result(expr, key, is_unsat)
            return is_unsat

        return _oracle

    @staticmethod
    def _expr_mentions_symbol(expr, symbol_name: str) -> bool:
        """Return True if ``expr`` contains an uninterpreted const by name."""
        from z3 import Z3_OP_UNINTERPRETED

        seen = set()
        stack = [expr]
        while stack:
            cur = stack.pop()
            if cur is None:
                continue
            try:
                key = cur.hash()
            except Exception:
                continue
            if key in seen:
                continue
            seen.add(key)
            try:
                decl = cur.decl()
                if (
                    decl.kind() == Z3_OP_UNINTERPRETED
                    and decl.name() == symbol_name
                    and len(cur.children()) == 0
                ):
                    return True
                stack.extend(cur.children())
            except Exception:
                continue
        return False

    def _array_mismatch_query_with_solver(
        self,
        solver,
        evm_array,
        x86_array,
        deadline: Optional[float],
        path_condition,
        ctx,
        *,
        timeout_cap_ms: Optional[int] = None,
        key_name: str = "storage_check_key",
    ):
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            timeout_cap_ms,
        ):
            return None, 0.0

        key = BitVec(key_name, 256, ctx=ctx)
        if path_condition is not None:
            solver.add(path_condition)
        solver.add(Select(evm_array, key) != Select(x86_array, key))

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time
        return result, solve_time

    def _try_array_structural_fast_path(
        self,
        evm_array,
        x86_array,
        path_condition,
        solver,
        deadline: Optional[float],
        ctx,
        context: str,
        logs: Optional[list[str]],
        *,
        log_label: str,
        success_subject: str,
    ) -> Optional[tuple[bool, str]]:
        """Try cheap, sound structural proofs for storage-like Array equality."""
        prefix = self._ctx.context_prefix(context)
        if _storage_store_chains_equal(evm_array, x86_array):
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label} equivalence check: "
                f"0.000s, structural-eq fast path",
            )
            return True, f"{success_subject} equivalent (structural)"

        if path_condition is None:
            return None

        path_conjuncts = _collect_and_conjuncts(path_condition)
        if _storage_arrays_eq_under_path(
            evm_array,
            x86_array,
            path_conjuncts,
            solver_check=self._make_unsat_oracle(solver, deadline, ctx),
        ):
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label} equivalence check: "
                f"~0s, path-aware structural-eq fast path",
            )
            return True, f"{success_subject} equivalent (path-aware structural)"

        return None

    def _storage_mentions_symbolic_calldatasize(
        self,
        evm_storage,
        x86_storage,
        path_condition,
    ) -> bool:
        if path_condition is None:
            return False
        return (
            self._expr_mentions_symbol(path_condition, "CallDataSize")
            or self._expr_mentions_symbol(evm_storage, "CallDataSize")
            or self._expr_mentions_symbol(x86_storage, "CallDataSize")
        )

    def _calldatasize_partitions(self, ctx):
        calldata_size = BitVec("CallDataSize", 64, ctx=ctx)
        exact_limit = self._ctx.tuning.storage_calldatasize_exact_partition_limit
        for i in range(exact_limit):
            yield (
                f"size={i}",
                calldata_size == BitVecVal(i, 64, ctx=ctx),
                self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms,
            )
        yield (
            f"size>={exact_limit}",
            UGE(calldata_size, BitVecVal(exact_limit, 64, ctx=ctx)),
            self._ctx.tuning.storage_calldatasize_tail_partition_timeout_ms,
        )

    def _check_storage_equivalence_by_calldatasize_partition(
        self,
        solver,
        evm_storage,
        x86_storage,
        deadline: Optional[float],
        path_condition,
        context: str,
        logs: Optional[list[str]],
        ctx,
    ):
        """Exhaustive split for storage queries mentioning symbolic CallDataSize."""
        total_solve_time = 0.0
        start = time.time()
        for label, size_condition, partition_timeout_ms in self._calldatasize_partitions(ctx):
            partition_condition = (
                And(path_condition, size_condition)
                if path_condition is not None
                else size_condition
            )
            result, solve_time = self._array_mismatch_query_with_solver(
                solver,
                evm_storage,
                x86_storage,
                deadline,
                partition_condition,
                ctx,
                timeout_cap_ms=partition_timeout_ms,
                key_name=f"storage_check_key_{label.replace('>=', 'ge').replace('=', '_')}",
            )
            total_solve_time += solve_time
            if result is None:
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            if result == unsat:
                continue
            prefix = self._ctx.context_prefix(context)
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage calldata-size split {label}: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == sat:
                msg = self._ctx.observable_counterexample_message(
                    "storage",
                    context,
                    label,
                )
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            msg = self._ctx.unknown_message_for_solver(solver, partition_timeout_ms)
            self._ctx.emit_solver_log(logs, f"    └─ {msg} ({label})")
            return False, msg

        prefix = self._ctx.context_prefix(context)
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage equivalence check: "
            f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
            "calldatasize partition",
        )
        return True, "Storage equivalent (calldatasize partition)"

    def _check_storage_equivalence(
        self,
        evm_storage,
        x86_storage,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        """检查EVM和x86的Storage是否等价。"""
        return self._check_storage_equivalence_with_solver(
            self._ctx.solver,
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
        fast_path = self._try_array_structural_fast_path(
            evm_storage,
            x86_storage,
            path_condition,
            solver,
            deadline,
            ctx,
            context,
            logs,
            log_label="Storage",
            success_subject="Storage",
        )
        if fast_path is not None:
            return fast_path

        prefix = self._ctx.context_prefix(context)
        if self._storage_mentions_symbolic_calldatasize(
            evm_storage,
            x86_storage,
            path_condition,
        ):
            result, solve_time = self._array_mismatch_query_with_solver(
                solver,
                evm_storage,
                x86_storage,
                deadline,
                path_condition,
                ctx,
                timeout_cap_ms=self._ctx.tuning.storage_quick_timeout_ms,
                key_name="storage_check_key_quick",
            )
            if result is None:
                msg = self._ctx.timeout_message()
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage equivalence quick check: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == unsat:
                return True, "Storage equivalent"
            if result == sat:
                msg = self._ctx.observable_counterexample_message("storage", context)
                self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                return False, msg

            verified, msg = self._check_storage_equivalence_by_calldatasize_partition(
                solver,
                evm_storage,
                x86_storage,
                deadline,
                path_condition,
                context,
                logs,
                ctx,
            )
            return verified, msg

        result, solve_time = self._array_mismatch_query_with_solver(
            solver,
            evm_storage,
            x86_storage,
            deadline,
            path_condition,
            ctx,
            timeout_cap_ms=None,
            key_name="storage_check_key",
        )
        if result is None:
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage equivalence check: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Storage equivalent"
        if result == sat:
            msg = self._ctx.observable_counterexample_message("storage", context)
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
        self._ctx.emit_solver_log(logs, f"    └─ {msg}")
        return False, msg

    def _check_transient_storage_equivalence(
        self,
        evm_ts,
        x86_ts,
        deadline=None,
        path_condition=None,
        context: str = "",
    ):
        """检查EVM和x86的Transient Storage是否等价。"""
        return self._check_transient_storage_equivalence_with_solver(
            self._ctx.solver,
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
        fast_path = self._try_array_structural_fast_path(
            evm_ts,
            x86_ts,
            path_condition,
            solver,
            deadline,
            ctx,
            context,
            logs,
            log_label="Transient storage",
            success_subject="Transient storage",
        )
        if fast_path is not None:
            return fast_path

        result, solve_time = self._array_mismatch_query_with_solver(
            solver,
            evm_ts,
            x86_ts,
            deadline,
            path_condition,
            ctx,
            key_name="transient_storage_check_key",
        )
        if result is None:
            msg = self._ctx.timeout_message()
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        prefix = self._ctx.context_prefix(context)
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Transient storage equivalence check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Transient storage equivalent"
        if result == sat:
            msg = self._ctx.observable_counterexample_message(
                "transient storage",
                context,
            )
            self._ctx.emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        msg = self._ctx.unknown_message_for_solver(solver, self._ctx.timeout_ms)
        self._ctx.emit_solver_log(logs, f"    └─ {msg}")
        return False, msg
