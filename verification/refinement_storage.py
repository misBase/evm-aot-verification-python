"""Storage and transient-storage equivalence helpers for refinement checks."""

from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
import time
from typing import Optional

from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolVal,
    Context,
    Extract,
    Goal,
    Select,
    Solver,
    SolverFor,
    Tactic,
    Then,
    UGE,
    ULT,
    is_bv_value,
    is_true,
    sat,
    simplify,
    substitute,
    unsat,
)

from utils.z3_helpers import (
    collect_and_conjuncts,
    decompose_store_chain,
    expr_mentions_symbol,
)

from .refinement_context import _RefinementContext


_STORAGE_FEASIBILITY_RESCUE_LOCK = threading.Lock()
_STORAGE_FEASIBILITY_RESCUE_ATTEMPTS = 1
_STORAGE_EXACT_PARTITION_WORKERS = 4
_STORAGE_TRANSLATE_LOCK = threading.Lock()


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


def _expr_node_count(expr, *, limit: int = 128) -> int:
    """返回 AST 节点数；超过 ``limit`` 后提前停止。"""
    seen = set()
    stack = [expr]
    count = 0
    while stack:
        cur = stack.pop()
        try:
            key = cur.hash()
        except Exception:
            continue
        if key in seen:
            continue
        seen.add(key)
        count += 1
        if count > limit:
            return count
        try:
            stack.extend(cur.children())
        except Exception:
            continue
    return count


def _uninterpreted_const_name(expr) -> Optional[str]:
    try:
        from z3 import Z3_OP_UNINTERPRETED

        if (
            hasattr(expr, "decl")
            and expr.decl().kind() == Z3_OP_UNINTERPRETED
            and len(expr.children()) == 0
        ):
            return expr.decl().name()
    except Exception:
        return None
    return None


def _is_small_path_value_substitution_term(term) -> bool:
    """筛选适合在路径条件下重写的小表达式。"""
    try:
        from z3 import Z3_OP_EXTRACT, Z3_OP_SELECT

        if _expr_node_count(term, limit=80) > 80:
            return False

        const_name = _uninterpreted_const_name(term)
        if const_name in {"CallValue64", "CallDataSize"}:
            return True

        if not hasattr(term, "decl"):
            return False
        kind = term.decl().kind()
        if kind == Z3_OP_SELECT:
            array, index = term.children()
            array_name = _uninterpreted_const_name(array)
            index_value = simplify(index)
            return (
                array_name == "CallData"
                and is_bv_value(index_value)
                and index_value.as_long() < 128
            )

        if kind == Z3_OP_EXTRACT:
            child = term.children()[0]
            if not (hasattr(child, "decl") and child.decl().kind() == Z3_OP_SELECT):
                return False
            array, index = child.children()
            array_name = _uninterpreted_const_name(array)
            index_value = simplify(index)
            return (
                array_name in {"Storage", "TransientStorage"}
                and is_bv_value(index_value)
                and index_value.as_long() < 16
            )
    except Exception:
        return False
    return False


def _collect_path_value_substitutions(condition, *, max_replacements: int = 64):
    """收集路径条件在语法上蕴含的 ``term -> concrete_bv`` 重写。

    对仍在原始路径条件下检查的表达式，这些重写是安全的：路径的每个 model 中
    ``term`` 与 ``concrete_bv`` 值相同。若调用方连 condition 本身也重写，
    仍只能把 UNSAT 当作结论，因为从条件中消去等式可能削弱 SAT 查询。
    """
    replacements = []
    for conjunct in collect_and_conjuncts(condition):
        try:
            if not (hasattr(conjunct, "decl") and conjunct.decl().kind_name() == "="):
                continue
        except Exception:
            pass
        try:
            from z3 import Z3_OP_EQ

            if conjunct.decl().kind() != Z3_OP_EQ:
                continue
            left, right = conjunct.children()
            left_s = simplify(left)
            right_s = simplify(right)
            if is_bv_value(left_s) and _is_small_path_value_substitution_term(right):
                replacements.append((right, left_s))
            elif is_bv_value(right_s) and _is_small_path_value_substitution_term(left):
                replacements.append((left, right_s))
        except Exception:
            continue
        if len(replacements) >= max_replacements:
            break

    deduped = []
    for term, value in replacements:
        duplicate = False
        for existing, _ in deduped:
            try:
                from z3 import eq as _z3_eq

                if _z3_eq(existing, term):
                    duplicate = True
                    break
            except Exception:
                continue
        if not duplicate:
            deduped.append((term, value))
    return tuple(deduped)


def _rewrite_exprs_with_path_value_substitutions(
    condition,
    *exprs,
    max_replacements: int = 64,
):
    """使用路径中的具体事实重写非 condition 表达式。"""
    if condition is None:
        return exprs, 0
    replacements = _collect_path_value_substitutions(
        condition,
        max_replacements=max_replacements,
    )
    if not replacements:
        return exprs, 0
    rewritten = []
    for expr in exprs:
        try:
            rewritten.append(simplify(substitute(expr, *replacements)))
        except Exception:
            rewritten.append(expr)
    return tuple(rewritten), len(replacements)


def _select_store_replacement(expr):
    """当 BV 地址可判定时，化简一个 ``Select(Store(...), idx)``。"""
    try:
        from z3 import Z3_OP_SELECT, Z3_OP_STORE

        if not (hasattr(expr, "decl") and expr.decl().kind() == Z3_OP_SELECT):
            return None
        array, index = expr.children()
        cur = array
        changed = False
        while hasattr(cur, "decl") and cur.decl().kind() == Z3_OP_STORE:
            base, key, value = cur.children()
            if is_true(simplify(key == index)):
                return value
            if is_true(simplify(key != index)):
                cur = base
                changed = True
                continue
            break
        if changed:
            return Select(cur, index)
    except Exception:
        return None
    return None


def _simplify_select_store_chains(expr, *, max_rounds: int = 4):
    """在表达式内部应用可判定的 select/store 重写。"""
    current = expr
    for _ in range(max_rounds):
        replacements = []
        seen = set()
        stack = [current]
        while stack:
            cur = stack.pop()
            try:
                key = cur.hash()
            except Exception:
                continue
            if key in seen:
                continue
            seen.add(key)
            replacement = _select_store_replacement(cur)
            if replacement is not None:
                replacements.append((cur, replacement))
                continue
            try:
                stack.extend(cur.children())
            except Exception:
                continue
        if not replacements:
            return simplify(current)
        try:
            current = simplify(substitute(current, *replacements))
        except Exception:
            return simplify(current)
    return simplify(current)


def _preprocess_partition_condition(condition, ctx):
    """对具体 calldata-size partition 做保持等价的轻量预处理。"""
    try:
        goal = Goal(ctx=ctx) if ctx is not None else Goal()
        goal.add(condition)
        tactic = (
            Then(
                Tactic("simplify", ctx=ctx),
                Tactic("propagate-values", ctx=ctx),
            )
            if ctx is not None
            else Then("simplify", "propagate-values")
        )
        subgoals = tactic(goal)
        if len(subgoals) != 1:
            return condition
        formulas = list(subgoals[0])
        return simplify(And(BoolVal(True, ctx=ctx), *formulas))
    except Exception:
        return condition


def _preprocess_satisfiability_query(query, ctx):
    """对闭合 solver 查询做保持 SAT 性的预处理。"""
    try:
        goal = Goal(ctx=ctx) if ctx is not None else Goal()
        goal.add(query)
        tactic = (
            Then(
                Tactic("simplify", ctx=ctx),
                Tactic("propagate-values", ctx=ctx),
                Tactic("solve-eqs", ctx=ctx),
                Tactic("simplify", ctx=ctx),
            )
            if ctx is not None
            else Then("simplify", "propagate-values", "solve-eqs", "simplify")
        )
        subgoals = tactic(goal)
        if len(subgoals) != 1:
            return query
        formulas = list(subgoals[0])
        return simplify(And(BoolVal(True, ctx=ctx), *formulas))
    except Exception:
        return query


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
            return (
                solver_check is not None
                and _non_array_exprs_equal_under_path(a, b, path_conjuncts, solver_check)
            )
        if ka not in (Z3_OP_STORE, Z3_OP_ITE):
            if solver_check is not None and _non_array_exprs_equal_under_path(
                a, b, path_conjuncts, solver_check,
            ):
                return True
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


def _non_array_exprs_equal_under_path(a, b, path_conjuncts, solver_check) -> bool:
    """证明非 Array 子表达式在当前路径下相等。"""
    try:
        from z3 import And as _And, Z3_ARRAY_SORT

        if not a.sort().eq(b.sort()):
            return False
        if a.sort().kind() == Z3_ARRAY_SORT:
            return False
        return solver_check(_And(*path_conjuncts, a != b))
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
    try:
        from z3 import And as _And
        then_infeasible = solver_check is not None and solver_check(_And(*conjuncts_then))
    except Exception:
        then_infeasible = False
    if not then_infeasible:
        if not _storage_arrays_eq_under_path(
            then_branch, other, conjuncts_then, solver_check, max_depth=max_depth - 1,
        ):
            return False
    conjuncts_else = list(path_conjuncts)
    if neg_cond is not None:
        conjuncts_else = conjuncts_else + [neg_cond]
    try:
        from z3 import And as _And
        else_infeasible = solver_check is not None and solver_check(_And(*conjuncts_else))
    except Exception:
        else_infeasible = False
    if else_infeasible:
        return True
    return _storage_arrays_eq_under_path(
        else_branch, other, conjuncts_else, solver_check, max_depth=max_depth - 1,
    )


def _storage_store_chains_equal(a, b) -> bool:
    """更深一层结构性等价：递归走 Store / If 节点比较 AST 形态。"""
    if a is None or b is None:
        return False
    return _storage_arrays_syntactically_equal(a, b)


def _store_chain_lengths_differ(a, b) -> bool:
    """判断两个 array 是否有明显不同的 Store-chain 深度。"""
    try:
        _, stores_a = decompose_store_chain(a)
        _, stores_b = decompose_store_chain(b)
        return len(stores_a) != len(stores_b)
    except Exception:
        return False


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
        mismatch = Select(evm_array, key) != Select(x86_array, key)
        if path_condition is not None:
            solver.add(path_condition)
        solver.add(mismatch)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time
        return result, solve_time

    def _path_condition_unsat_rescue_with_solver(
        self,
        path_condition,
        deadline: Optional[float],
        logs: Optional[list[str]],
        ctx,
        context: str,
        *,
        log_label: str = "Storage path feasibility rescue",
        timeout_cap_ms: Optional[int] = None,
        attempts: int = _STORAGE_FEASIBILITY_RESCUE_ATTEMPTS,
    ) -> bool:
        """cheap check 超时后，尝试证明 storage 查询因路径不可行而 vacuous。"""
        if path_condition is None:
            return False

        prefix = self._ctx.context_prefix(context)
        timeout_cap_ms = (
            self._ctx.tuning.storage_path_feasibility_rescue_timeout_ms
            if timeout_cap_ms is None
            else timeout_cap_ms
        )
        for attempt in range(attempts):
            rescue_ctx = Context()
            rescue_condition = path_condition.translate(rescue_ctx)
            solver = SolverFor("QF_AUFBV", ctx=rescue_ctx)
            if not self._ctx.reset_solver_with_capped_budget_for(
                solver,
                self._ctx.timeout_ms,
                deadline,
                timeout_cap_ms,
            ):
                return False

            solver.add(rescue_condition)
            start_time = time.time()
            with _STORAGE_FEASIBILITY_RESCUE_LOCK:
                result = solver.check()
            solve_time = time.time() - start_time

            retry = f" retry {attempt + 1}" if attempt else ""
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label}{retry}: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == unsat:
                return True
            if result == sat:
                return False
        return False

    def _condition_unsat_probe_with_solver(
        self,
        solver,
        condition,
        deadline: Optional[float],
        logs: Optional[list[str]],
        context: str,
        *,
        log_label: str,
        timeout_cap_ms: int,
    ) -> bool:
        """使用调用方的 solver/context 探测条件是否 UNSAT。"""
        if condition is None:
            return False
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            timeout_cap_ms,
        ):
            return False

        solver.add(condition)
        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = self._ctx.context_prefix(context)
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}{log_label}: {solve_time:.3f}s, result={result}",
        )
        return result == unsat

    def _try_array_mismatch_unsat_with_path_value_substitution(
        self,
        solver,
        evm_array,
        x86_array,
        deadline: Optional[float],
        path_condition,
        ctx,
        context: str,
        logs: Optional[list[str]],
        *,
        log_label: str,
        timeout_cap_ms: int,
    ) -> tuple[Optional[bool], float]:
        """尝试路径值重写后的弱化 mismatch 查询。

        如果 ``path_condition`` 包含 ``CallData[0] == 0x86`` 这类事实，把它们
        代入 condition 和 storage 表达式通常能折叠 merge 引入的 ITE。由于重写
        condition 可能削弱查询，这里只接受 UNSAT 作为证明；SAT/UNKNOWN 会回退到
        原始查询。
        """
        if path_condition is None:
            return None, 0.0
        replacements = _collect_path_value_substitutions(path_condition)
        if not replacements:
            return None, 0.0

        try:
            rewritten_condition = simplify(
                substitute(path_condition, *replacements)
            )
            rewritten_evm_array = simplify(substitute(evm_array, *replacements))
            rewritten_x86_array = simplify(substitute(x86_array, *replacements))
        except Exception:
            return None, 0.0

        prefix = self._ctx.context_prefix(context)
        if _storage_store_chains_equal(rewritten_evm_array, rewritten_x86_array):
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label} value-subst equivalence check: "
                f"0.000s, {len(replacements)} rewrite(s), structural-eq fast path",
            )
            return True, 0.0

        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            timeout_cap_ms,
        ):
            return None, 0.0
        key = BitVec(f"{log_label.replace(' ', '_')}_value_subst_key", 256, ctx=ctx)
        mismatch = Select(rewritten_evm_array, key) != Select(rewritten_x86_array, key)
        query = _preprocess_satisfiability_query(
            And(rewritten_condition, mismatch),
            ctx,
        )
        solver.add(query)

        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time
        if result != unsat:
            fallback_solver = Solver(ctx=ctx) if ctx is not None else Solver()
            if self._ctx.reset_solver_with_capped_budget_for(
                fallback_solver,
                self._ctx.timeout_ms,
                deadline,
                min(timeout_cap_ms, 60000),
            ):
                fallback_solver.add(query)
                fallback_start = time.time()
                fallback_result = fallback_solver.check()
                fallback_solve_time = time.time() - fallback_start
                if fallback_result == unsat:
                    result = fallback_result
                    solve_time += fallback_solve_time
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}{log_label} value-subst mismatch check: "
            f"{solve_time:.3f}s, {len(replacements)} rewrite(s), result={result}",
        )
        if result == unsat:
            return True, solve_time
        return None, solve_time

    def _try_rewritten_noop_store_equivalence(
        self,
        solver,
        evm_array,
        x86_array,
        deadline: Optional[float],
        ctx,
        context: str,
        logs: Optional[list[str]],
        *,
        log_label: str,
        timeout_cap_ms: int,
        rewrite_count: int,
    ) -> tuple[Optional[bool], float]:
        """路径值重写后，证明单侧 Store 是 no-op。

        这个证明刻意不再携带完整路径：路径派生的等式已经代入 array，
        此时直接证明 ``Store(base, k, Select(base, k)) == base``，可以避免
        把无关分支算术继续拖进 solver。
        """
        try:
            from z3 import Z3_OP_STORE
        except Exception:
            return None, 0.0

        evm_array = _simplify_select_store_chains(evm_array)
        x86_array = _simplify_select_store_chains(x86_array)

        def _store_side(store_side, other):
            try:
                if not (
                    hasattr(store_side, "decl")
                    and store_side.decl().kind() == Z3_OP_STORE
                ):
                    return None
                base, key, value = store_side.children()
                if not _storage_store_chains_equal(base, other):
                    return None
                value = _simplify_select_store_chains(value)
                original_value = _simplify_select_store_chains(Select(other, key))
                return value, original_value
            except Exception:
                return None

        candidates = [
            _store_side(evm_array, x86_array),
            _store_side(x86_array, evm_array),
        ]
        candidates = [candidate for candidate in candidates if candidate is not None]
        if not candidates:
            return None, 0.0

        prefix = self._ctx.context_prefix(context)
        for value, original_value in candidates:
            try:
                if is_true(simplify(value == original_value)):
                    self._ctx.emit_solver_log(
                        logs,
                        f"    ├─ {prefix}{log_label} value-subst no-op Store check: "
                        f"0.000s, {rewrite_count} rewrite(s), select-store fast path",
                    )
                    return True, 0.0
            except Exception:
                pass
            if not self._ctx.reset_solver_with_capped_budget_for(
                solver,
                self._ctx.timeout_ms,
                deadline,
                timeout_cap_ms,
            ):
                return None, 0.0
            solver.add(value != original_value)
            start_time = time.time()
            result = solver.check()
            solve_time = time.time() - start_time
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label} value-subst no-op Store check: "
                f"{solve_time:.3f}s, {rewrite_count} rewrite(s), result={result}",
            )
            if result == unsat:
                return True, solve_time
        return None, 0.0

    def _prove_exprs_equal_under_path_with_solver(
        self,
        solver,
        left,
        right,
        path_conjuncts,
        deadline: Optional[float],
        ctx,
        logs: Optional[list[str]],
        context: str,
        *,
        log_label: str,
        timeout_cap_ms: int,
    ) -> bool:
        try:
            if not left.sort().eq(right.sort()):
                return False
        except Exception:
            return False
        if not self._ctx.reset_solver_with_capped_budget_for(
            solver,
            self._ctx.timeout_ms,
            deadline,
            timeout_cap_ms,
        ):
            return False
        try:
            solver.add(And(*path_conjuncts, left != right))
        except Exception:
            return False
        start_time = time.time()
        result = solver.check()
        solve_time = time.time() - start_time

        prefix = self._ctx.context_prefix(context)
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}{log_label}: {solve_time:.3f}s, result={result}",
        )
        return result == unsat

    def _prove_bv_exprs_equal_by_chunks_under_path(
        self,
        solver,
        left,
        right,
        path_conjuncts,
        deadline: Optional[float],
        ctx,
        logs: Optional[list[str]],
        context: str,
        *,
        log_label: str,
    ) -> bool:
        try:
            if not left.sort().eq(right.sort()):
                return False
            bit_width = left.size()
        except Exception:
            return False

        try:
            if is_true(simplify(left == right)):
                return True
        except Exception:
            pass

        chunk_timeout_ms = min(
            self._ctx.tuning.storage_store_noop_timeout_ms,
            10000,
        )

        def _prove_range(hi: int, lo: int) -> bool:
            left_chunk = Extract(hi, lo, left)
            right_chunk = Extract(hi, lo, right)
            if self._prove_exprs_equal_under_path_with_solver(
                solver,
                left_chunk,
                right_chunk,
                path_conjuncts,
                deadline,
                ctx,
                logs,
                context,
                log_label=f"{log_label} bits {hi}..{lo}",
                timeout_cap_ms=chunk_timeout_ms,
            ):
                return True
            if hi - lo + 1 <= 32:
                return False
            cur_hi = hi
            while cur_hi >= lo:
                cur_lo = max(lo, cur_hi - 31)
                if not _prove_range(cur_hi, cur_lo):
                    return False
                cur_hi = cur_lo - 1
            return True

        if bit_width == 256:
            ranges = [(255, 128), (127, 0)]
        else:
            ranges = [(bit_width - 1, 0)]

        for hi, lo in ranges:
            if not _prove_range(hi, lo):
                return False
        return True

    def _try_noop_store_fast_path(
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
        """证明 ``Store(base, key, value) == base`` 在当前路径下成立。"""
        if path_condition is None:
            return None
        try:
            from z3 import Z3_OP_STORE
        except Exception:
            return None

        path_conjuncts = collect_and_conjuncts(path_condition)
        weak_oracle = self._make_unsat_oracle(solver, deadline, ctx)

        def _check_store_side(store_side, other) -> bool:
            try:
                if not (
                    hasattr(store_side, "decl")
                    and store_side.decl().kind() == Z3_OP_STORE
                ):
                    return False
                base, key, value = store_side.children()
            except Exception:
                return False
            if not _storage_arrays_eq_under_path(
                base,
                other,
                path_conjuncts,
                weak_oracle,
            ):
                return False
            return self._prove_exprs_equal_under_path_with_solver(
                solver,
                value,
                Select(other, key),
                path_conjuncts,
                deadline,
                ctx,
                logs,
                context,
                log_label=f"{log_label} no-op Store value check",
                timeout_cap_ms=1000,
            ) or self._prove_bv_exprs_equal_by_chunks_under_path(
                solver,
                value,
                Select(other, key),
                path_conjuncts,
                deadline,
                ctx,
                logs,
                context,
                log_label=f"{log_label} no-op Store value chunk check",
            )

        if _check_store_side(evm_array, x86_array) or _check_store_side(
            x86_array,
            evm_array,
        ):
            prefix = self._ctx.context_prefix(context)
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}{log_label} equivalence check: "
                "~0s, path-aware no-op Store fast path",
            )
            return True, f"{success_subject} equivalent (path-aware no-op Store)"
        return None

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
        """尝试便宜且健全的 storage-like Array 结构性等价证明。"""
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

        path_conjuncts = collect_and_conjuncts(path_condition)
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
        return (
            expr_mentions_symbol(evm_storage, "CallDataSize")
            or expr_mentions_symbol(x86_storage, "CallDataSize")
        )

    def _storage_or_path_mentions_symbolic_calldatasize(
        self,
        evm_storage,
        x86_storage,
        path_condition,
    ) -> bool:
        return (
            self._storage_mentions_symbolic_calldatasize(
                evm_storage,
                x86_storage,
                path_condition,
            )
            or (
                path_condition is not None
                and expr_mentions_symbol(path_condition, "CallDataSize")
            )
        )

    def _calldatasize_partitions(self, ctx):
        calldata_size = BitVec("CallDataSize", 64, ctx=ctx)
        exact_limit = self._ctx.tuning.storage_calldatasize_exact_partition_limit
        for i in range(exact_limit):
            size_value = BitVecVal(i, 64, ctx=ctx)
            yield (
                f"size={i}",
                calldata_size == size_value,
                self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms,
                size_value,
            )
        yield (
            f"size>={exact_limit}",
            UGE(calldata_size, BitVecVal(exact_limit, 64, ctx=ctx)),
            self._ctx.tuning.storage_calldatasize_tail_partition_timeout_ms,
            None,
        )

    def _check_exact_storage_partition_worker(
        self,
        size: int,
        evm_storage,
        x86_storage,
        path_condition,
        deadline: Optional[float],
        context: str,
    ) -> tuple[int, bool, Optional[str], float, list[str]]:
        """在 fresh context 中检查一个精确 calldata-size storage partition。"""
        worker_ctx = Context()
        worker_solver = SolverFor("QF_AUFBV", ctx=worker_ctx)
        worker_logs: list[str] = []
        total_solve_time = 0.0

        with _STORAGE_TRANSLATE_LOCK:
            worker_evm_storage = evm_storage.translate(worker_ctx)
            worker_x86_storage = x86_storage.translate(worker_ctx)
            worker_path_condition = (
                path_condition.translate(worker_ctx)
                if path_condition is not None
                else None
            )
        calldata_size = BitVec("CallDataSize", 64, ctx=worker_ctx)
        size_value = BitVecVal(size, 64, ctx=worker_ctx)
        partition_condition = (
            And(worker_path_condition, calldata_size == size_value)
            if worker_path_condition is not None
            else calldata_size == size_value
        )
        try:
            replacements = ((calldata_size, size_value),)
            partition_condition = simplify(
                substitute(partition_condition, *replacements)
            )
            partition_evm_storage = simplify(
                substitute(worker_evm_storage, *replacements)
            )
            partition_x86_storage = simplify(
                substitute(worker_x86_storage, *replacements)
            )
        except Exception:
            partition_evm_storage = worker_evm_storage
            partition_x86_storage = worker_x86_storage

        partition_condition = _preprocess_partition_condition(
            partition_condition,
            worker_ctx,
        )

        fast_path = self._try_array_structural_fast_path(
            partition_evm_storage,
            partition_x86_storage,
            partition_condition,
            worker_solver,
            deadline,
            worker_ctx,
            context,
            worker_logs,
            log_label=f"Storage calldata-size split size={size}",
            success_subject="Storage",
        )
        if fast_path is not None:
            return size, True, None, total_solve_time, worker_logs

        store_chain_lengths_differ = _store_chain_lengths_differ(
            partition_evm_storage,
            partition_x86_storage,
        )
        if store_chain_lengths_differ:
            subst_result, subst_solve_time = (
                self._try_array_mismatch_unsat_with_path_value_substitution(
                    worker_solver,
                    partition_evm_storage,
                    partition_x86_storage,
                    deadline,
                    partition_condition,
                    worker_ctx,
                    context,
                    worker_logs,
                    log_label=f"Storage calldata-size split size={size}",
                    timeout_cap_ms=min(
                        self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms,
                        60000,
                    ),
                )
            )
            total_solve_time += subst_solve_time
            if subst_result is True:
                return size, True, None, total_solve_time, worker_logs

        result, solve_time = self._array_mismatch_query_with_solver(
            worker_solver,
            partition_evm_storage,
            partition_x86_storage,
            deadline,
            partition_condition,
            worker_ctx,
            timeout_cap_ms=(
                self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms
            ),
            key_name=f"storage_check_key_size_{size}",
        )
        total_solve_time += solve_time
        if result == unsat:
            return size, True, None, total_solve_time, worker_logs
        if result == sat:
            return (
                size,
                False,
                self._ctx.observable_counterexample_message(
                    "storage",
                    context,
                    f"size={size}",
                ),
                total_solve_time,
                worker_logs,
            )
        msg = self._ctx.unknown_message_for_solver(
            worker_solver,
            self._ctx.tuning.storage_calldatasize_exact_partition_timeout_ms,
        )
        if context:
            msg = f"{context}: {msg}"
        return size, False, msg, total_solve_time, worker_logs

    def _check_exact_storage_partitions_parallel(
        self,
        start_size: int,
        end_size: int,
        evm_storage,
        x86_storage,
        path_condition,
        deadline: Optional[float],
        context: str,
        logs: Optional[list[str]],
    ) -> tuple[bool, Optional[str], float]:
        """并行检查精确 calldata-size partition，范围两端都包含。"""
        sizes = list(range(start_size, end_size + 1))
        if not sizes:
            return True, None, 0.0
        max_workers = min(_STORAGE_EXACT_PARTITION_WORKERS, len(sizes))
        total_solve_time = 0.0
        start_time = time.time()
        prefix = self._ctx.context_prefix(context)
        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage calldata-size exact partitions "
            f"size={start_size}..{end_size}: checking with {max_workers} worker(s)",
        )
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [
                executor.submit(
                    self._check_exact_storage_partition_worker,
                    size,
                    evm_storage,
                    x86_storage,
                    path_condition,
                    deadline,
                    context,
                )
                for size in sizes
            ]
            for future in as_completed(futures):
                size, verified, msg, solve_time, worker_logs = future.result()
                total_solve_time += solve_time
                if self._ctx.verbose:
                    for line in worker_logs:
                        self._ctx.emit_solver_log(logs, line)
                if not verified:
                    return False, f"{msg} (size={size})" if msg else None, total_solve_time

        self._ctx.emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage calldata-size exact partitions "
            f"size={start_size}..{end_size}: "
            f"{time.time() - start_time:.3f}s wall / {total_solve_time:.3f}s solve",
        )
        return True, None, total_solve_time

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
        """对提到符号 CallDataSize 的 storage 查询做穷举切分。"""
        total_solve_time = 0.0
        start = time.time()
        calldata_size = BitVec("CallDataSize", 64, ctx=ctx)
        exact_limit = self._ctx.tuning.storage_calldatasize_exact_partition_limit
        skip_remaining_exact_partitions = False
        range_coalesce_attempted = False
        for (
            label,
            size_condition,
            partition_timeout_ms,
            exact_size_value,
        ) in self._calldatasize_partitions(ctx):
            if exact_size_value is not None and skip_remaining_exact_partitions:
                continue
            partition_condition = (
                And(path_condition, size_condition)
                if path_condition is not None
                else size_condition
            )
            partition_evm_storage = evm_storage
            partition_x86_storage = x86_storage
            if exact_size_value is not None:
                try:
                    replacements = ((calldata_size, exact_size_value),)
                    partition_condition = simplify(
                        substitute(partition_condition, *replacements)
                    )
                    partition_evm_storage = simplify(
                        substitute(evm_storage, *replacements)
                    )
                    partition_x86_storage = simplify(
                        substitute(x86_storage, *replacements)
                    )
                except Exception:
                    partition_evm_storage = evm_storage
                    partition_x86_storage = x86_storage
            partition_condition = _preprocess_partition_condition(
                partition_condition,
                ctx,
            )
            fast_path = self._try_array_structural_fast_path(
                partition_evm_storage,
                partition_x86_storage,
                partition_condition,
                solver,
                deadline,
                ctx,
                context,
                logs,
                log_label=f"Storage calldata-size split {label}",
                success_subject="Storage",
            )
            if fast_path is not None:
                continue

            store_chain_lengths_differ = _store_chain_lengths_differ(
                partition_evm_storage,
                partition_x86_storage,
            )
            exact_size_int = None
            if exact_size_value is not None:
                try:
                    exact_size_int = exact_size_value.as_long()
                except Exception:
                    exact_size_int = None

            if (
                store_chain_lengths_differ
                and exact_size_int is not None
                and exact_size_int < 32
            ):
                verified, msg, batch_solve_time = (
                    self._check_exact_storage_partitions_parallel(
                        exact_size_int,
                        exact_limit - 1,
                        evm_storage,
                        x86_storage,
                        path_condition,
                        deadline,
                        context,
                        logs,
                    )
                )
                total_solve_time += batch_solve_time
                if not verified:
                    if msg is None:
                        msg = self._ctx.timeout_message()
                    self._ctx.emit_solver_log(logs, f"    └─ {msg}")
                    return False, msg
                skip_remaining_exact_partitions = True
                continue

            if (
                exact_size_value is not None
                and path_condition is not None
                and not range_coalesce_attempted
                and store_chain_lengths_differ
            ):
                range_coalesce_attempted = True
                if (
                    exact_size_int is not None
                    and exact_size_int + 1 < exact_limit
                ):
                    range_condition = And(
                        path_condition,
                        UGE(
                            calldata_size,
                            BitVecVal(exact_size_int, 64, ctx=ctx),
                        ),
                        ULT(
                            calldata_size,
                            BitVecVal(exact_limit, 64, ctx=ctx),
                        ),
                    )
                    range_condition = _preprocess_partition_condition(
                        range_condition,
                        ctx,
                    )
                    if self._condition_unsat_probe_with_solver(
                        solver,
                        range_condition,
                        deadline,
                        logs,
                        context,
                        log_label=(
                            "Storage calldata-size feasibility split "
                            f"size={exact_size_int}..{exact_limit - 1}"
                        ),
                        timeout_cap_ms=(
                            self._ctx.tuning
                            .storage_calldatasize_tail_partition_timeout_ms
                        ),
                    ):
                        skip_remaining_exact_partitions = True
                        continue

            skip_partition_feasibility = (
                exact_size_value is not None
                and store_chain_lengths_differ
                and exact_size_int is not None
                and exact_size_int < 32
            )
            if not skip_partition_feasibility:
                partition_feasibility_timeout_ms = (
                    partition_timeout_ms
                    if exact_size_value is None
                    else (
                        self._ctx.tuning.storage_quick_timeout_ms
                        if store_chain_lengths_differ
                        else self._ctx.tuning.storage_path_feasibility_rescue_timeout_ms
                    )
                )
                if self._condition_unsat_probe_with_solver(
                    solver,
                    partition_condition,
                    deadline,
                    logs,
                    context,
                    log_label=f"Storage calldata-size feasibility split {label}",
                    timeout_cap_ms=partition_feasibility_timeout_ms,
                ):
                    continue

            if store_chain_lengths_differ:
                subst_timeout_ms = min(partition_timeout_ms, 60000)
                subst_result, subst_solve_time = (
                    self._try_array_mismatch_unsat_with_path_value_substitution(
                        solver,
                        partition_evm_storage,
                        partition_x86_storage,
                        deadline,
                        partition_condition,
                        ctx,
                        context,
                        logs,
                        log_label=f"Storage calldata-size split {label}",
                        timeout_cap_ms=subst_timeout_ms,
                    )
                )
                total_solve_time += subst_solve_time
                if subst_result is True:
                    continue

            result, solve_time = self._array_mismatch_query_with_solver(
                solver,
                partition_evm_storage,
                partition_x86_storage,
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
            if self._path_condition_unsat_rescue_with_solver(
                partition_condition,
                deadline,
                logs,
                ctx,
                context,
                log_label=f"Storage calldata-size feasibility split {label}",
            ):
                continue
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
        (evm_storage, x86_storage), rewrite_count = (
            _rewrite_exprs_with_path_value_substitutions(
                path_condition,
                evm_storage,
                x86_storage,
            )
        )
        if rewrite_count:
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage path-value rewrite: "
                f"{rewrite_count} concrete path fact(s)",
            )
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

        storage_mentions_calldatasize = self._storage_mentions_symbolic_calldatasize(
            evm_storage,
            x86_storage,
            path_condition,
        )
        if self._storage_or_path_mentions_symbolic_calldatasize(
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

            if self._path_condition_unsat_rescue_with_solver(
                path_condition,
                deadline,
                logs,
                ctx,
                context,
            ):
                self._ctx.emit_solver_log(
                    logs,
                    f"    ├─ {prefix}Storage equivalence check: "
                    "vacuous under infeasible path condition",
                )
                return True, "Storage equivalent (infeasible path)"

            if not storage_mentions_calldatasize:
                # storage 表达式已不再依赖 CallDataSize；继续按 calldata size 切分
                # 只会重复同一个 array 查询。这里落回下方完整的非 partition 检查。
                pass
            else:
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

        if self._path_condition_unsat_rescue_with_solver(
            path_condition,
            deadline,
            logs,
            ctx,
            context,
        ):
            self._ctx.emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage equivalence check: "
                "vacuous under infeasible path condition",
            )
            return True, "Storage equivalent (infeasible path)"

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
