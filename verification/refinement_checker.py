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
_PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS = 250
_STORAGE_QUICK_TIMEOUT_CAP_MS = 750
_STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT = 68
_STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS = 30000
_PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS = 200


@dataclass
class _PathPairChunkCheckResult:
    checked_pair_count: int
    verified: bool
    message: Optional[str]
    logs: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class _RefinementCheckTuning:
    """Small timeout and partition knobs used by refinement sub-checks."""

    path_pair_feasibility_timeout_ms: int
    storage_quick_timeout_ms: int
    storage_calldatasize_exact_partition_limit: int
    storage_calldatasize_exact_partition_timeout_ms: int
    storage_calldatasize_tail_partition_timeout_ms: int
    path_structural_oracle_timeout_ms: int

    @classmethod
    def for_timeout(cls, timeout_ms: int) -> "_RefinementCheckTuning":
        storage_quick_timeout_ms = min(timeout_ms, _STORAGE_QUICK_TIMEOUT_CAP_MS)
        return cls(
            path_pair_feasibility_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS,
            ),
            storage_quick_timeout_ms=storage_quick_timeout_ms,
            storage_calldatasize_exact_partition_limit=(
                _STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT
            ),
            storage_calldatasize_exact_partition_timeout_ms=min(
                timeout_ms,
                max(storage_quick_timeout_ms, 1000),
            ),
            storage_calldatasize_tail_partition_timeout_ms=min(
                timeout_ms,
                _STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS,
            ),
            path_structural_oracle_timeout_ms=min(
                timeout_ms,
                _PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS,
            ),
        )


def _storage_arrays_structurally_equal(a, b) -> bool:
    """快速结构等价检查（同一 Z3 AST 实例或 hash 相等）。

    Z3 表达式是 maximally shared 的（同一 AST manager 下相同表达式共享同一指针），
    因此当两个 path 在同一 base Storage Array 上做了相同序列的 SSTORE，最终的
    Store-chain 表达式会 hash 相等。这种情况下 storage equivalence 是平凡的，
    可以跳过 z3 全 256-bit 量化 SAT。

    保守起见：不等于不代表 z3 也不等价（只是这条 fast path miss），所以这是
    sound 的——只是 perf 优化。
    """
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
    """将一个 Z3 Array 表达式分解为 (base_array, [(key, value), ...]) 形式。

    递归剥离顶层 Store(arr, k, v)；剩下的 base 是非 Store-rooted 表达式
    （通常是初始 Array constant 或更复杂的合并 If）。返回的 key/value 列表
    顺序对应写入顺序：列表最后一项是最近一次写入。如果遇到非 Store 节点
    立即停止。
    """
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
    """递归地按 AST 结构判断两个 Z3 Array 表达式是否等价。

    支持穿透 Store / If 节点：
    - Store(base_a, ka, va) ≡ Store(base_b, kb, vb)
      iff base_a ≡ base_b ∧ ka ≡ kb ∧ va ≡ vb
    - If(c_a, t_a, e_a) ≡ If(c_b, t_b, e_b)
      iff c_a ≡ c_b ∧ t_a ≡ t_b ∧ e_a ≡ e_b
    - 叶节点：用 z3.eq AST 相等（处理 BitVecVal, Const 等）

    这是 sufficient（不 necessary）：返回 True 时两侧 Z3 Array 严格 syntactic
    相等，因此 Storage equivalence 平凡成立；返回 False 不代表语义不等价，
    只是 fast path miss，会 fallback 到 z3 SAT。
    """
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
    """把一个 BoolRef 展平成它的 And-conjunct 列表（递归穿透嵌套 And）。

    用于 path-condition-aware 的 If 守卫 syntactic 匹配：path_condition
    在 path-pair 检查里通常是 `And(evm_cond, x86_cond)`，其中 evm/x86_cond
    自己又是 `And(*conjuncts)`。展平后我们才能 O(N) 查找某个守卫表达式
    是否作为 conjunct 出现。
    """
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
    """如果 target syntactic 出现在 conjuncts 中，返回 True；否则 False。

    这里不调 solver；不确认即返回 False，交给后续 oracle 或完整 SAT 检查。
    """
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
    """对一个 ITE 节点 `If(C, then, else)`，在给定 path_condition（已展平的
    conjuncts list）下判断哪一支被 "选中"。

    返回值：
    - 0 表示 path_condition ⇒ C，应取 then 分支
    - 1 表示 path_condition ⇒ ¬C，应取 else 分支
    - None 表示无法判断（fast path miss）

    syntactic 优先（O(|conjuncts|)），失败再用可选的 solver_check。
    solver_check(expr) 应当返回 True 当且仅当 expr unsat（即该方向可剪枝）。
    传 None 则跳过 solver，纯靠 syntactic 匹配。
    """
    children = if_expr.children()
    if len(children) != 3:
        return None
    cond, then_branch, else_branch = children

    # 1) syntactic: C ∈ conjuncts? then-branch active.
    if _bool_implied_by_conjuncts(path_conjuncts, cond):
        return 0
    # 2) syntactic: ¬C ∈ conjuncts? else-branch active. 也接受 conjuncts
    #    中出现 NotOf(C)（即 children[0] of cond 若 cond 自身是 Not）。
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
    """path-condition-aware 版本的 Storage AST 等价比较。

    与 _storage_arrays_syntactically_equal 的差别：遇到一侧是 If(C, T, E)
    而另一侧不是 If（或形状不同），尝试在 path_condition 下确定 If 被
    "压平" 到 T 还是 E，递归比较选中支。

    **Sound case-splitting**：当 path_condition 不能 syntactic 或 oracle
    entail `C` / `¬C` 时（典型情况：merged state 的 constraints 是
    `Or(C1,C2,...)`，pair path_condition 包含的是这个 Or 而非具体 C_i），
    回退到 case split：要求 `then` 分支在 `path ∧ C` 下、`else` 分支在
    `path ∧ ¬C` 下都与对侧等价。这两支若都 holds 则不论 C 真假都等价
    (codex review 2026-05-21 的关键建议)。

    `max_depth` 用于避免病态 If 嵌套深度爆栈/卡死；命中 cap 时返回 False。

    sound：返回 True 时两个 Storage 在 path_condition 约束下等价；False 时
    fast path miss，调用方会 fallback 到 z3 SAT。
    """
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
    """处理单侧 ITE：先尝试 entailment 选支，否则 case-split.

    sound: case-split 要求两侧都成立。
    """
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
    """更深一层结构性等价：递归走 Store / If 节点比较 AST 形态。

    sufficient（不 necessary）条件：两侧 Z3 Array 在 store/if 树上 syntactic
    相等。返回 True 时 sound（两个 Z3 Array 等价）；False 时 fast path miss。

    应用场景：path_observations + enable_merge 模式下，x86 的 storage 通常
    是嵌套 If(cond_i, store_chain_i, fallback)；EVM 侧没合并，是简单的
    Store 链。两边都基于同一 base `Array('Storage', ...)`、SSTORE 的 (k,v)
    表达式按 AST 一致（因为两侧 sstore 共享 EVMStorageState.sstore），所以
    顶层结构应当 syntactically 匹配。
    """
    if a is None or b is None:
        return False
    return _storage_arrays_syntactically_equal(a, b)


class RefinementChecker:
    """检查x86和EVM语义之间的精化关系。
    
    验证x86精化EVM：对所有输入，x86_output = EVM_output。
    """
    
    def __init__(self, timeout_ms: int = 60000, verbose: bool = False,
                 z3_verbose: bool = False):
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

    def _make_unsat_oracle(self, _parent_solver, deadline: Optional[float], ctx):
        """返回一个闭包 oracle(expr) -> bool 用于 path-aware structural fast path。

        语义：oracle(expr) 返回 True 当且仅当 expr 在很短预算内被证 unsat。
        - 用独立的 short-timeout solver，与外层 storage SAT fallback 隔离。
        - `_unsat_oracle_cache` 按 context/hash 分桶；复用前检查 AST equality。
        - 任何 unknown / sat / 异常返回 False（保守，sound）。

        如果 ctx 不是 None（worker-local Context），用同一 ctx 创建独立 solver；
        否则用 main context。
        """
        # 这是 path-aware fast path 内部的 implication 探测预算，不影响外层
        # storage fallback 的完整 solver budget。
        local_budget_ms = self._tuning.path_structural_oracle_timeout_ms
        cache_miss = object()

        def _cache_key(expr):
            try:
                return (id(expr.ctx), expr.hash())
            except Exception:
                return None

        def _lookup_cached(expr, key):
            from z3 import eq as _z3_eq

            with self._unsat_oracle_cache_lock:
                for cached_expr, cached_result in self._unsat_oracle_cache.get(key, []):
                    try:
                        if _z3_eq(cached_expr, expr):
                            return cached_result
                    except Exception:
                        continue
            return cache_miss

        def _remember_result(expr, key, result: bool) -> None:
            from z3 import eq as _z3_eq

            with self._unsat_oracle_cache_lock:
                bucket = self._unsat_oracle_cache.setdefault(key, [])
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
        if not self._reset_solver_with_capped_budget_for(
            solver,
            self.timeout_ms,
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
        prefix = self._context_prefix(context)
        if _storage_store_chains_equal(evm_array, x86_array):
            self._emit_solver_log(
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
            self._emit_solver_log(
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
        exact_limit = self._tuning.storage_calldatasize_exact_partition_limit
        for i in range(exact_limit):
            yield (
                f"size={i}",
                calldata_size == BitVecVal(i, 64, ctx=ctx),
                self._tuning.storage_calldatasize_exact_partition_timeout_ms,
            )
        yield (
            f"size>={exact_limit}",
            UGE(calldata_size, BitVecVal(exact_limit, 64, ctx=ctx)),
            self._tuning.storage_calldatasize_tail_partition_timeout_ms,
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
        """Exhaustive split for storage queries mentioning symbolic CallDataSize.

        Instead of asking Z3 to solve one large formula with symbolic
        CallDataSize in many byte-range guards, prove the same storage mismatch
        query over a complete uint64 partition: exact sizes below
        ``storage_calldatasize_exact_partition_limit`` plus one unsigned tail.

        The limit is a performance knob, not a semantic assumption.  Soundness
        comes from each subquery keeping the original path condition and storage
        expressions while adding one constraint from this exhaustive partition.
        """
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
                msg = self._timeout_message()
                self._emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            if result == unsat:
                continue
            prefix = self._context_prefix(context)
            self._emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage calldata-size split {label}: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == sat:
                msg = self._observable_counterexample_message(
                    "storage",
                    context,
                    label,
                )
                self._emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            msg = self._unknown_message_for_solver(solver, partition_timeout_ms)
            self._emit_solver_log(logs, f"    └─ {msg} ({label})")
            return False, msg

        prefix = self._context_prefix(context)
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage equivalence check: "
            f"{time.time() - start:.3f}s wall / {total_solve_time:.3f}s solve, "
            "calldatasize partition",
        )
        return True, "Storage equivalent (calldatasize partition)"

    def _emit_solver_log(self, logs: Optional[list[str]], line: str) -> None:
        if not self.verbose:
            return
        if logs is None:
            print(line)
        else:
            logs.append(line)
    
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
        deadline = time.time() + (self.timeout_ms / 1000.0)

        return self._check_refinement_direct_memory(
            evm_result, x86_result, deadline,
            path_condition=assumptions,
        )

    def check_refinement_paths(
        self,
        evm_results: list[dict],
        x86_results: list[dict],
        path_pair_workers: int = 1,
        skip_feasibility: bool = False,
    ) -> Tuple[bool, Optional[str]]:
        """Check refinement directly over terminal path observations.

        This avoids first merging whole terminal memory/storage arrays.  For each
        feasible EVM/x86 terminal-path intersection, it proves the same
        observable properties as ``check_refinement``.

        Args:
            skip_feasibility: 跳过 ``_check_path_pair_may_be_feasible`` 预检查。
                在符号 calldata 等场景下，feasibility precheck 自身也要 bit-blast
                完整 path 谓词但很少能剪枝；跳过它能少做大约 pair_count 次 SAT 调用。
                refinement check 在 path_condition 为 UNSAT 时返回 unsat（vacuously
                refined），仍 sound——只是会把统计的 "feasible pair(s)" 计成全部
                pair_count。
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
                skip_feasibility=skip_feasibility,
            )
        else:
            checked_pair_count, pair_count, failure = self._check_path_pairs_parallel(
                evm_results,
                x86_results,
                deadline,
                path_pair_workers,
                skip_feasibility=skip_feasibility,
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
        skip_feasibility: bool = False,
    ) -> tuple[int, int, Optional[str]]:
        pair_count = 0
        checked_pair_count = 0
        for evm_index, evm_result in enumerate(evm_results):
            evm_condition = evm_result.get("condition", BoolVal(True))
            for x86_index, x86_result in enumerate(x86_results):
                x86_condition = x86_result.get("condition", BoolVal(True))
                path_condition = And(evm_condition, x86_condition)
                pair_count += 1
                if not skip_feasibility:
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
        skip_feasibility: bool = False,
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
                    skip_feasibility,
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
        skip_feasibility: bool = False,
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

            if not skip_feasibility:
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
        if not self._reset_solver_with_capped_budget_for(
            solver,
            self.timeout_ms,
            deadline,
            self._tuning.path_pair_feasibility_timeout_ms,
        ):
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

        prefix = self._context_prefix(context)
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
                timeout_cap_ms=self._tuning.storage_quick_timeout_ms,
                key_name="storage_check_key_quick",
            )
            if result is None:
                msg = self._timeout_message()
                self._emit_solver_log(logs, f"    └─ {msg}")
                return False, msg
            self._emit_solver_log(
                logs,
                f"    ├─ {prefix}Storage equivalence quick check: "
                f"{solve_time:.3f}s, result={result}",
            )
            if result == unsat:
                return True, "Storage equivalent"
            if result == sat:
                msg = self._observable_counterexample_message("storage", context)
                self._emit_solver_log(logs, f"    └─ {msg}")
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
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Storage equivalence check: {solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Storage equivalent"
        if result == sat:
            msg = self._observable_counterexample_message("storage", context)
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
            msg = self._timeout_message()
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        prefix = self._context_prefix(context)
        self._emit_solver_log(
            logs,
            f"    ├─ {prefix}Transient storage equivalence check: "
            f"{solve_time:.3f}s, result={result}",
        )

        if result == unsat:
            return True, "Transient storage equivalent"
        if result == sat:
            msg = self._observable_counterexample_message(
                "transient storage",
                context,
            )
            self._emit_solver_log(logs, f"    └─ {msg}")
            return False, msg

        msg = self._unknown_message_for_solver(solver, self.timeout_ms)
        self._emit_solver_log(logs, f"    └─ {msg}")
        return False, msg
