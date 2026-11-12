"""
x86-64 全局状态管理（参考 evm_ir）。

定义 X86WorldState、X86Constraints 和 X86GlobalState 类。
"""

from __future__ import annotations

import os
import time
from contextlib import contextmanager
from typing import List, Optional, Dict, TYPE_CHECKING
from z3 import (BoolRef, BoolVal, Solver, SolverFor, unsat, sat, unknown, is_true, And, simplify,
                Z3_get_estimated_alloc_size, Z3Exception, set_param)

from state.smt_state import SMTState

# 用于类型注解的前向引用
if TYPE_CHECKING:
    from .cfg_structures import X86CFGNode
    from .cfg_annotations import X86StateAnnotation

DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS = 1000
# A reachability budget of T ms is enforced as Z3's deterministic resource
# limit (T * RLIMIT_PER_MS), so which checks come back unknown -- and hence
# how many infeasible paths survive -- no longer depends on machine load.
# Calibrated with REACH_STATS_FILE on Safe pc=5377 under the old 1s wall
# budget (load ~5, 1351 checks): Z3 spends ~3.4k rlimit/ms (median, 2.0k-6.8k
# p10-p90); timed-out checks had spent up to 10.2M, decided ones <= 8.5M.
# x86 paths vs rate: 5000/ms -> 185, 7500 -> 177, 10000 -> 172 (1s wall: 176-263),
# and 10000 costs less total rlimit than 5000 (fewer paths, fewer checks).
# The wall clock is only a safety net for pathological tactics.
REACHABILITY_RLIMIT_PER_MS = 10000
REACHABILITY_WALL_SAFETY_FACTOR = 10
# A path kept without a witness makes every later check on it pay a full solve. Its blasted
# form usually has a model at a few times the slot: Aave 7200's five SAT kept queries took
# 6.7-31M rlimit and 1.4-3.7s (none within 10M). So for such a path, a blasted search at
# WITNESS_SEARCH_FACTOR slots, from a per-run wall budget (ponytail: 1800s, 4% of a 12h node).
WITNESS_SEARCH_FACTOR = 5
WITNESS_SEARCH_WALL_MS = 15000
WITNESS_SEARCH_SECONDS = 1800
# A check may add at most this much to Z3's memory; above it Z3 stops with "max. memory exceeded",
# the answer is unknown and the path is kept. ponytail: 1 GB; PoolManager 22747 grew +1.5 GB in one
# reachability check after a DIV summary and +2.3 GB in the next 10s (the servers' 15-24 GB spikes
# that killed whole process pools). The solver parameter max_memory is ignored by incremental
# solvers (PrefixSolver), and an interrupt is honoured only tens of seconds later, so the cap is
# Z3's process-wide memory_high_watermark_mb, set around the check only. Not memory_max_size: that
# one throws out_of_memory_error from the allocator itself, also where nothing can catch it, and
# the process aborts (servers, PoolManager 18089: SIGABRT inside Z3_solver_check_assumptions). The
# high watermark is only read at Z3's cooperative checkpoints, the points where a timeout or an
# interrupt stops a solver, so it ends like them: unknown, or a Z3Exception, and Z3 stays usable.
REACHABILITY_MEMORY_MB = 1024
_WATCH = {"tripped": False}
_CAPS = []  # active caps in MB, innermost last
_MEMORY_STOPS = ("max. memory exceeded", "out of memory")  # Z3's words for a stop at the cap
_CAP_CANCELS = ("canceled", "Resource limits hit")  # a stop at the cap, or a timeout/interrupt
_LAST_EXIT = {"over": False}  # whether Z3 held at least the cap when the last capped block ended


@contextmanager
def z3_memory_cap(mb=None):
    """Z3 may allocate at most `mb` (default REACHABILITY_MEMORY_MB) more inside
    the block (and never more than an enclosing cap); beyond it Z3 stops at its
    next checkpoint: the call answers unknown or raises a Z3Exception (see
    out_of_memory), it never aborts the process. Under a node memory budget
    (common.node_monitor) also at most half the node's remaining headroom, so
    that gradual growth inside one call ends that call (unknown) before it ends
    the node. Neither bounds a single step without a checkpoint (bit-blasting a
    512-bit division: ~500 MB at once); the node budget's hard limit does."""
    from common.node_monitor import memory_headroom_mb  # lazy: layer order
    extra = REACHABILITY_MEMORY_MB if mb is None else mb
    headroom = memory_headroom_mb()
    if headroom is not None:
        # Half: the cap counts Z3's own allocations, while the process grew ~1.6x that in RSS
        # (allocator overhead, untracked buffers), and Z3 stops only at its next checkpoint.
        extra = max(1, min(extra, headroom // 2))
    limit = Z3_get_estimated_alloc_size() // 2**20 + extra
    _CAPS.append(min(limit, _CAPS[-1]) if _CAPS else limit)
    set_param("memory_high_watermark_mb", _CAPS[-1])
    try:
        yield
    finally:
        _LAST_EXIT["over"] = _at_cap()
        _CAPS.pop()
        set_param("memory_high_watermark_mb", _CAPS[-1] if _CAPS else 0)  # 0: unlimited


def _at_cap():
    """Whether Z3 holds (nearly) the innermost active cap."""
    return bool(_CAPS) and Z3_get_estimated_alloc_size() // 2**20 >= _CAPS[-1] - 16


def out_of_memory(exc):
    """Whether a Z3Exception (or a solver's reason_unknown) is a stop at a
    z3_memory_cap() (recorded for memory_tripped()). Some checkpoints above the
    watermark report "canceled" (a push or add there: "Resource limits hit in
    push", Aave 7200 after 54 min), which a timeout or an interrupt reports too:
    it counts only while Z3 holds the cap (inside the block), or held it when
    the last capped block ended (an exception handled after it)."""
    text = str(exc)
    if not (any(word in text for word in _MEMORY_STOPS)
            or any(word in text for word in _CAP_CANCELS) and (_at_cap() if _CAPS else _LAST_EXIT["over"])):
        return False
    _WATCH["tripped"] = True
    return True


def _bounded_check(solver, timeout_ms, tag, wall_ms=None):
    """solver.check() under the reachability budget; any non-UNSAT keeps the path.

    `wall_ms` replaces the wall-clock safety net (timeout_ms x the factor) for
    callers whose budget is a wall-clock budget against a deadline. The check
    may add at most REACHABILITY_MEMORY_MB to Z3's memory, else it is unknown;
    memory_tripped() says whether the last one was stopped for that."""
    if timeout_ms is not None and timeout_ms > 0:
        cap = 2**32 - 1  # both are unsigned-int Z3 params
        wall = timeout_ms * REACHABILITY_WALL_SAFETY_FACTOR if wall_ms is None else max(wall_ms, 1)
        solver.set("rlimit", min(timeout_ms * REACHABILITY_RLIMIT_PER_MS, cap))
        solver.set("timeout", min(wall, cap))
    _WATCH["tripped"] = False
    try:
        with z3_memory_cap():
            result = _check(solver, tag)
            if result == unknown:
                out_of_memory(solver.reason_unknown())  # records a stop at the cap
    except Z3Exception as exc:
        if not out_of_memory(exc):
            raise
        return unknown
    return result


def _check(solver, tag):
    stats = os.environ.get("REACH_STATS_FILE")
    if not stats:
        return solver.check()
    # Diagnostic: "tag result seconds rlimit-spent". Z3's "rlimit count" is
    # cumulative per context, so spent = after - before.
    before = solver.statistics().get_key_value("rlimit count")
    started = time.monotonic()
    result = solver.check()
    spent = solver.statistics().get_key_value("rlimit count") - before
    with open(stats, "a") as log:
        log.write(f"{tag} {result} {time.monotonic() - started:.4f} {spent}\n")
    return result


def memory_tripped():
    """Whether the last _bounded_check was interrupted for memory."""
    return _WATCH["tripped"]


class PrefixSolver:
    """One incremental solver, one push scope per conjunct.

    A query pops back to the longest common prefix (by AST id) with the
    previous query and pushes the rest, so sibling and descendant paths reuse
    the internalized terms and learned clauses (Safe 5377: 958 reachability
    queries 482s -> 86s). At every check the assertions are exactly
    `conjuncts`: pop retracts a scope's assertion together with every clause
    learned from it, so UNSAT here is UNSAT of the conjunction. The asserted
    ASTs are kept in `stack`, which keeps their ids from being reused.

    That needs scope k to hold exactly stack[k]. An exception between push,
    add and append (an interrupt, a Z3 error) could break it and leave an
    assertion no query asked for, so any failure while syncing resets the
    solver, and a scope count off from `stack` resets it before the check.
    """

    def __init__(self, solver=None):
        self.solver = solver if solver is not None else SolverFor("QF_AUFBV")
        self.stack: List[BoolRef] = []
        # Wall seconds this run may still spend on witness searches (X86Constraints._is_possible).
        self.witness_seconds = WITNESS_SEARCH_SECONDS

    def reset(self):
        self.solver.reset()
        self.stack = []

    def check(self, conjuncts, timeout_ms, tag="incremental", wall_ms=None):
        if self.solver.num_scopes() != len(self.stack):
            self.reset()
        common = 0
        for old, new in zip(self.stack, conjuncts):
            if old.ctx is not new.ctx or old.get_id() != new.get_id():
                break
            common += 1
        try:
            if len(self.stack) > common:
                self.solver.pop(len(self.stack) - common)
                del self.stack[common:]
            for conjunct in conjuncts[common:]:
                self.solver.push()
                self.stack.append(conjunct)
                self.solver.add(conjunct)
        except BaseException:
            self.reset()
            raise
        result = _bounded_check(self.solver, timeout_ms, tag, wall_ms)
        if memory_tripped():
            self.reset()  # drop what the interrupted check built (an unknown keeps the path)
        return result


class X86Constraints:
    """x86-64 约束条件集合。

    参考 evm_ir 的 Constraints 类，扩展支持 CPU 标志约束。
    """

    def __init__(self):
        """初始化约束集合。"""
        self._constraints: List[BoolRef] = [BoolVal(True)]
        self.flag_constraints: Dict[str, BoolRef] = {}  # CPU 标志: CF, ZF, SF, OF
        # Last satisfying model found on this path (shared with forks): a
        # concrete witness, so a branch it satisfies needs no solver call.
        self._witness = None

    def add(self, constraint: BoolRef) -> None:
        """添加约束。

        Args:
            constraint: 要添加的布尔约束
        """
        self._constraints.append(constraint)

    def add_flag_constraint(self, flag: str, condition: BoolRef) -> None:
        """添加 CPU 标志约束。

        Args:
            flag: 标志名称（CF, ZF, SF, OF）
            condition: 标志条件的布尔约束
        """
        self.flag_constraints[flag] = condition

    def __copy__(self):
        """浅拷贝约束。

        创建新的 Constraints 对象和新的约束列表（但列表中的 Z3 表达式是共享的）。
        这与 evm_ir 的实现一致，确保后续添加约束不会影响原状态。

        Returns:
            新的 X86Constraints 实例，包含新的约束列表
        """
        new_constraints = X86Constraints()
        # 复制列表内容，而不是共享引用
        # Z3 表达式是不可变的，所以共享列表元素是安全的
        new_constraints._constraints = self._constraints.copy()
        new_constraints.flag_constraints = self.flag_constraints.copy()
        new_constraints._witness = self._witness
        return new_constraints

    def __deepcopy__(self, memo):
        """深拷贝约束。

        Returns:
            新的 X86Constraints 实例，复制约束列表
        """
        import copy
        new_constraints = X86Constraints()
        new_constraints._constraints = copy.deepcopy(self._constraints, memo)
        new_constraints.flag_constraints = copy.deepcopy(self.flag_constraints, memo)
        new_constraints._witness = self._witness
        return new_constraints

    def __iter__(self):
        """迭代约束。"""
        return iter(self._constraints)

    def __len__(self):
        """约束数量。"""
        return len(self._constraints)

    def is_possible(self, solver_timeout: Optional[int] = None,
                    prefix_solver: Optional[PrefixSolver] = None) -> bool:
        """检查约束是否可满足（可达性检查）。

        Args:
            solver_timeout: 求解器超时时间（毫秒）
            prefix_solver: 执行器持有的增量 solver（见 PrefixSolver）；None
                时每次新建 solver

        Returns:
            如果约束可满足则返回 True

        The whole check (witness evaluation, solver calls, the blasted fallback)
        may add at most REACHABILITY_MEMORY_MB to Z3's memory: pruning only, so
        out of memory keeps the path (and resets the incremental solver).
        """
        try:
            with z3_memory_cap():
                return self._is_possible(solver_timeout, prefix_solver)
        except Z3Exception as exc:
            if not out_of_memory(exc):
                raise
            if prefix_solver is not None:
                prefix_solver.reset()
            self._witness = None
            return True

    def _is_possible(self, solver_timeout, prefix_solver):
        # A model under which the whole path condition evaluates to true is a
        # sat witness: the solver could only answer sat (or time out -> keep).
        # Pruning below still requires an explicit UNSAT, so this only skips
        # calls whose outcome is already "keep". At a fork the parent's model
        # satisfies exactly one branch, halving the solver calls.
        if self._witness is not None and is_true(
                self._witness.eval(self.as_bool(), model_completion=True)):
            return True
        timeout_ms = (
            solver_timeout
            if solver_timeout is not None
            else DEFAULT_REACHABILITY_SOLVER_TIMEOUT_MS
        )
        from verification.block_equivalence import abstract_nonlinear_mul  # lazy: layer cycle
        from common.isolated_sat import expensive_bitblast, isolated_sat
        path = self.as_bool()
        if expensive_bitblast(path):
            # PrefixSolver.push internalizes bit-vectors before check's limits
            # take effect. Keep the entire expensive path out of that solver.
            self._witness = None
            wall = timeout_ms * REACHABILITY_WALL_SAFETY_FACTOR
            rlimit = timeout_ms * REACHABILITY_RLIMIT_PER_MS
            result = isolated_sat(path, wall, rlimit=rlimit)
            if result != "unknown":
                return result != "unsat"
            result = isolated_sat(path, wall, blast=True, rlimit=rlimit)
            if result != "unknown":
                return result != "unsat"
            return isolated_sat(path, wall, rlimit=rlimit, refute_probe=True) != "unsat"
        if prefix_solver is not None:
            # Exact query first, incrementally (same rlimit budget). Only an
            # unknown pays for the bvmul->UF probe on a fresh solver: its UNSAT
            # is exact UNSAT (see below); anything else keeps the path.
            conjuncts = list(self._constraints) + list(self.flag_constraints.values())
            result = prefix_solver.check(conjuncts, timeout_ms)
            self._witness = prefix_solver.solver.model() if result == sat else None
            if result != unknown:
                return result == sat
            # Reads through store chains over lambda arrays (symbolic-length copy
            # results) defeat model construction: Aave 7200 x86 paths stay unknown at
            # 30-40s, so the path loses its witness and every later check and summary
            # entry pays a full solve. Blasted into ites (an exact rewrite) the same
            # query is SAT in ~4s. Its UNSAT is exact; a model counts as the path's
            # witness only if it makes the path condition literally true.
            # Building the blasted term counts against the check's memory cap too (PoolManager
            # 22747: +2 GB in one fallback); out of memory keeps the path.
            path = self.as_bool()
            try:
                with z3_memory_cap():
                    blasted = SolverFor("QF_AUFBV")
                    blasted.add(simplify(path, blast_select_store=True))
                    result = _bounded_check(blasted, timeout_ms, "blast")
                    if result == unsat:
                        return False
                    if result == sat:
                        model = blasted.model()
                        if is_true(model.eval(path, model_completion=True)):
                            self._witness = model
                        return True
                    # The last fallback keeps its original whole-slot budget;
                    # all multiplication/potential preparation stays in one child.
                    if isolated_sat(path, timeout_ms * REACHABILITY_WALL_SAFETY_FACTOR,
                                    rlimit=timeout_ms * REACHABILITY_RLIMIT_PER_MS,
                                    refute_probe=True) == "unsat":
                        return False
                    # Kept without a witness: one larger search on the same blasted query.
                    # Same rules as above: UNSAT is exact, a model counts only if literal.
                    if prefix_solver.witness_seconds > 0:
                        started = time.monotonic()
                        wall = min(WITNESS_SEARCH_WALL_MS, int(prefix_solver.witness_seconds * 1000))
                        try:  # the model and its check are part of the search's cost
                            result = _bounded_check(blasted, timeout_ms * WITNESS_SEARCH_FACTOR, "witness", wall)
                            if result == unsat:
                                return False
                            if result == sat:
                                model = blasted.model()
                                if is_true(model.eval(path, model_completion=True)):
                                    self._witness = model
                        finally:
                            prefix_solver.witness_seconds = max(
                                0.0, prefix_solver.witness_seconds - (time.monotonic() - started))
                    return True
            except Z3Exception as exc:
                if not out_of_memory(exc):
                    raise
                return True
        # 全符号场景下，calldata/storage 是 Z3 Array，约束含 Array Select。默认的
        # 通用 Solver() 会尝试组合多种理论，bit-blast 慢；QF_AUFBV 直接走 array
        # + bit-vector + uninterpreted-function tactic，对我们用到的形式更快。
        solver = SolverFor("QF_AUFBV")
        for constraint in self._constraints:
            solver.add(constraint)
        for flag_cond in self.flag_constraints.values():
            solver.add(flag_cond)

        # Symbolic memory-expansion gas (words*words) puts 64-bit multipliers
        # in the path condition. Refute first with bvmul abstracted to a UF:
        # every real model extends to the abstraction, so its UNSAT is exact
        # UNSAT (2-4x faster on those paths); SAT/unknown there proves nothing
        # and falls through to the exact query below.
        relaxed, changed = abstract_nonlinear_mul(self.as_bool())
        if changed:
            probe = SolverFor("QF_AUFBV")
            probe.add(simplify(relaxed, blast_select_store=True))
            if _bounded_check(probe, timeout_ms, "probe") == unsat:
                self._witness = None
                return False

        result = _bounded_check(solver, timeout_ms, "exact")
        self._witness = solver.model() if result == sat else None
        # 仅当明确 UNSAT 时才剪枝；UNKNOWN 视为可能可达，避免不声音剪枝。
        return result != unsat

    def as_bool(self) -> BoolRef:
        """将约束集合转换为单个 BoolRef（合取）。

        Returns:
            所有约束的合取
        """
        all_constraints = list(self._constraints) + list(self.flag_constraints.values())
        if len(all_constraints) == 0:
            return BoolVal(True)
        elif len(all_constraints) == 1:
            return all_constraints[0]
        else:
            return And(*all_constraints)


class X86WorldState:
    """x86-64 全局世界状态。

    参考 evm_ir 的 WorldState，管理：
    - 约束条件
    - 注解
    """

    def __init__(self):
        """初始化世界状态。"""
        self.constraints: X86Constraints = X86Constraints()
        self.annotations: List[X86StateAnnotation] = []

    def __copy__(self):
        """浅拷贝（快速）。

        参考 mythril 的设计，拷贝注解列表以确保状态独立。
        虽然当前代码中不使用注解，但为未来扩展预留正确的行为。

        Returns:
            新的 X86WorldState 实例
        """
        import copy
        new_state = X86WorldState()
        new_state.constraints = copy.copy(self.constraints)
        # 拷贝注解列表（参考 mythril）
        new_state.annotations = [copy(a) for a in self.annotations]
        return new_state

    def __deepcopy__(self, memo):
        """深拷贝（慢但正确）。

        参考 mythril 的设计，注解仍使用 copy（Z3 表达式不可变）。
        主要区别是 constraints 使用 deepcopy。

        Returns:
            新的 X86WorldState 实例
        """
        import copy
        new_state = X86WorldState()
        new_state.constraints = copy.deepcopy(self.constraints, memo)
        # 注解使用 copy 而非 deepcopy（参考 mythril）
        new_state.annotations = [copy(a) for a in self.annotations]
        return new_state


class X86GlobalState:
    """x86-64 全局执行状态。

    参考 evm_ir 的 GlobalState 设计：
    - world_state: 全局世界状态
    - mstate: 机器状态（x86-64 状态）
    - node: 当前 CFG 节点
    """

    def __init__(self,
                 mstate: SMTState,
                 world_state: Optional[X86WorldState] = None,
                 node: Optional[X86CFGNode] = None):
        """初始化全局状态。

        Args:
            mstate: 机器状态（x86-64 状态）
            world_state: 世界状态（约束、注解等）
            node: 当前 CFG 节点
        """
        self.mstate = mstate
        self.world_state = world_state if world_state is not None else X86WorldState()
        self.node = node

        # 执行深度（用于循环检测）
        self.depth = 0

        # 该 state 进入的 block 原始末尾控制流（建边 + 终止判定）是否已被
        # 一个跨 block summary 接管。命中跨 block summary 时由 executor 置位，
        # 用于让外层 manage_cfg / 终止判定跳过这个已被 summary 折叠的 entry。
        self.summary_control_flow_managed = False

    def __copy__(self):
        """浅拷贝（快速，用于大多数情况）。

        Returns:
            新的 X86GlobalState 实例
        """
        import copy
        # 注意：SMTState 本身是不可变表达式，可以共享
        # WorldState 也使用浅拷贝
        new_state = X86GlobalState(
            mstate=self.mstate,  # SMTState 不可变，共享
            world_state=copy.copy(self.world_state),
            node=self.node
        )
        new_state.depth = self.depth
        new_state.summary_control_flow_managed = self.summary_control_flow_managed
        return new_state

    def __deepcopy__(self, memo):
        """深拷贝（慢，用于分支路径）。

        Returns:
            新的 X86GlobalState 实例
        """
        import copy
        new_state = X86GlobalState(
            mstate=self.mstate.copy(),  # 深拷贝 SMTState
            world_state=copy.deepcopy(self.world_state, memo),
            node=self.node
        )
        new_state.depth = self.depth
        new_state.summary_control_flow_managed = self.summary_control_flow_managed
        return new_state

    def get_constraints(self) -> X86Constraints:
        """获取约束条件。

        Returns:
            约束集合
        """
        return self.world_state.constraints

    def add_constraint(self, constraint: BoolRef) -> None:
        """添加约束。

        Args:
            constraint: 要添加的约束
        """
        self.world_state.constraints.add(constraint)

    def annotate(self, annotation: X86StateAnnotation) -> None:
        """添加注解。

        Args:
            annotation: 状态注解
        """
        self.world_state.annotations.append(annotation)

    def get_annotation(self, annotation_type: type) -> Optional[X86StateAnnotation]:
        """获取指定类型的注解。

        Args:
            annotation_type: 注解类型

        Returns:
            匹配的注解或 None
        """
        for ann in self.world_state.annotations:
            if isinstance(ann, annotation_type):
                return ann
        return None

    def __repr__(self):
        node_str = f"node=0x{self.node.address:x}" if self.node else "node=None"
        return f"X86GlobalState(depth={self.depth}, {node_str}, constraints={len(self.world_state.constraints)})"
