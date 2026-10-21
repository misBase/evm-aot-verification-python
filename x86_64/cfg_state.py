"""
x86-64 全局状态管理（参考 evm_ir）。

定义 X86WorldState、X86Constraints 和 X86GlobalState 类。
"""

from __future__ import annotations

import os
import time
from typing import List, Optional, Dict, TYPE_CHECKING
from z3 import BoolRef, BoolVal, Solver, SolverFor, unsat, sat, unknown, is_true, And, simplify

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


def _bounded_check(solver, timeout_ms, tag, wall_ms=None):
    """solver.check() under the reachability budget; any non-UNSAT keeps the path.

    `wall_ms` replaces the wall-clock safety net (timeout_ms x the factor) for
    callers whose budget is a wall-clock budget against a deadline."""
    if timeout_ms is not None and timeout_ms > 0:
        cap = 2**32 - 1  # both are unsigned-int Z3 params
        wall = timeout_ms * REACHABILITY_WALL_SAFETY_FACTOR if wall_ms is None else max(wall_ms, 1)
        solver.set("rlimit", min(timeout_ms * REACHABILITY_RLIMIT_PER_MS, cap))
        solver.set("timeout", min(wall, cap))
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

    def reset(self):
        self.solver.reset()
        self.stack = []

    def check(self, conjuncts, timeout_ms, tag="incremental", wall_ms=None):
        if self.solver.num_scopes() != len(self.stack):
            self.reset()
        common = 0
        for old, new in zip(self.stack, conjuncts):
            if old.get_id() != new.get_id():
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
        return _bounded_check(self.solver, timeout_ms, tag, wall_ms)


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
        """
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
            path = self.as_bool()
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
            relaxed, changed = abstract_nonlinear_mul(path)
            if changed:
                probe = SolverFor("QF_AUFBV")
                probe.add(relaxed)
                return _bounded_check(probe, timeout_ms, "probe") != unsat
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
            probe.add(relaxed)
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
