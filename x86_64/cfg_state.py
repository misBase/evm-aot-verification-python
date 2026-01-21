"""
x86-64 全局状态管理（参考 evm_ir）。

定义 X86WorldState、X86Constraints 和 X86GlobalState 类。
"""

from __future__ import annotations

from typing import List, Optional, Dict, TYPE_CHECKING
from z3 import BoolRef, BoolVal, Solver, sat, And

from state.smt_state import SMTState

# 用于类型注解的前向引用
if TYPE_CHECKING:
    from .cfg_structures import X86CFGNode
    from .cfg_annotations import X86StateAnnotation


class X86Constraints:
    """x86-64 约束条件集合。

    参考 evm_ir 的 Constraints 类，扩展支持 CPU 标志约束。
    """

    def __init__(self):
        """初始化约束集合。"""
        self._constraints: List[BoolRef] = [BoolVal(True)]
        self.flag_constraints: Dict[str, BoolRef] = {}  # CPU 标志: CF, ZF, SF, OF

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
        return new_constraints

    def __iter__(self):
        """迭代约束。"""
        return iter(self._constraints)

    def __len__(self):
        """约束数量。"""
        return len(self._constraints)

    def is_possible(self, solver_timeout: Optional[int] = None) -> bool:
        """检查约束是否可满足（可达性检查）。

        Args:
            solver_timeout: 求解器超时时间（毫秒）

        Returns:
            如果约束可满足则返回 True
        """
        solver = Solver()
        for constraint in self._constraints:
            solver.add(constraint)
        for flag_cond in self.flag_constraints.values():
            solver.add(flag_cond)

        if solver_timeout is not None:
            solver.set(timeout=solver_timeout)

        result = solver.check()
        return result == sat

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

        Returns:
            新的 X86WorldState 实例
        """
        import copy
        new_state = X86WorldState()
        new_state.constraints = copy.copy(self.constraints)
        # 注解引用共享
        new_state.annotations = self.annotations
        return new_state

    def __deepcopy__(self, memo):
        """深拷贝（慢但正确）。

        Returns:
            新的 X86WorldState 实例
        """
        import copy
        new_state = X86WorldState()
        new_state.constraints = copy.deepcopy(self.constraints, memo)
        new_state.annotations = copy.deepcopy(self.annotations, memo)
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
            world_state=copy(self.world_state),
            node=self.node
        )
        new_state.depth = self.depth
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
