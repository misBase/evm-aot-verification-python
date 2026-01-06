"""
全局状态管理（参考 mythril）。

定义 WorldState、Constraints 和 GlobalState 类。
"""

from __future__ import annotations

from typing import List, Optional, TYPE_CHECKING
from z3 import BoolRef, BoolVal, Solver, sat

from state.smt_state import SMTState

# 用于类型注解的前向引用
if TYPE_CHECKING:
    from .cfg_structures import CFGNode


class WorldState:
    """全局世界状态。

    参考 mythril 的 WorldState，管理：
    - 约束条件
    - 事务序列
    - 注解
    """

    def __init__(self):
        """初始化世界状态。"""
        from z3 import BoolVal
        self.constraints: Constraints = Constraints()
        self.transaction_sequence: List = []
        self.annotations: List['StateAnnotation'] = []

    def __copy__(self):
        """浅拷贝（快速）。

        Returns:
            新的 WorldState 实例
        """
        new_state = WorldState()
        new_state.constraints = self.constraints
        # transaction_sequence 引用共享
        new_state.transaction_sequence = self.transaction_sequence
        # 注解引用共享
        new_state.annotations = self.annotations
        return new_state

    def __deepcopy__(self, memo):
        """深拷贝（慢但正确）。

        Returns:
            新的 WorldState 实例
        """
        import copy
        new_state = WorldState()
        new_state.constraints = copy.deepcopy(self.constraints, memo)
        new_state.transaction_sequence = self.transaction_sequence.copy()
        new_state.annotations = copy.deepcopy(self.annotations, memo)
        return new_state


class Constraints:
    """约束条件集合。

    参考 mythril 的 Constraints 类。
    """

    def __init__(self):
        """初始化约束集合。"""
        from z3 import BoolVal
        self._constraints: List[BoolRef] = [BoolVal(True)]

    def add(self, constraint: BoolRef) -> None:
        """添加约束。

        Args:
            constraint: 要添加的布尔约束
        """
        self._constraints.append(constraint)

    def __copy__(self):
        """浅拷贝约束。

        Returns:
            新的 Constraints 实例，共享约束列表
        """
        new_constraints = Constraints()
        new_constraints._constraints = self._constraints
        return new_constraints

    def __deepcopy__(self, memo):
        """深拷贝约束。

        Returns:
            新的 Constraints 实例，复制约束列表
        """
        import copy
        new_constraints = Constraints()
        new_constraints._constraints = copy.deepcopy(self._constraints, memo)
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

        if solver_timeout is not None:
            solver.set(timeout=solver_timeout)

        result = solver.check()
        return result == sat

    def as_bool(self) -> BoolRef:
        """将约束集合转换为单个 BoolRef（合取）。

        Returns:
            所有约束的合取
        """
        from z3 import And
        if len(self._constraints) == 0:
            return BoolVal(True)
        elif len(self._constraints) == 1:
            return self._constraints[0]
        else:
            return And(*self._constraints)


class GlobalState:
    """全局执行状态。

    参考 mythril 的 GlobalState 设计：
    - world_state: 全局世界状态
    - mstate: 机器状态（EVM 状态）
    - environment: 环境信息
    - node: 当前 CFG 节点
    """

    def __init__(self,
                 mstate: SMTState,
                 world_state: Optional[WorldState] = None,
                 node: Optional[CFGNode] = None):
        """初始化全局状态。

        Args:
            mstate: 机器状态（EVM 状态）
            world_state: 世界状态（约束、注解等）
            node: 当前 CFG 节点
        """
        self.mstate = mstate
        self.world_state = world_state if world_state is not None else WorldState()
        self.node = node

        # 执行深度（用于循环检测）
        self.depth = 0

    def __copy__(self):
        """浅拷贝（快速，用于大多数情况）。

        Returns:
            新的 GlobalState 实例
        """
        import copy
        # 注意：SMTState 本身是不可变表达式，可以共享
        # WorldState 也使用浅拷贝
        new_state = GlobalState(
            mstate=self.mstate,  # SMTState 不可变，共享
            world_state=copy(self.world_state),
            node=self.node
        )
        new_state.depth = self.depth
        return new_state

    def __deepcopy__(self, memo):
        """深拷贝（慢，用于分支路径）。

        Returns:
            新的 GlobalState 实例
        """
        import copy
        new_state = GlobalState(
            mstate=self.mstate.copy(),  # 深拷贝 SMTState
            world_state=copy.deepcopy(self.world_state, memo),
            node=self.node
        )
        new_state.depth = self.depth
        return new_state

    def get_constraints(self) -> Constraints:
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

    def annotate(self, annotation: 'StateAnnotation') -> None:
        """添加注解。

        Args:
            annotation: 状态注解
        """
        self.world_state.annotations.append(annotation)

    def get_annotation(self, annotation_type: type) -> Optional['StateAnnotation']:
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
