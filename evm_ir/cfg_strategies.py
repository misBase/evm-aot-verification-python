"""
搜索策略（参考 mythril）。

定义 SearchStrategy 抽象基类和具体策略实现。
"""

from typing import List, Optional, Dict, Iterator
from abc import ABC, abstractmethod

from .cfg_state import GlobalState


class SearchStrategy(ABC):
    """搜索策略抽象基类。

    参考 mythril 的 BasicSearchStrategy。
    """

    def __init__(self, work_list: List[GlobalState], max_depth: int = 100):
        """初始化搜索策略。

        Args:
            work_list: 工作列表（由外部维护）
            max_depth: 最大执行深度
        """
        self.work_list = work_list
        self.max_depth = max_depth

    @abstractmethod
    def get_strategic_global_state(self) -> Optional[GlobalState]:
        """获取下一个要执行的状态。

        由子类实现具体的策略。

        Returns:
            GlobalState 或 None
        """
        raise NotImplementedError("Subclasses must implement get_strategic_global_state()")

    def __iter__(self) -> Iterator[GlobalState]:
        """迭代器接口。

        Returns:
            自身
        """
        return self

    def __next__(self) -> GlobalState:
        """获取下一个状态（迭代器协议）。

        Returns:
            下一个 GlobalState

        Raises:
            StopIteration: 如果没有更多状态
        """
        try:
            global_state = self.get_strategic_global_state()
            if global_state is None:
                raise StopIteration

            # 检查深度限制
            if global_state.depth >= self.max_depth:
                return self.__next__()  # 跳过超深度状态

            return global_state
        except (IndexError, StopIteration):
            raise StopIteration


class DFSStrategy(SearchStrategy):
    """深度优先搜索策略。

    参考 mythril 的 DepthFirstSearchStrategy。
    使用 LIFO 顺序（栈）。
    """

    def get_strategic_global_state(self) -> Optional[GlobalState]:
        """获取最后一个添加的状态（LIFO）。

        Returns:
            GlobalState 或 None
        """
        if not self.work_list:
            return None
        return self.work_list.pop()


class BFSStrategy(SearchStrategy):
    """广度优先搜索策略。

    参考 mythril 的 BreadthFirstSearchStrategy。
    使用 FIFO 顺序（队列）。
    """

    def get_strategic_global_state(self) -> Optional[GlobalState]:
        """获取第一个添加的状态（FIFO）。

        Returns:
            GlobalState 或 None
        """
        if not self.work_list:
            return None
        return self.work_list.pop(0)


class ExtensionStrategy(SearchStrategy):
    """策略包装器，用于扩展基础策略。

    参考 mythril 的策略扩展机制。
    """

    def __init__(self, super_strategy: SearchStrategy, work_list: List[GlobalState], max_depth: int = 100):
        """初始化扩展策略。

        Args:
            super_strategy: 基础策略
            work_list: 工作列表
            max_depth: 最大深度
        """
        super().__init__(work_list, max_depth)
        self.super_strategy = super_strategy

    def get_strategic_global_state(self) -> Optional[GlobalState]:
        """委托给基础策略。

        Returns:
            GlobalState 或 None
        """
        return self.super_strategy.get_strategic_global_state()


class BoundedLoopsStrategy(ExtensionStrategy):
    """有界循环策略。

    参考 mythril 的 BoundedLoopsStrategy。
    限制循环迭代次数。
    """

    def __init__(self, super_strategy: SearchStrategy, work_list: List[GlobalState],
                 max_depth: int = 100, loop_bound: int = 3):
        """初始化有界循环策略。

        Args:
            super_strategy: 基础策略
            work_list: 工作列表
            max_depth: 最大深度
            loop_bound: 循环边界（最大迭代次数）
        """
        super().__init__(super_strategy, work_list, max_depth)
        self.loop_bound = loop_bound
        # 跟踪每个 JUMPDEST 的访问次数
        self.loop_visits: Dict[int, int] = {}

    def get_strategic_global_state(self) -> Optional[GlobalState]:
        """获取下一个未超过循环边界的状态。

        Returns:
            GlobalState 或 None
        """
        while True:
            state = self.super_strategy.get_strategic_global_state()
            if state is None:
                return None

            # 检查当前 PC 是否是循环目标
            current_pc = state.node.pc if state.node else None

            if current_pc is not None:
                # 检查循环计数
                count = self.loop_visits.get(current_pc, 0)
                if count >= self.loop_bound:
                    # 超过边界，跳过这个状态
                    continue

                # 增加计数
                self.loop_visits[current_pc] = count + 1

            return state
