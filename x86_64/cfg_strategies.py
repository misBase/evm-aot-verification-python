"""
x86-64 搜索策略（参考 evm_ir）。

定义 SearchStrategy 抽象基类和具体策略实现。
"""

from typing import List, Optional, Dict, Iterator
from abc import ABC, abstractmethod

from .cfg_state import X86GlobalState


class X86SearchStrategy(ABC):
    """x86-64 搜索策略抽象基类。

    参考 evm_ir 的 BasicSearchStrategy。
    """

    def __init__(self, work_list: List[X86GlobalState], max_depth: int = 100):
        """初始化搜索策略。

        Args:
            work_list: 工作列表（由外部维护）
            max_depth: 最大执行深度
        """
        self.work_list = work_list
        self.max_depth = max_depth

    @abstractmethod
    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """获取下一个要执行的状态。

        由子类实现具体的策略。

        Returns:
            X86GlobalState 或 None
        """
        raise NotImplementedError("Subclasses must implement get_strategic_global_state()")

    def __iter__(self) -> Iterator[X86GlobalState]:
        """迭代器接口。

        Returns:
            自身
        """
        return self

    def __next__(self) -> X86GlobalState:
        """获取下一个状态（迭代器协议）。

        Returns:
            下一个 X86GlobalState

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


class X86DFSStrategy(X86SearchStrategy):
    """深度优先搜索策略。

    参考 evm_ir 的 DepthFirstSearchStrategy。
    使用 LIFO 顺序（栈）。
    """

    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """获取最后一个添加的状态（LIFO）。

        Returns:
            X86GlobalState 或 None
        """
        if not self.work_list:
            return None
        return self.work_list.pop()


class X86BFSStrategy(X86SearchStrategy):
    """广度优先搜索策略。

    参考 evm_ir 的 BreadthFirstSearchStrategy。
    使用 FIFO 顺序（队列）。
    """

    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """获取第一个添加的状态（FIFO）。

        Returns:
            X86GlobalState 或 None
        """
        if not self.work_list:
            return None
        return self.work_list.pop(0)


class X86ExtensionStrategy(X86SearchStrategy):
    """策略包装器，用于扩展基础策略。

    参考 evm_ir 的策略扩展机制。
    """

    def __init__(self, super_strategy: X86SearchStrategy, work_list: List[X86GlobalState], max_depth: int = 100):
        """初始化扩展策略。

        Args:
            super_strategy: 基础策略
            work_list: 工作列表
            max_depth: 最大深度
        """
        super().__init__(work_list, max_depth)
        self.super_strategy = super_strategy

    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """委托给基础策略。

        Returns:
            X86GlobalState 或 None
        """
        return self.super_strategy.get_strategic_global_state()


class X86TopologicalStrategy(X86SearchStrategy):
    """拓扑排序策略。

    按拓扑序处理 work_list，保证处理某个 block 时其所有前驱都已处理完毕。
    适用于无循环的 DAG 型 CFG，配合合流点合并优化使用。
    """

    def __init__(self, work_list: List[X86GlobalState], max_depth: int = 100,
                 topo_order: Optional[Dict[int, int]] = None):
        """初始化拓扑排序策略。

        Args:
            work_list: 工作列表
            max_depth: 最大深度
            topo_order: addr → 拓扑序号映射
        """
        super().__init__(work_list, max_depth)
        self.topo_order = topo_order or {}

    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """选择拓扑序最小的状态优先处理。

        Returns:
            X86GlobalState 或 None
        """
        if not self.work_list:
            return None
        # 找到拓扑序最小的状态
        best_idx = 0
        best_order = self.topo_order.get(
            self.work_list[0].node.address if self.work_list[0].node else 0,
            float('inf')
        )
        for i in range(1, len(self.work_list)):
            addr = self.work_list[i].node.address if self.work_list[i].node else 0
            order = self.topo_order.get(addr, float('inf'))
            if order < best_order:
                best_order = order
                best_idx = i
        return self.work_list.pop(best_idx)


class X86BoundedLoopsStrategy(X86ExtensionStrategy):
    """有界循环策略。

    参考 evm_ir 的 BoundedLoopsStrategy。
    限制循环迭代次数。

    Note:
        循环检测的实现需要与 CFG 配合。
        当前使用简化实现：对所有地址的访问次数进行限制。
        完整实现应该只对循环头（有回边的节点）进行计数。
    """

    def __init__(self, super_strategy: X86SearchStrategy, work_list: List[X86GlobalState],
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
        # 跟踪每个地址的访问次数
        # TODO: 完整实现应该只对循环头（有回边的节点）计数
        # 这需要先执行 CFG 分析来确定哪些节点是循环头
        self.loop_visits: Dict[int, int] = {}

    def get_strategic_global_state(self) -> Optional[X86GlobalState]:
        """获取下一个未超过循环边界的状态。

        简化实现：对所有地址的访问进行计数和限制。

        完整实现应该：
        1. 使用 CFG.detect_loop_headers() 识别循环头
        2. 只对循环头的访问进行计数
        3. 非循环头节点不受限制

        Returns:
            X86GlobalState 或 None
        """
        while True:
            state = self.super_strategy.get_strategic_global_state()
            if state is None:
                return None

            # 检查当前地址是否是循环目标
            current_addr = state.node.address if state.node else None

            if current_addr is not None:
                # 检查循环计数
                count = self.loop_visits.get(current_addr, 0)
                if count >= self.loop_bound:
                    # 超过边界，跳过这个状态
                    continue

                # 增加计数
                self.loop_visits[current_addr] = count + 1

            return state
