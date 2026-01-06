"""
状态注释系统（参考 mythril）。

定义 StateAnnotation 基类和具体注解类型。
"""


class StateAnnotation:
    """状态注释基类。

    用于附加元数据到状态，支持分析和合并策略。
    """

    @property
    def persist_across_calls(self) -> bool:
        """是否在调用边界持久化。"""
        return False

    def check_merge(self, other: 'StateAnnotation') -> bool:
        """检查是否可以与另一个注释合并。

        Args:
            other: 另一个 StateAnnotation

        Returns:
            如果可以合并则返回 True
        """
        return type(self) == type(other)

    def merge(self, other: 'StateAnnotation') -> 'StateAnnotation':
        """与另一个注释合并。

        Args:
            other: 另一个 StateAnnotation

        Returns:
            合并后的注释
        """
        # 默认实现：返回 self
        return self


class LoopCountAnnotation(StateAnnotation):
    """循环计数注释。

    跟踪对特定 JUMPDEST 的访问次数。
    """

    def __init__(self, loop_target_pc: int, count: int = 0):
        """初始化循环计数注释。

        Args:
            loop_target_pc: 循环目标块的 PC
            count: 当前迭代次数
        """
        self.loop_target_pc = loop_target_pc
        self.count = count

    def check_merge(self, other: StateAnnotation) -> bool:
        """只有相同循环目标才能合并。"""
        return isinstance(other, LoopCountAnnotation) and self.loop_target_pc == other.loop_target_pc

    def merge(self, other: StateAnnotation) -> StateAnnotation:
        """合并时取最大计数。"""
        if isinstance(other, LoopCountAnnotation):
            return LoopCountAnnotation(self.loop_target_pc, max(self.count, other.count))
        return self

    def __repr__(self):
        return f"LoopCount(pc={self.loop_target_pc}, count={self.count})"
