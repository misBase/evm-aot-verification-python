"""
x86-64 状态注解系统（参考 evm_ir）。

定义状态注解基类和具体注解实现。
"""

from typing import Any


class X86StateAnnotation:
    """x86-64 状态注解基类。

    参考 evm_ir 的 StateAnnotation，用于在执行过程中附加元数据。
    """

    @property
    def persist_across_calls(self) -> bool:
        """是否在函数调用中持久化。"""
        return False

    def check_merge(self, other: 'X86StateAnnotation') -> bool:
        """检查是否可以与另一个注解合并。

        Args:
            other: 另一个注解

        Returns:
            如果可以合并则返回 True
        """
        return type(self) == type(other)

    def merge(self, other: 'X86StateAnnotation') -> 'X86StateAnnotation':
        """与另一个注解合并。

        Args:
            other: 另一个注解

        Returns:
            合并后的注解
        """
        # 默认实现：返回 self
        return self


class LoopDetectionAnnotation(X86StateAnnotation):
    """循环检测注解。

    用于追踪循环目标的访问次数。
    参考 evm_ir 的 LoopCountAnnotation。

    Note:
        循环检测位置已在主逻辑中预留：
        - X86BoundedLoopsStrategy 中的 loop_visits 计数
        - X86DynamicCFG.detect_loop_headers() 方法
        具体的循环检测实现暂未完成。
    """

    def __init__(self, loop_target_addr: int, count: int = 0):
        """初始化循环检测注解。

        Args:
            loop_target_addr: 循环目标地址（循环头）
            count: 访问计数
        """
        self.loop_target_addr = loop_target_addr
        self.count = count

    def check_merge(self, other: X86StateAnnotation) -> bool:
        """只有相同循环目标才能合并。

        Args:
            other: 另一个注解

        Returns:
            如果可以合并则返回 True
        """
        return isinstance(other, LoopDetectionAnnotation) and \
               self.loop_target_addr == other.loop_target_addr

    def merge(self, other: X86StateAnnotation) -> X86StateAnnotation:
        """合并时取最大计数。

        Args:
            other: 另一个注解

        Returns:
            合并后的注解
        """
        if isinstance(other, LoopDetectionAnnotation):
            return LoopDetectionAnnotation(
                self.loop_target_addr,
                max(self.count, other.count)
            )
        return self

    def __repr__(self):
        return f"LoopDetectionAnnotation(addr=0x{self.loop_target_addr:x}, count={self.count})"
