"""
EVM 栈状态建模。
"""

from typing import Optional
from z3 import BitVec, BitVecVal, Array, ArraySort, BitVecSort, IntSort, Int, Select, Store


class EVMStackState:
    """EVM栈状态表示。

    使用Z3 Array对EVM栈建模：Stack : Array[Int, BitVec[256]]
    栈指针SP : Int（范围0-1024）
    栈顶元素：Stack[SP-1]
    """

    def __init__(self, stack_array: Optional[Array] = None, sp: Optional[Int] = None):
        """初始化EVM栈状态。

        Args:
            stack_array: 可选的现有Stack数组
            sp: 可选的现有SP指针
        """
        # Stack : Array[Int, BitVec[256]]
        if stack_array is None:
            self.Stack = Array('Stack', IntSort(), BitVecSort(256))
        else:
            self.Stack = stack_array

        # SP : Int（栈指针，范围0-1024）
        if sp is None:
            self.SP = Int('SP')
        else:
            self.SP = sp

    def dup(self, n: int) -> 'EVMStackState':
        """DUP操作：复制栈上的第n个元素到栈顶。

        DUP1复制栈顶元素，DUP2复制次栈顶元素，以此类推。

        Args:
            n: DUP编号（1-16），DUP1复制Stack[SP-1]，DUP2复制Stack[SP-2]

        Returns:
            具有更新Stack和SP的新EVMStackState
        """
        if not 1 <= n <= 16:
            raise ValueError(f"DUP number must be 1-16, got {n}")

        # 获取要复制的值：Stack[SP-n]
        value = Select(self.Stack, self.SP - n)

        # 推送到栈顶：SP' = SP + 1, Stack' = Store(Stack, SP, value)
        new_sp = self.SP + 1
        new_stack = Store(self.Stack, self.SP, value)

        new_state = EVMStackState(stack_array=new_stack, sp=new_sp)
        return new_state

    def swap(self, n: int) -> 'EVMStackState':
        """SWAP操作：交换栈顶元素和第n个元素。

        SWAP1交换Stack[SP-1]和Stack[SP-2]，SWAP2交换Stack[SP-1]和Stack[SP-3]，以此类推。

        Args:
            n: SWAP编号（1-16），SWAP1交换栈顶和次栈顶

        Returns:
            具有更新Stack的新EVMStackState（SP不变）
        """
        if not 1 <= n <= 16:
            raise ValueError(f"SWAP number must be 1-16, got {n}")

        # 获取栈顶元素：Stack[SP-1]
        top_value = Select(self.Stack, self.SP - 1)

        # 获取要交换的元素：Stack[SP-1-n]
        other_value = Select(self.Stack, self.SP - 1 - n)

        # 存储到交换位置：Stack[SP-1-n] = top_value
        new_stack = Store(self.Stack, self.SP - 1 - n, top_value)

        # 存储栈顶：Stack[SP-1] = other_value
        new_stack = Store(new_stack, self.SP - 1, other_value)

        new_state = EVMStackState(stack_array=new_stack, sp=self.SP)
        return new_state

    def push(self, value: BitVec) -> 'EVMStackState':
        """将值推送到栈上。

        PUSH操作：SP' = SP + 1, Stack' = Store(Stack, SP, value)

        Args:
            value: 要推送的256位BitVec值

        Returns:
            具有更新Stack和SP的新EVMStackState
        """
        if value.size() != 256:
            raise ValueError(f"Stack value must be 256 bits, got {value.size()}")

        # SP' = SP + 1
        new_sp = self.SP + 1
        # Stack' = Store(Stack, SP, value)
        new_stack = Store(self.Stack, self.SP, value)

        # 创建新状态
        new_state = EVMStackState(stack_array=new_stack, sp=new_sp)
        return new_state

    def pop(self) -> tuple[BitVec, 'EVMStackState']:
        """从栈中弹出一个值。

        POP操作：value = Select(Stack, SP-1), SP' = SP - 1

        Returns:
            (popped_value, new_state)元组
        """
        # value = Select(Stack, SP-1)
        value = Select(self.Stack, self.SP - 1)
        # SP' = SP - 1
        new_sp = self.SP - 1
        # Stack保持不变（我们不修改它，只更改SP）

        new_state = EVMStackState(stack_array=self.Stack, sp=new_sp)
        return value, new_state

    def peek(self, index: int = 0) -> BitVec:
        """查看栈值而不弹出。

        Args:
            index: 栈索引（0 = 栈顶，1 = 次栈顶，等等）

        Returns:
            索引处的256位BitVec值
        """
        # 栈索引0在SP-1，索引1在SP-2，等等
        stack_index = self.SP - 1 - index
        return Select(self.Stack, stack_index)

    @property
    def top(self) -> BitVec:
        """获取栈的顶部元素（Stack[SP-1]）。

        Returns:
            栈顶的256位BitVec值
        """
        return Select(self.Stack, self.SP - 1)

    def back(self, n: int) -> BitVec:
        """获取栈中back(n)位置的值。

        back(0)是栈顶（Stack[SP-1]）
        back(1)是次栈顶（Stack[SP-2]）
        等等

        Args:
            n: 栈索引（0 = 栈顶，1 = 次栈顶，等等）

        Returns:
            back(n)位置的256位BitVec值
        """
        # back(n) = Stack[SP-1-n]
        stack_index = self.SP - 1 - n
        return Select(self.Stack, stack_index)

    def copy(self) -> 'EVMStackState':
        """创建栈状态的副本。

        Returns:
            具有相同Stack和SP的新EVMStackState实例
        """
        # 注意：在Z3中，数组和整数是不可变表达式，
        # 所以我们可以直接重用它们
        new_state = EVMStackState(stack_array=self.Stack, sp=self.SP)
        return new_state
