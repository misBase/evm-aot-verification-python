"""
EVM Gas 状态建模。
"""

from typing import Optional
from z3 import BitVec, BitVecVal, BoolRef


class EVMGasState:
    """EVM Gas状态表示。

    跟踪Gas消耗：Gas : BitVec[64]
    支持静态Gas和动态Gas计算。
    """

    def __init__(self, initial_gas: Optional[BitVec] = None):
        """初始化EVM Gas状态。

        Args:
            initial_gas: 可选的初始Gas值
        """
        # Gas : BitVec[64]
        if initial_gas is None:
            self.Gas = BitVec('Gas', 64)
        else:
            self.Gas = initial_gas

    def consume_static(self, amount: int) -> 'EVMGasState':
        """消耗静态Gas。

        Args:
            amount: 要消耗的Gas数量

        Returns:
            具有更新Gas的新EVMGasState
        """
        from z3 import BitVecVal, If, UGT
        amount_bv = BitVecVal(amount, 64)

        # 检查Gas溢出：如果Gas < amount，设为0（out of gas）
        new_gas = If(UGT(amount_bv, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - amount_bv)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

    def consume_dynamic(self, cost: BitVec) -> 'EVMGasState':
        """消耗动态Gas。

        Args:
            cost: 动态Gas成本（符号表达式）

        Returns:
            具有更新Gas的新EVMGasState
        """
        from z3 import If, UGT

        # 检查Gas溢出：如果Gas < cost，设为0（out of gas）
        new_gas = If(UGT(cost, self.Gas),
                     BitVecVal(0, 64),
                     self.Gas - cost)

        new_state = EVMGasState(initial_gas=new_gas)
        return new_state

    def is_out_of_gas(self) -> BoolRef:
        """检查是否耗尽Gas。

        Returns:
            BoolRef：如果Gas == 0则为True
        """
        from z3 import BitVecVal
        return self.Gas == BitVecVal(0, 64)

    def copy(self) -> 'EVMGasState':
        """创建Gas状态的副本。

        Returns:
            具有相同Gas的新EVMGasState实例
        """
        new_state = EVMGasState(initial_gas=self.Gas)
        return new_state
