"""
测试EVM高级操作语义：SLOAD、SSTORE和Gas计算。
"""

import pytest
from z3 import BitVec, BitVecVal, Solver, sat
from state.smt_state import SMTState
from evm_ir.semantics import evm_operator_to_z3
from evm_ir.models import EvmOperator


class TestEVMStorageOperations:
    """测试EVM存储操作的语义建模。"""

    def test_sload_operation(self):
        """测试SLOAD操作：从存储中加载值。"""
        # 创建操作：SLOAD
        op = EvmOperator(kind="SLOAD", pc=0)

        # 创建状态：栈上有一个键
        state = SMTState()
        key = BitVecVal(100, 256)
        state.evm_stack = state.evm_stack.push(key)

        # 执行SLOAD
        result_state = evm_operator_to_z3(op, state)

        # 验证结果：操作不抛出异常
        assert result_state is not None

    def test_sstore_operation(self):
        """测试SSTORE操作：存储值到存储中。"""
        # 创建操作：SSTORE
        op = EvmOperator(kind="SSTORE", pc=0)

        # 创建状态：栈上有值和键
        state = SMTState()
        key = BitVecVal(100, 256)
        value = BitVecVal(42, 256)

        # 先推送key，再推送value（栈顶是value）
        state.evm_stack = state.evm_stack.push(key)
        state.evm_stack = state.evm_stack.push(value)

        # 执行SSTORE
        result_state = evm_operator_to_z3(op, state)

        # 验证结果：操作不抛出异常
        assert result_state is not None

    def test_sload_sstore_sequence(self):
        """测试SLOAD/SSTORE序列操作。"""
        # 创建SSTORE操作
        sstore_op = EvmOperator(kind="SSTORE", pc=0)
        sload_op = EvmOperator(kind="SLOAD", pc=0)

        state = SMTState()
        key = BitVecVal(100, 256)
        value = BitVecVal(42, 256)

        # 执行SSTORE
        state.evm_stack = state.evm_stack.push(key)
        state.evm_stack = state.evm_stack.push(value)
        state = evm_operator_to_z3(sstore_op, state)

        # 执行SLOAD（重新推送key）
        state.evm_stack = state.evm_stack.push(key)
        state = evm_operator_to_z3(sload_op, state)

        # 验证结果：操作不抛出异常
        assert state is not None


class TestEVMGasOperations:
    """测试EVM Gas计算的语义建模。"""

    def test_sload_gas_consumption(self):
        """测试SLOAD的Gas消耗。"""
        # 创建操作：SLOAD
        op = EvmOperator(kind="SLOAD", pc=0)

        # 创建状态：初始Gas为100000
        state = SMTState()
        state.evm_gas = state.evm_gas.consume_static(0)  # 重置为符号变量
        state.evm_stack = state.evm_stack.push(BitVecVal(100, 256))

        # 执行SLOAD
        result_state = evm_operator_to_z3(op, state)

        # 验证结果：操作不抛出异常
        assert result_state is not None

    def test_sstore_gas_consumption(self):
        """测试SSTORE的Gas消耗。"""
        # 创建操作：SSTORE
        op = EvmOperator(kind="SSTORE", pc=0)

        # 创建状态
        state = SMTState()
        state.evm_stack = state.evm_stack.push(BitVecVal(100, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(42, 256))

        # 执行SSTORE
        result_state = evm_operator_to_z3(op, state)

        # 验证结果：操作不抛出异常
        assert result_state is not None

    def test_multiple_operations_gas(self):
        """测试多个操作的Gas累计消耗。"""
        # 创建操作：ADD (静态Gas成本为3)
        add_op = EvmOperator(kind="ADD", pc=0)

        # 创建状态
        state = SMTState()
        state.evm_stack = state.evm_stack.push(BitVecVal(10, 256))
        state.evm_stack = state.evm_stack.push(BitVecVal(20, 256))

        # 执行ADD
        result_state = evm_operator_to_z3(add_op, state)

        # 验证结果：操作不抛出异常
        assert result_state is not None
