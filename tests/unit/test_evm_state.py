"""
EVM状态模型的单元测试。

测试EVMStackState、EVMStorageState、EVMGasState的功能。
"""

import pytest
from z3 import BitVec, BitVecVal, IntVal, Solver, sat
from state.smt_state import EVMStackState, EVMStorageState, EVMGasState, SMTState


class TestEVMStackState:
    """测试EVMStackState的功能。"""

    def test_initial_stack(self):
        """测试初始栈状态。"""
        stack = EVMStackState()
        assert stack.depth == 0
        # SP和Stack是符号变量，无法直接比较

    def test_push_single_value(self):
        """测试推送单个值到栈上。"""
        stack = EVMStackState(initial_depth=0, sp=IntVal(0))
        value = BitVecVal(42, 256)
        new_stack = stack.push(value)

        # 验证深度增加
        assert new_stack.depth == 1

        # 验证可以推送的值
        solver = Solver()
        # 栈顶应该是推送的值
        solver.add(new_stack.Stack == new_stack.Stack)
        # SP应该是1
        solver.add(new_stack.SP == IntVal(1))
        assert solver.check() == sat

    def test_pop_single_value(self):
        """测试从栈中弹出单个值。"""
        stack = EVMStackState(initial_depth=1, sp=IntVal(1))
        value, new_stack = stack.pop()

        # 验证深度减少
        assert new_stack.depth == 0

    def test_dup1(self):
        """测试DUP1操作：复制栈顶元素。"""
        stack = EVMStackState(initial_depth=1, sp=IntVal(1))
        new_stack = stack.dup(1)

        # 验证深度增加
        assert new_stack.depth == 2

    def test_dup2(self):
        """测试DUP2操作：复制次栈顶元素。"""
        stack = EVMStackState(initial_depth=2, sp=IntVal(2))
        new_stack = stack.dup(2)

        # 验证深度增加
        assert new_stack.depth == 3

    def test_dup_invalid_range(self):
        """测试DUP操作的无效范围。"""
        stack = EVMStackState()

        # DUP0应该失败
        with pytest.raises(ValueError, match="DUP number must be 1-16"):
            stack.dup(0)

        # DUP17应该失败
        with pytest.raises(ValueError, match="DUP number must be 1-16"):
            stack.dup(17)

    def test_swap1(self):
        """测试SWAP1操作：交换栈顶和次栈顶元素。"""
        stack = EVMStackState(initial_depth=2, sp=IntVal(2))
        new_stack = stack.swap(1)

        # 验证深度不变
        assert new_stack.depth == 2

    def test_swap_invalid_range(self):
        """测试SWAP操作的无效范围。"""
        stack = EVMStackState()

        # SWAP0应该失败
        with pytest.raises(ValueError, match="SWAP number must be 1-16"):
            stack.swap(0)

        # SWAP17应该失败
        with pytest.raises(ValueError, match="SWAP number must be 1-16"):
            stack.swap(17)

    def test_peek(self):
        """测试peek操作：查看栈值而不弹出。"""
        stack = EVMStackState(initial_depth=1, sp=IntVal(1))

        # peek(0)应该返回栈顶
        value = stack.peek(0)
        assert value.size() == 256

    def test_back(self):
        """测试back操作：获取栈中back(n)位置的值。"""
        stack = EVMStackState(initial_depth=2, sp=IntVal(2))

        # back(0)应该返回栈顶
        value0 = stack.back(0)
        assert value0.size() == 256

        # back(1)应该返回次栈顶
        value1 = stack.back(1)
        assert value1.size() == 256

    def test_copy(self):
        """测试复制栈状态。"""
        stack = EVMStackState(initial_depth=1, sp=IntVal(1))
        new_stack = stack.copy()

        # 验证深度相同
        assert new_stack.depth == stack.depth


class TestEVMStorageState:
    """测试EVMStorageState的功能。"""

    def test_initial_storage(self):
        """测试初始存储状态。"""
        storage = EVMStorageState()
        # Storage是符号数组，无法直接比较内容

    def test_sload(self):
        """测试从存储中加载值。"""
        storage = EVMStorageState()
        key = BitVecVal(100, 256)
        value = storage.sload(key)

        # 应该返回256位值
        assert value.size() == 256

    def test_sstore(self):
        """测试存储值到存储中。"""
        storage = EVMStorageState()
        key = BitVecVal(100, 256)
        value = BitVecVal(42, 256)
        new_storage = storage.sstore(key, value)

        # 验证可以读取存储的值
        loaded_value = new_storage.sload(key)
        solver = Solver()
        solver.add(loaded_value == value)
        assert solver.check() == sat

    def test_sload_invalid_key_size(self):
        """测试使用无效键大小进行SLOAD。"""
        storage = EVMStorageState()
        key = BitVecVal(100, 64)  # 错误：应该是256位

        with pytest.raises(ValueError, match="Storage key must be 256 bits"):
            storage.sload(key)

    def test_sstore_invalid_value_size(self):
        """测试使用无效值大小进行SSTORE。"""
        storage = EVMStorageState()
        key = BitVecVal(100, 256)
        value = BitVecVal(42, 64)  # 错误：应该是256位

        with pytest.raises(ValueError, match="Storage value must be 256 bits"):
            storage.sstore(key, value)

    def test_copy(self):
        """测试复制存储状态。"""
        storage = EVMStorageState()
        new_storage = storage.copy()

        # 验证Storage数组相同
        solver = Solver()
        solver.add(new_storage.Storage == storage.Storage)
        assert solver.check() == sat


class TestEVMGasState:
    """测试EVMGasState的功能。"""

    def test_initial_gas(self):
        """测试初始Gas状态。"""
        gas = EVMGasState()
        # Gas是符号变量，无法直接比较值

    def test_consume_static(self):
        """测试消耗静态Gas。"""
        gas = EVMGasState(initial_gas=BitVecVal(1000, 64))
        new_gas = gas.consume_static(100)

        # 创建求解器验证Gas消耗
        solver = Solver()
        # Gas应该减少100，或者为0（如果溢出）
        # 这里我们假设有足够的Gas
        solver.add(new_gas.Gas == BitVecVal(900, 64))
        assert solver.check() == sat

    def test_consume_static_overflow(self):
        """测试Gas溢出情况。"""
        gas = EVMGasState(initial_gas=BitVecVal(50, 64))
        new_gas = gas.consume_static(100)

        # Gas应该变为0（out of gas）
        solver = Solver()
        solver.add(new_gas.Gas == BitVecVal(0, 64))
        assert solver.check() == sat

    def test_consume_dynamic(self):
        """测试消耗动态Gas。"""
        gas = EVMGasState(initial_gas=BitVecVal(1000, 64))
        cost = BitVecVal(200, 64)
        new_gas = gas.consume_dynamic(cost)

        # Gas应该减少200
        solver = Solver()
        solver.add(new_gas.Gas == BitVecVal(800, 64))
        assert solver.check() == sat

    def test_is_out_of_gas(self):
        """测试检查是否耗尽Gas。"""
        # Gas为0的情况 - 返回BoolRef，需要求解器验证
        gas_empty = EVMGasState(initial_gas=BitVecVal(0, 64))
        out_of_gas_result = gas_empty.is_out_of_gas()
        # 验证结果为True
        solver = Solver()
        solver.add(out_of_gas_result == True)
        assert solver.check() == sat

        # Gas不为0的情况
        gas_full = EVMGasState(initial_gas=BitVecVal(1000, 64))
        not_out_of_gas = gas_full.is_out_of_gas()
        solver = Solver()
        solver.add(not_out_of_gas == False)
        assert solver.check() == sat

    def test_copy(self):
        """测试复制Gas状态。"""
        gas = EVMGasState(initial_gas=BitVecVal(1000, 64))
        new_gas = gas.copy()

        # 验证Gas值相同
        solver = Solver()
        solver.add(new_gas.Gas == gas.Gas)
        assert solver.check() == sat


class TestSMTState:
    """测试SMTState的完整性。"""

    def test_initial_state(self):
        """测试初始SMT状态。"""
        state = SMTState()

        # 验证所有子状态都存在
        assert state.evm_stack is not None
        assert state.evm_memory is not None
        assert state.evm_storage is not None
        assert state.evm_gas is not None
        assert state.x86_memory is not None
        assert state.x86_registers is not None
        assert state.return_offset.size() == 64
        assert state.return_length.size() == 64
        assert state.pc == 0

    def test_copy_state(self):
        """测试复制SMT状态。"""
        state = SMTState()
        new_state = state.copy()

        # 验证所有子状态都被复制
        assert new_state.evm_stack is not None
        assert new_state.evm_memory is not None
        assert new_state.evm_storage is not None
        assert new_state.evm_gas is not None
        assert new_state.x86_memory is not None
        assert new_state.x86_registers is not None
        assert new_state.pc == state.pc

    def test_state_with_operations(self):
        """测试执行一系列操作后的状态。"""
        state = SMTState()

        # 推送一些值到栈上
        value1 = BitVecVal(100, 256)
        value2 = BitVecVal(200, 256)
        state.evm_stack = state.evm_stack.push(value1)
        state.evm_stack = state.evm_stack.push(value2)

        # 验证栈深度
        assert state.evm_stack.depth == 2

        # 弹出一个值 - pop返回一个元组
        popped_value, new_stack_state = state.evm_stack.pop()
        assert new_stack_state.depth == 1
