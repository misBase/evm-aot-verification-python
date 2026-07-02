"""
GoFunctionSemantics 单元测试。

验证通过 x86 内存操作建模 Go host/builtin 函数的语义效果。
"""

import pytest
from z3 import BitVec, BitVecVal, Solver, sat, unsat, simplify

from state.smt_state import SMTState, EVMStorageState, MemoryDomain, PointerTag
from x86_64.aot_profile import GO_HPC_EVM_PROFILE, X86AOTProfile
from x86_64.go_function_semantics import GoFunctionSemantics, GoFunctionSemanticsError, StackAlignmentError, LIMBS_PER_UINT256
from x86_64.models import Register


def _make_profile_with_host(host_map):
    """创建带自定义 host 函数映射的 AOT profile。"""
    return X86AOTProfile(
        offsets=GO_HPC_EVM_PROFILE.offsets,
        status_codes=GO_HPC_EVM_PROFILE.status_codes,
        resumable_statuses=GO_HPC_EVM_PROFILE.resumable_statuses,
        builtin_functions=GO_HPC_EVM_PROFILE.builtin_functions,
        host_functions=host_map,
    )


R13_BASE = 0x10000  # callEngine 基址，与栈区域分离
R14_BASE = 0x20000  # 当前 block 的栈基准


def _make_state_with_stack(values, sp_start=0):
    """创建带初始 Uint256 栈值的 SMTState。

    这里按当前 block 的栈窗口布局初始化已有栈值：
    最后一个 value 是逻辑栈顶，位于 R14-0x20；再下面一个位于 R14-0x40。

    参数:
        values: 按 push 顺序排列的 256-bit 整数
        sp_start: block-local 初始 sp（单位：limb），默认 0

    返回:
        (state, sp_start) 元组
    """
    from x86_64.go_function_semantics import STACK_ELEMENT_SIZE

    state = SMTState()
    state.x86_registers.set_register(Register.R13, BitVecVal(R13_BASE, 64))
    state.x86_registers.set_register(Register.R14, BitVecVal(R14_BASE, 64))

    depth = len(values)
    for push_index, val in enumerate(values):
        stack_index = depth - 1 - push_index
        addr_offset = -((stack_index + 1) * STACK_ELEMENT_SIZE)
        base_offset = BitVecVal(R14_BASE + addr_offset, 64)
        state.x86_memory = state.x86_memory.store_256bit(base_offset, BitVecVal(val, 256), domain=MemoryDomain.STACK)

    return state, sp_start


def _compute_stack_addr(r14_base: int, sp: int) -> int:
    """根据 block-local sp 计算栈内存地址。

    公式：addr = r14 + sp * 8。
    这与 bias=0 时的 GoFunctionSemantics._compute_stack_address 一致。

    参数:
        r14_base: R14 基址
        sp: Go 栈指针（单位：limb）

    返回:
        绝对内存地址
    """
    from x86_64.go_function_semantics import LIMB_SIZE_BYTES
    return r14_base + sp * LIMB_SIZE_BYTES


def _assert_callengine_stack_pointer(state: SMTState, expected_sp: int) -> None:
    expected = BitVecVal(expected_sp & ((1 << 64) - 1), 64)
    sp_offset = GO_HPC_EVM_PROFILE.offsets["stack_pointer"]
    sp_from_memory = state.x86_memory.load_64bit(
        BitVecVal(R13_BASE + sp_offset, 64),
        domain=MemoryDomain.CALLENGINE,
    )

    solver = Solver()
    solver.add(state.callengine_stack_pointer_limbs != expected)
    assert solver.check() == unsat

    solver = Solver()
    solver.add(sp_from_memory != expected)
    assert solver.check() == unsat


class TestPopPush:
    """测试底层 pop/push 操作。"""

    def test_pop_single_value(self):
        """从 x86 内存弹出一个 Uint256。"""
        state, sp = _make_state_with_stack([0x1234])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        value, new_sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        solver.add(value == BitVecVal(0x1234, 256))
        assert solver.check() == sat
        assert new_sp == sp - LIMBS_PER_UINT256

    def test_push_then_pop_roundtrip(self):
        """push 后再 pop 应拿回原值。"""
        state, sp = _make_state_with_stack([])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        val = BitVecVal(0xDEADBEEF, 256)
        sp, state = sem._push_uint256(sp, val, state)
        popped, sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        solver.add(popped != val)
        assert solver.check() == unsat, "Push then pop should return the same value"

    def test_pop_two_values_order(self):
        """连续 pop 两个值，验证 LIFO 顺序。"""
        state, sp = _make_state_with_stack([0xAA, 0xBB])
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        first, sp, state = sem._pop_uint256(sp, state)
        second, sp, state = sem._pop_uint256(sp, state)

        solver = Solver()
        # 先弹出最后 push 的 0xBB，再弹出 0xAA。
        solver.add(first == BitVecVal(0xBB, 256))
        solver.add(second == BitVecVal(0xAA, 256))
        assert solver.check() == sat


class TestSloadSstore:
    """测试 SLOAD/SSTORE host 函数处理器。"""

    def test_sstore_modifies_storage(self):
        """SSTORE：pop key/value 后写入 storage。"""
        key_val = 0x42
        data_val = 0x1234

        profile = _make_profile_with_host({10: "sstore"})
        sem = GoFunctionSemantics(profile)

        # 栈从底到顶：[value, key]，key 最后 push、位于栈顶。
        state, sp = _make_state_with_stack([data_val, key_val])

        state = sem.apply(4, 10, sp, state)

        # 验证 storage 已更新。
        loaded = state.evm_storage.sload(BitVecVal(key_val, 256))
        solver = Solver()
        solver.add(loaded == BitVecVal(data_val, 256))
        assert solver.check() == sat

    def test_sload_reads_storage(self):
        """SLOAD：pop key 后 push Select(Storage, key)。"""
        key_val = 0x42
        data_val = 0x9999

        profile = _make_profile_with_host({9: "sload"})
        sem = GoFunctionSemantics(profile)

        # 预先写入 storage。
        state, sp = _make_state_with_stack([key_val])
        state.evm_storage = state.evm_storage.sstore(
            BitVecVal(key_val, 256), BitVecVal(data_val, 256)
        )

        state = sem.apply(4, 9, sp, state)

        # SLOAD 后 key 被弹出、结果被压回，因此 sp 净变化为 0。
        # 从 x86 栈顶读取压回的结果。
        result_sp = sp - LIMBS_PER_UINT256
        result_addr = _compute_stack_addr(R14_BASE, result_sp)
        result = state.x86_memory.load_256bit(BitVecVal(result_addr, 64), domain=MemoryDomain.STACK)

        solver = Solver()
        solver.add(result == BitVecVal(data_val, 256))
        assert solver.check() == sat

    def test_sstore_sload_roundtrip(self):
        """SSTORE 后再 SLOAD 应读回写入值。"""
        key_val = 0x10
        data_val = 0xABCD

        profile = _make_profile_with_host({10: "sstore", 9: "sload"})
        sem = GoFunctionSemantics(profile)

        # SSTORE：把 value 和 key 放到栈上。
        state, sp = _make_state_with_stack([data_val, key_val])
        state = sem.apply(4, 10, sp, state)

        # SSTORE 弹出两个 Uint256，sp 减少 2 * 4 limbs = 8。
        new_sp = sp - 2 * LIMBS_PER_UINT256

        # SLOAD：按栈地址公式把 key 写回栈槽。
        key_addr = _compute_stack_addr(R14_BASE, new_sp)
        state.x86_memory = state.x86_memory.store_256bit(
            BitVecVal(key_addr, 64), BitVecVal(key_val, 256), domain=MemoryDomain.STACK,
        )
        sload_sp = new_sp + LIMBS_PER_UINT256

        state = sem.apply(4, 9, sload_sp, state)

        # 按当前 block 的栈窗口地址规则读取 SLOAD 压回的结果
        result_sp = sload_sp - LIMBS_PER_UINT256
        result_addr = _compute_stack_addr(R14_BASE, result_sp)
        result = state.x86_memory.load_256bit(BitVecVal(result_addr, 64), domain=MemoryDomain.STACK)

        solver = Solver()
        solver.add(result != BitVecVal(data_val, 256))
        assert solver.check() == unsat, "SSTORE/SLOAD roundtrip should preserve value"


class TestCallFamilyEffects:
    """测试 CALL 系列的作用域化 identity 和 return-data 写入。"""

    def test_staticcall_writes_symbolic_return_data(self):
        profile = _make_profile_with_host({5: "staticCall"})
        sem = GoFunctionSemantics(profile)

        # 栈从底到顶：
        # retSize, retOffset, argsSize, argsOffset, addr, gas
        state, sp = _make_state_with_stack([2, 0x40, 4, 0, 0x1234, 1000])
        state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
        # staticCall 把返回数据写入 EVM 内存（R15+retOffset），所以读取也用 EVM 域
        old_inside = state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM)
        old_outside = state.x86_memory.load_byte(BitVecVal(0x3F, 64), domain=MemoryDomain.EVM)

        state = sem.apply(4, 5, sp, state, evm_pc=0x20)

        solver_inside = Solver()
        solver_inside.add(state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM) != old_inside)
        assert solver_inside.check() == sat

        solver_outside = Solver()
        solver_outside.add(state.x86_memory.load_byte(BitVecVal(0x3F, 64), domain=MemoryDomain.EVM) != old_outside)
        assert solver_outside.check() == unsat

    def test_staticcall_same_args_different_pc_are_independent(self):
        profile = _make_profile_with_host({5: "staticCall"})
        sem = GoFunctionSemantics(profile)

        state1, sp1 = _make_state_with_stack([2, 0x40, 4, 0, 0x1234, 1000])
        state2, sp2 = _make_state_with_stack([2, 0x40, 4, 0, 0x1234, 1000])

        state1 = sem.apply(4, 5, sp1, state1, evm_pc=0x20)
        state2 = sem.apply(4, 5, sp2, state2, evm_pc=0x24)

        result_sp1 = sp1 - 6 * LIMBS_PER_UINT256
        result_sp2 = sp2 - 6 * LIMBS_PER_UINT256
        result1 = state1.x86_memory.load_256bit(
            BitVecVal(_compute_stack_addr(R14_BASE, result_sp1), 64), domain=MemoryDomain.STACK,
        )
        result2 = state2.x86_memory.load_256bit(
            BitVecVal(_compute_stack_addr(R14_BASE, result_sp2), 64), domain=MemoryDomain.STACK,
        )

        solver = Solver()
        solver.add(result1 == BitVecVal(1, 256))
        solver.add(result2 == BitVecVal(0, 256))
        assert solver.check() == sat

    def test_staticcall_updates_return_data_source_and_callengine_mirror(self):
        profile = _make_profile_with_host({5: "staticCall"})
        sem = GoFunctionSemantics(profile)

        state, sp = _make_state_with_stack([2, 0x40, 4, 0, 0x1234, 1000])
        state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))

        state = sem.apply(4, 5, sp, state, evm_pc=0x21)

        r13 = state.x86_registers.get_register(Register.R13)
        ptr_from_mem = state.x86_memory.load_64bit(
            r13 + BitVecVal(GO_HPC_EVM_PROFILE.offsets["return_data_pointer"], 64),
            domain=MemoryDomain.CALLENGINE,
        )
        size_from_mem = state.x86_memory.load_64bit(
            r13 + BitVecVal(GO_HPC_EVM_PROFILE.offsets["return_data_size"], 64),
            domain=MemoryDomain.CALLENGINE,
        )

        solver = Solver()
        solver.add(ptr_from_mem != state.callengine_return_data_pointer)
        assert solver.check() == unsat

        solver = Solver()
        solver.add(size_from_mem != BitVecVal(2, 64))
        assert solver.check() == unsat

        first_byte = simplify(state.return_data[BitVecVal(0, 64)])
        assert "evm_static_call_ret_byte_" in str(first_byte)

    def test_apply_clears_caller_saved_pointer_tags(self):
        profile = _make_profile_with_host({5: "staticCall"})
        sem = GoFunctionSemantics(profile)

        state, sp = _make_state_with_stack([2, 0x40, 4, 0, 0x1234, 1000])
        state.x86_registers.set_pointer_tag(Register.RSI, PointerTag.CALLDATA_PTR)
        state.x86_registers.set_pointer_tag(Register.RAX, PointerTag.CODE_PTR)
        state.x86_registers.set_pointer_tag(Register.R12, PointerTag.RETURNDATA_PTR)

        state = sem.apply(4, 5, sp, state, evm_pc=0x22)

        assert state.x86_registers.get_pointer_tag(Register.RSI) == PointerTag.NONE
        assert state.x86_registers.get_pointer_tag(Register.RAX) == PointerTag.NONE
        assert state.x86_registers.get_pointer_tag(Register.R12) == PointerTag.RETURNDATA_PTR


class TestExtCodeCopyEffects:
    """测试 x86 侧 EXTCODECOPY 的符号内存写入。"""

    def test_extcodecopy_writes_symbolic_bytes_to_x86_memory(self):
        profile = _make_profile_with_host({14: "extCodeCopy"})
        sem = GoFunctionSemantics(profile)

        # 栈从底到顶：size, offset, destOffset, addr。
        state, sp = _make_state_with_stack([2, 0x10, 0x40, 0x1234])
        state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
        # extCodeCopy 写入 EVM 内存（R15+destOffset）
        old_inside = state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM)
        old_outside = state.x86_memory.load_byte(BitVecVal(0x3F, 64), domain=MemoryDomain.EVM)

        state = sem.apply(4, 14, sp, state, evm_pc=0x30)

        solver_inside = Solver()
        solver_inside.add(state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM) != old_inside)
        assert solver_inside.check() == sat

        solver_outside = Solver()
        solver_outside.add(state.x86_memory.load_byte(BitVecVal(0x3F, 64), domain=MemoryDomain.EVM) != old_outside)
        assert solver_outside.check() == unsat

    def test_extcodecopy_zero_size_leaves_x86_memory_unchanged(self):
        profile = _make_profile_with_host({14: "extCodeCopy"})
        sem = GoFunctionSemantics(profile)

        state, sp = _make_state_with_stack([0, 0x10, 0x40, 0x1234])
        state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
        old_inside = state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM)

        state = sem.apply(4, 14, sp, state, evm_pc=0x30)

        solver = Solver()
        solver.add(state.x86_memory.load_byte(BitVecVal(0x40, 64), domain=MemoryDomain.EVM) != old_inside)
        assert solver.check() == unsat


class TestBuiltinFunctions:
    """测试 builtin 函数处理器（statusCode=5）。"""

    def _read_result_after_binary_op(self, state, original_sp):
        """读取二元操作后的 x86 栈结果。

        二元操作会 pop a、pop b、push result，sp 净变化为 -4 limbs。
        结果位于 (original_sp - 2*4) 对应的栈地址。
        """
        result_sp = original_sp - 2 * LIMBS_PER_UINT256
        result_addr = _compute_stack_addr(R14_BASE, result_sp)
        return state.x86_memory.load_256bit(BitVecVal(result_addr, 64), domain=MemoryDomain.STACK)

    def test_builtin_gas_cost(self):
        """GAS builtin：push 剩余 gas（未解释函数）。"""
        # 使用包含 gas_cost 的 builtin_functions 映射。
        # gas_cost 在 GO_HPC_EVM_PROFILE.builtin_functions 中的索引是 9。
        profile = X86AOTProfile(
            offsets=GO_HPC_EVM_PROFILE.offsets,
            status_codes=GO_HPC_EVM_PROFILE.status_codes,
            resumable_statuses=GO_HPC_EVM_PROFILE.resumable_statuses,
            builtin_functions={9: "gas_cost"},  # gas_cost 的索引是 9
            host_functions={},
        )
        sem = GoFunctionSemantics(profile)

        # GAS 不弹栈，只压入结果。
        state, sp = _make_state_with_stack([])

        # gas_cost 处理器应能正常执行。
        state = sem.apply(5, 9, sp, state)

        # 验证结果写在当前 sp 对应的位置。
        result_addr = _compute_stack_addr(R14_BASE, sp)
        result = state.x86_memory.load_256bit(BitVecVal(result_addr, 64), domain=MemoryDomain.STACK)

        # 结果是 256-bit BitVec（未解释函数结果）。
        assert result.size() == 256

    def test_builtin_div(self):
        """DIV builtin：pop a（栈顶）、pop b，push a/b。"""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # 栈从底到顶：[3, 100]，栈顶为 100、次栈顶为 3。
        # DIV 弹出 a=100、b=3，压入 100/3 = 33。
        state, sp = _make_state_with_stack([3, 100])
        state = sem.apply(5, 4, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(33, 256))
        assert solver.check() == unsat, "100 / 3 should be 33"

    def test_builtin_div_by_zero(self):
        """DIV 除零应返回 0（EVM 语义）。"""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # 栈从底到顶：[0, 42]，栈顶为 42、次栈顶为 0。
        # DIV 弹出 a=42、b=0，因此按 EVM 语义得到 42/0 = 0。
        state, sp = _make_state_with_stack([0, 42])
        state = sem.apply(5, 4, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(0, 256))
        assert solver.check() == unsat, "DIV by zero must return 0"

    def test_builtin_mod(self):
        """MOD builtin：pop a（栈顶）、pop b，push a%b。"""
        from z3 import SolverFor
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # 栈从底到顶：[3, 100]，栈顶为 100、次栈顶为 3。
        # MOD 弹出 a=100、b=3，压入 100%3 = 1。
        state, sp = _make_state_with_stack([3, 100])
        state = sem.apply(5, 5, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != BitVecVal(1, 256))
        assert solver.check() == unsat, "100 % 3 should be 1"

    def test_builtin_exp(self):
        """EXP builtin 使用与 IR 侧一致的未解释函数。"""
        from z3 import Function, BitVecSort, SolverFor

        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)

        # 栈从底到顶：[10, 2]，栈顶 2 是 base，次栈顶 10 是 exp。
        # EXP 弹出 base=2、exp=10，压入 evm_exp(2, 10)。
        state, sp = _make_state_with_stack([10, 2])
        state = sem.apply(5, 8, sp, state)

        result = self._read_result_after_binary_op(state, sp)

        exp_func = Function('evm_exp', BitVecSort(256), BitVecSort(256), BitVecSort(256))
        expected = exp_func(BitVecVal(2, 256), BitVecVal(10, 256))

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result != expected)
        assert solver.check() == unsat


class TestExtractMethods:
    """测试 cfg_executor 的元数据提取方法。

    使用 muti_block 测试数据里的真实 x86 block 验证提取逻辑。
    """

    def test_extract_from_real_go_bridge_block(self):
        """从 muti_block.hex 的真实 Go bridge block 提取元数据。"""
        from pathlib import Path
        from x86_64.cfg_executor import X86SymbolicExecutor
        from x86_64.disassembler import disassemble_hex
        from x86_64.cfg import identify_basic_blocks

        test_dir = Path(__file__).parent.parent
        hex_file = test_dir / "data" / "muti_block.hex"
        if not hex_file.exists():
            pytest.skip("muti_block.hex not found")

        hex_data = hex_file.read_text().strip()
        instructions = disassemble_hex(hex_data, base_addr=0x0)
        blocks = identify_basic_blocks(instructions)

        executor = X86SymbolicExecutor(blocks, enable_go_bridge=True)

        # 查找匹配 CallGoFunction 模式的 block。
        found_go_bridge = False
        for block in blocks:
            if executor._is_call_go_function_pattern(block):
                found_go_bridge = True
                status = executor._extract_status_code(block)
                sp = executor._extract_stack_pointer(block)
                assert status is not None, f"Block 0x{block.start_addr:x} should have status_code"
                assert status in executor.aot_profile.resumable_statuses
                # SP 可能不存在（可省略）。
                if sp is not None:
                    assert isinstance(sp, int)
                break

        # 如果没有 Go bridge block 就跳过；muti_block 正常应包含它。
        if not found_go_bridge:
            pytest.skip("No Go bridge blocks found in muti_block.hex")


class TestStorageEquivalence:
    """测试 RefinementChecker 的 storage 等价检查。"""

    def test_same_storage_is_equivalent(self):
        """同一个 storage array 应判等价。"""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        verified, msg = checker._check_storage_equivalence(storage, storage)
        assert verified

    def test_different_storage_not_equivalent(self):
        """写入不同的 storage array 不应判等价。"""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort, Store

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        s1 = Store(storage, BitVecVal(0, 256), BitVecVal(1, 256))
        s2 = Store(storage, BitVecVal(0, 256), BitVecVal(2, 256))

        verified, msg = checker._check_storage_equivalence(s1, s2)
        assert not verified

    def test_same_write_is_equivalent(self):
        """写入相同的 storage array 应判等价。"""
        from verification.refinement_checker import RefinementChecker
        from z3 import Array, BitVecSort, Store

        checker = RefinementChecker(timeout_ms=5000)
        storage = Array('Storage', BitVecSort(256), BitVecSort(256))

        s1 = Store(storage, BitVecVal(42, 256), BitVecVal(100, 256))
        s2 = Store(storage, BitVecVal(42, 256), BitVecVal(100, 256))

        verified, msg = checker._check_storage_equivalence(s1, s2)
        assert verified


class TestErrorHandling:
    """测试元数据缺失或未知时的错误处理。"""

    def test_host_func_index_none_warns_and_skips(self):
        """host func_index=None 时应告警并跳过，而不是报错。"""
        profile = _make_profile_with_host({9: "sload"})
        sem = GoFunctionSemantics(profile)

        state, sp = _make_state_with_stack([0x42])

        # 不应抛异常，只告警并返回原状态。
        result = sem.apply(4, None, sp, state)
        assert result is state  # 状态不变

    def test_host_func_index_unknown_raises_error(self):
        """host func_index 未知时应抛出 GoFunctionSemanticsError。"""
        profile = _make_profile_with_host({})  # 空映射
        sem = GoFunctionSemantics(profile)

        state, sp = _make_state_with_stack([0x42])

        with pytest.raises(GoFunctionSemanticsError, match="unknown host func_index"):
            sem.apply(4, 99, sp, state)

    def test_builtin_func_index_none_warns_and_skips(self):
        """builtin func_index=None 时应告警并跳过，而不是报错。"""
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)
        state, sp = _make_state_with_stack([3, 100])

        # 不应抛异常，只告警并返回原状态。
        result = sem.apply(5, None, sp, state)
        assert result is state  # 状态不变

    def test_builtin_func_index_unknown_raises_error(self):
        """builtin func_index 未知时应抛出 GoFunctionSemanticsError。"""
        profile = X86AOTProfile(
            offsets=GO_HPC_EVM_PROFILE.offsets,
            status_codes=GO_HPC_EVM_PROFILE.status_codes,
            resumable_statuses=GO_HPC_EVM_PROFILE.resumable_statuses,
            builtin_functions={},  # 空映射
            host_functions={},
        )
        sem = GoFunctionSemantics(profile)
        state, sp = _make_state_with_stack([3, 100])

        with pytest.raises(GoFunctionSemanticsError, match="unknown builtin func_index"):
            sem.apply(5, 99, sp, state)

    def test_unknown_host_function_raises_error(self):
        """未实现的 host 函数应抛出 GoFunctionSemanticsError。"""
        profile = _make_profile_with_host({0: "unknown_func"})
        sem = GoFunctionSemantics(profile)
        state, sp = _make_state_with_stack([0x42])

        with pytest.raises(GoFunctionSemanticsError, match="unimplemented host function"):
            sem.apply(4, 0, sp, state)

    def test_unknown_builtin_function_raises_error(self):
        """未实现的 builtin 函数应抛出 GoFunctionSemanticsError。"""
        profile = X86AOTProfile(
            offsets=GO_HPC_EVM_PROFILE.offsets,
            status_codes=GO_HPC_EVM_PROFILE.status_codes,
            resumable_statuses=GO_HPC_EVM_PROFILE.resumable_statuses,
            builtin_functions={0: "unknown_func"},
            host_functions={},
        )
        sem = GoFunctionSemantics(profile)
        state, sp = _make_state_with_stack([3, 100])

        with pytest.raises(GoFunctionSemanticsError, match="unimplemented builtin function"):
            sem.apply(5, 0, sp, state)

    def test_misaligned_sp_raises_stack_alignment_error(self):
        """sp 未按 4 limbs 对齐时应抛出 StackAlignmentError。"""
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)
        state, _ = _make_state_with_stack([])

        # sp=1 未对齐（1 % 4 != 0）。
        with pytest.raises(StackAlignmentError, match="not aligned"):
            sem.apply(4, 0, 1, state)

        # sp=2 未对齐。
        with pytest.raises(StackAlignmentError, match="not aligned"):
            sem.apply(4, 0, 2, state)

        # sp=6 未对齐（6 % 4 != 0）。
        with pytest.raises(StackAlignmentError, match="not aligned"):
            sem.apply(5, 3, 6, state)

        # sp=0、4、8、12 已对齐，不应抛异常。
        for aligned_sp in [0, 4, 8, 12]:
            state, _ = _make_state_with_stack([])
            # 只验证不会抛异常。
            sem.apply(5, 3, aligned_sp, state)


class TestSha3Memory:
    """测试 SHA3 使用 x86_memory，而不是旧的 evm_memory。"""

    def test_sha3_uses_x86_memory(self):
        """SHA3 应使用 x86 EVM 域中 R15+offset 处的内存作为 hash 输入。

        该测试验证：x86 指令通过 x86_memory 改内存后，SHA3 会从同一份内存读取。
        """
        from z3 import SolverFor
        from common import uninterpreted

        profile = _make_profile_with_host({1: "sha3"})
        sem = GoFunctionSemantics(profile)

        # 创建在 offset 0 处带有 EVM 内存数据的状态。
        state = SMTState()
        state.x86_registers.set_register(Register.R13, BitVecVal(R13_BASE, 64))
        state.x86_registers.set_register(Register.R14, BitVecVal(R14_BASE, 64))
        r15_base = 0x30000
        state.x86_registers.set_register(Register.R15, BitVecVal(r15_base, 64))

        # SHA3 从 EVM 256-bit 内存（R15 域）读取。
        data = BitVecVal(0xDEADBEEF, 256)
        state.x86_memory = state.x86_memory.store_256bit(
            BitVecVal(r15_base, 64), data, domain=MemoryDomain.EVM,
        )

        # 把 offset 和 length 压栈（length=32 bytes）。
        sp = 0
        sp, state = sem._push_uint256(sp, BitVecVal(32, 256), state)  # 长度
        sp, state = sem._push_uint256(sp, BitVecVal(0, 256), state)   # 偏移

        # 执行 SHA3。
        state = sem.apply(4, 1, sp, state)

        # sha3 helper 应 hash R15 相对的 EVM 内存 slice。
        expected_hash = uninterpreted.sha3_semantics(
            state.x86_memory.evm_mem,
            BitVecVal(r15_base, 64),
            BitVecVal(0, 256),
            BitVecVal(32, 256),
        )

        # 结果应写入 sp 对应的栈内存（R14 域）。
        result_addr = _compute_stack_addr(R14_BASE, sp - 2 * LIMBS_PER_UINT256)
        result_bv = state.x86_memory.load_256bit(BitVecVal(result_addr, 64), domain=MemoryDomain.STACK)

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(result_bv != expected_hash)
        assert solver.check() == unsat

    def test_sha3_fast_path_ignores_slice_external_writes(self):
        from z3 import BitVecSort, K, SolverFor, Store
        from common import uninterpreted

        zero_mem = K(BitVecSort(64), BitVecVal(0, 8))
        noisy_mem = Store(zero_mem, BitVecVal(100, 64), BitVecVal(0xAB, 8))

        clean_hash = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(32, 256)
        )
        noisy_hash = uninterpreted.sha3_semantics(
            noisy_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(32, 256)
        )

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(clean_hash != noisy_hash)
        assert solver.check() == unsat

    def test_sha3_fast_path_equates_different_write_order(self):
        from z3 import BitVec, BitVecSort, K, SolverFor, Store
        from common import uninterpreted

        mem_forward = K(BitVecSort(64), BitVecVal(0, 8))
        mem_reverse = K(BitVecSort(64), BitVecVal(0, 8))
        symbolic_bytes = [BitVec(f"sha3_byte_{i}", 8) for i in range(32)]

        for i, byte in enumerate(symbolic_bytes):
            mem_forward = Store(mem_forward, BitVecVal(i, 64), byte)
        for i in reversed(range(32)):
            mem_reverse = Store(mem_reverse, BitVecVal(i, 64), symbolic_bytes[i])

        forward_hash = uninterpreted.sha3_semantics(
            mem_forward, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(32, 256)
        )
        reverse_hash = uninterpreted.sha3_semantics(
            mem_reverse, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(32, 256)
        )

        solver = SolverFor("QF_AUFBV")
        solver.set("timeout", 5000)
        solver.add(forward_hash != reverse_hash)
        assert solver.check() == unsat

    def test_sha3_fast_path_uses_concrete_length_data_width(self):
        from z3 import BitVecSort, K
        from common import uninterpreted

        zero_mem = K(BitVecSort(64), BitVecVal(0, 8))
        hash_5 = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(5, 256)
        )
        hash_6 = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(6, 256)
        )

        assert hash_5.decl().name() == "sha3_bytes_5"
        assert hash_6.decl().name() == "sha3_bytes_6"
        assert hash_5.arg(0).size() == 40
        assert hash_6.arg(0).size() == 48

    def test_sha3_length_identity_keeps_same_padding_unconstrained(self):
        from z3 import BitVecSort, K, SolverFor
        from common import uninterpreted

        zero_mem = K(BitVecSort(64), BitVecVal(0, 8))
        hash_5 = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(5, 256)
        )
        hash_6 = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), BitVecVal(6, 256)
        )

        equal_solver = SolverFor("QF_AUFBV")
        equal_solver.set("timeout", 5000)
        equal_solver.add(hash_5 == hash_6)
        assert equal_solver.check() == sat

        distinct_solver = SolverFor("QF_AUFBV")
        distinct_solver.set("timeout", 5000)
        distinct_solver.add(hash_5 != hash_6)
        assert distinct_solver.check() == sat

    def test_sha3_symbolic_length_uses_slice_fallback(self):
        from z3 import BitVec, BitVecSort, K
        from common import uninterpreted

        zero_mem = K(BitVecSort(64), BitVecVal(0, 8))
        symbolic_length = BitVec("sha3_symbolic_length", 256)
        hash_value = uninterpreted.sha3_semantics(
            zero_mem, BitVecVal(0, 64), BitVecVal(0, 256), symbolic_length
        )

        assert hash_value.decl().name() == "sha3_slice"


class TestLog:
    """测试 LOG host 函数处理器的 topic 数量确定逻辑。"""

    def test_evm_immediate_matching_stack_value_pops_matching_topics(self):
        """evm_immediate 与 x86 栈上的 n_topics 一致时，正常按该数量弹出 topic
        并把新 sp 写回内存（不抛错）。"""
        profile = _make_profile_with_host({17: "log"})
        sem = GoFunctionSemantics(profile)

        # 栈从底到顶：[topic1, topic0, mSize, mStart, n_topics]。
        state, sp = _make_state_with_stack([0xAAAA, 0xBBBB, 8, 0, 2])

        state = sem.apply(4, 17, sp, state, evm_immediate=2)

        expected_sp = sp - (3 + 2) * LIMBS_PER_UINT256
        _assert_callengine_stack_pointer(state, expected_sp)

    def test_evm_immediate_matches_low64_when_topic_count_high_limbs_are_dirty(self):
        """LOG 的 topic 数遵循 Go Uint64() 语义，只比较低 64 位。"""
        profile = _make_profile_with_host({17: "log"})
        sem = GoFunctionSemantics(profile)

        dirty_high_limb_topic_count = (1 << 160) | 3
        state, sp = _make_state_with_stack(
            [0xAAAA, 0xBBBB, 0xCCCC, 8, 0, dirty_high_limb_topic_count]
        )

        state = sem.apply(4, 17, sp, state, evm_immediate=3)

        expected_sp = sp - (3 + 3) * LIMBS_PER_UINT256
        _assert_callengine_stack_pointer(state, expected_sp)

    def test_evm_immediate_mismatching_stack_value_raises(self):
        """evm_immediate 与 x86 栈上实际的 n_topics 不一致时必须 fail-closed 报错，
        而不是静默信任 evm_immediate 多/少弹栈元素——否则 call-site-mapping
        顺序错配会导致 sp 语义被静默破坏。"""
        profile = _make_profile_with_host({17: "log"})
        sem = GoFunctionSemantics(profile)

        # x86 侧栈上编码的是 LOG0（n_topics=0），但 evm_immediate 声称是 LOG2。
        state, sp = _make_state_with_stack([8, 0, 0])

        with pytest.raises(GoFunctionSemanticsError):
            sem.apply(4, 17, sp, state, evm_immediate=2)

    def test_evm_immediate_with_symbolic_stack_value_raises(self):
        """有 evm_immediate 时，x86 栈上的 n_topics 也必须可化简为同一常量。"""
        profile = _make_profile_with_host({17: "log"})
        sem = GoFunctionSemantics(profile)
        state, sp = _make_state_with_stack([8, 0, 0])
        symbolic_n_topics = BitVec("log_symbolic_n_topics", 256)
        state.x86_memory = state.x86_memory.store_256bit(
            BitVecVal(R14_BASE - 0x20, 64),
            symbolic_n_topics,
            domain=MemoryDomain.STACK,
        )

        with pytest.raises(GoFunctionSemanticsError, match="symbolic"):
            sem.apply(4, 17, sp, state, evm_immediate=2)

    def test_evm_immediate_out_of_log_range_raises_even_if_stack_matches(self):
        """LOG topic 数只能是 0..4；双方一致给出非法值也必须 fail-closed。"""
        profile = _make_profile_with_host({17: "log"})
        sem = GoFunctionSemantics(profile)

        # 栈从底到顶：[topic4, topic3, topic2, topic1, topic0, mSize, mStart, n_topics=5]。
        state, sp = _make_state_with_stack([0xAAAA, 0xBBBB, 0xCCCC, 0xDDDD, 0xEEEE, 8, 0, 5])

        with pytest.raises(GoFunctionSemanticsError, match="invalid evm_immediate"):
            sem.apply(4, 17, sp, state, evm_immediate=5)
