"""gas 相关 error code 的 IR 侧建模单测。

对齐目标（解释器 = 参照侧）：解释器对外可观察的 gas 错误只有 4 类，
`gas_table.go` 里几十个 `return 0, ErrGasUintOverflow` **全部经
`interpreter.go:204-205` 塌缩成 `ErrOutOfGas`**：

    E1  逐 op constantGas 不足                interpreter.go:176   ErrOutOfGas
    E2  operation.memorySize(stack) 溢出      interpreter.go:190   ErrGasUintOverflow
    E3  SafeMul(toWordSize(memSize),32) 溢出  interpreter.go:195   ErrGasUintOverflow
    E4  dynamicGas 任何 error 或 UseGas 失败  interpreter.go:205   ErrOutOfGas

本文件覆盖 E2/E3/E4 与 cap 支（cap 属于 E4 的"dynamicGas 内部 error"一类，
故状态码是 12 而**不是** 13——最容易搞错的一处）。
"""

import pytest
from z3 import (
    BitVec, BitVecVal, BoolVal, Solver, UGT, is_false, is_true, sat, simplify, unsat,
)

from evm_ir.semantics import (
    SNAPSHOT_PRE_FEE,
    _calc_mem_size_64,
    _calc_mem_size_64_with_uint,
    _charge_dynamic_gas,
)
from evm_ir.status_code import EvmStatusCode
from state.evm_gas_state import EVMGasState, word_fee
from state.smt_state import SMTState

GUO = EvmStatusCode.GAS_UINT_OVERFLOW   # 13
OOG = EvmStatusCode.OUT_OF_GAS          # 12

TWO_200 = BitVecVal(1 << 200, 256)
MEM_SIZE_CAP = 0x1FFFFFFFE0


def _conds(branches):
    return [simplify(cond) for cond, _, _ in branches]


def _statuses(branches):
    return [int(status) for _, status, _ in branches]


def _state(symbolic_gas=True):
    return SMTState.create_initial_state(symbolic_gas=symbolic_gas)


class TestCalcMemSize64:
    """`_calc_mem_size_64` 镜像 Go calcMemSize64（evm/common.go:30）的短路顺序。"""

    def test_normal_input_leaves_no_error_branch(self):
        requested, branches = _calc_mem_size_64(BitVecVal(0, 256), BitVecVal(32, 256))
        assert simplify(requested).eq(BitVecVal(32, 64))
        assert all(is_false(c) for c in _conds(branches))

    def test_zero_length_skips_offset_check(self):
        """`RETURN(offset=2^200, length=0)` 必须是**正常**路径。

        Go 的 `if length64 == 0 { return 0, false }` 在检查 offset **之前**短路，
        x86 makeCalcMemSize64 的 `TESTQ l1; JEQ`(gas_dynamic:333) 同构。旧实现
        无条件 assume offset 高 192 位为 0，把这条合法路径排除在验证域外。
        """
        requested, branches = _calc_mem_size_64(TWO_200, BitVecVal(0, 256))
        assert simplify(requested).eq(BitVecVal(0, 64))
        assert all(is_false(c) for c in _conds(branches)), (
            "length==0 时不检查 offset，该输入在解释器与 AOT 里都不报错"
        )

    def test_length_not_uint64_is_first_branch(self):
        _, branches = _calc_mem_size_64(BitVecVal(0, 256), TWO_200)
        assert is_true(_conds(branches)[0])
        assert _statuses(branches)[0] == GUO

    def test_offset_not_uint64_when_length_nonzero(self):
        _, branches = _calc_mem_size_64(TWO_200, BitVecVal(1, 256))
        conds = _conds(branches)
        assert is_false(conds[0]), "length 是 uint64，① 应恒假"
        assert is_true(conds[1]) and _statuses(branches)[1] == GUO

    def test_offset_plus_length_carry(self):
        _, branches = _calc_mem_size_64(
            BitVecVal((1 << 64) - 1, 256), BitVecVal(2, 256)
        )
        assert is_true(_conds(branches)[2])
        assert _statuses(branches)[2] == GUO

    def test_all_branches_are_pre_fee_snapshots(self):
        _, branches = _calc_mem_size_64(BitVec("o", 256), BitVec("l", 256))
        assert all(kind == SNAPSHOT_PRE_FEE for _, _, kind in branches)

    def test_symbolic_operands_keep_branches_live(self):
        _, branches = _calc_mem_size_64(BitVec("o", 256), BitVec("l", 256))
        for cond in _conds(branches):
            assert not is_false(cond) and not is_true(cond)


class TestMemSizeCap:
    """cap 支（`memSize > 0x1FFFFFFFE0`）的状态码是 **12**，不是 13。

    Go `memoryGasCost` 返回 `ErrGasUintOverflow`，但它是 `dynamicGas` 的返回值，
    在 `interpreter.go:204-205` 被 `err != nil` 塌缩成 `ErrOutOfGas`。AOT 精确复刻：
    `gas_dynamic:517` 的 jmpIfB 直接跳 `:582` 的 `exit(OutOfGas)`。
    """

    def test_cap_exceeded_gives_out_of_gas_not_overflow(self):
        _, branches = _calc_mem_size_64(
            BitVecVal(MEM_SIZE_CAP + 1, 256), BitVecVal(1, 256)
        )
        assert is_true(_conds(branches)[-1])
        assert _statuses(branches)[-1] == OOG, "cap 支必须是 OUT_OF_GAS(12)"
        assert _statuses(branches)[-2] == GUO, "倒数第二条是 E3 的 SafeMul 溢出(13)"

    def test_requested_equal_to_cap_is_allowed(self):
        requested, branches = _calc_mem_size_64(
            BitVecVal(MEM_SIZE_CAP - 1, 256), BitVecVal(1, 256)
        )
        assert simplify(requested).eq(BitVecVal(MEM_SIZE_CAP, 64))
        assert is_false(_conds(branches)[-1]), "requested == cap 不触发（Go 是 `>`）"


class TestCalcMemSize64WithUint:
    """MLOAD/MSTORE/MSTORE8 走 calcMemSize64WithUint，length 是非零常量。"""

    def test_no_length_branches(self):
        _, with_uint = _calc_mem_size_64_with_uint(BitVec("o", 256), 32)
        _, generic = _calc_mem_size_64(BitVec("o", 256), BitVec("l", 256))
        assert len(with_uint) == len(generic) - 1, (
            "length 是非零常量 ⟹ 没有 ① length-非-uint64 分支"
        )

    def test_offset_overflow_detected(self):
        _, branches = _calc_mem_size_64_with_uint(TWO_200, 32)
        assert is_true(_conds(branches)[0])
        assert _statuses(branches)[0] == GUO

    def test_normal_offset(self):
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(64, 256), 32)
        assert simplify(requested).eq(BitVecVal(96, 64))
        assert all(is_false(c) for c in _conds(branches))

    def test_zero_const_size_is_fail_closed(self):
        """const_size=0 时 Go 走 length==0 短路，语义不同，必须抛错而非静默同构。"""
        with pytest.raises(ValueError, match="const_size"):
            _calc_mem_size_64_with_uint(BitVecVal(0, 256), 0)


class TestChargeDynamicGasNormalPath:
    """正常路径：总额一次扣、纯减法、bookkeeping 演化。

    统一用具体 gas 预算（GasCheck.FIXED_BUDGET 的真实配置）：E4 是可见机器码、无条件
    建模，预算够大时 `UGT(fee, budget)` 在 simplify 阶段折成 False，pending_errors 保持
    干净。符号 gas 下 E4 恒可满足，这些断言就无从谈起。
    """

    def test_plain_subtraction_no_clamp(self):
        state = _state(symbolic_gas=False)
        gas_before = state.evm_gas.Gas
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)

        solver = Solver()
        solver.add(state.evm_gas.Gas != gas_before - BitVecVal(3, 64))
        assert solver.check() == unsat, (
            "E4 已把 gas 不足分叉出去，正常路径必须是纯减法（不再 If 钳零）"
        )
        assert not state.pending_errors
        assert simplify(state.callengine_memory_size_bytes).eq(BitVecVal(32, 64))
        assert simplify(state.callengine_memory_gas_used).eq(BitVecVal(3, 64))

    def test_second_expansion_charges_delta_only(self):
        """两次扩展：第二次 fee 必须是 `newTotalFee - oldLastGasCost`。

        这是"gas 状态必须始终演化"的核心回归——lastGasCost 不更新会让第二次按
        `newTotal - 0` 计费，OOG 阈值本身就是错的。
        """
        state = _state(symbolic_gas=False)
        gas_before = state.evm_gas.Gas
        for offset in (0, 32):
            requested, branches = _calc_mem_size_64_with_uint(
                BitVecVal(offset, 256), 32
            )
            _charge_dynamic_gas(state, requested, branches)

        # 1 word: total=3；2 words: lin=6, quad=floor(4/512)=0 → total=6，delta=3
        solver = Solver()
        solver.add(state.evm_gas.Gas != gas_before - BitVecVal(6, 64))
        assert solver.check() == unsat, "合计应扣 3 + (6-3) = 6"
        assert simplify(state.callengine_memory_gas_used).eq(BitVecVal(6, 64))
        assert simplify(state.callengine_memory_size_bytes).eq(BitVecVal(64, 64))

    def test_word_fee_folded_into_total(self):
        """SHA3(offset=0, len=32) = memFee(3) + wordFee(1 word × Sha3WordGas 6)。"""
        state = _state(symbolic_gas=False)
        gas_before = state.evm_gas.Gas
        requested, branches = _calc_mem_size_64(BitVecVal(0, 256), BitVecVal(32, 256))
        _charge_dynamic_gas(
            state, requested, branches, [word_fee(BitVecVal(32, 64), 6)],
        )
        solver = Solver()
        solver.add(state.evm_gas.Gas != gas_before - BitVecVal(9, 64))
        assert solver.check() == unsat, "两段 fee 必须累加成一个总额"


class TestGasStateEvolvesInAllModes:
    """gas 状态语义（扣减 + bookkeeping）无条件建模，两侧一致。

    对「错误分支建了但 gas 不演化」的回归：曾经扣减 gate 在 gas_modeling_enabled 后面，
    功能等价模式下 evm_gas 停在初始值，`dynamicCost > gas` 的阈值就是错的。
    """

    def test_memory_grow_matches_ir_bookkeeping_without_symbolic_gas(self):
        """默认 symbolic_gas=False 下连续两次 MEMORYGROW，IR 与 x86 的 mem_size 一致。

        x86 侧曾有 `gas off 就 <<5` 的遗留分支（把 byte size 当 word 数、放大 32 倍），
        会让两侧 bookkeeping 分叉，下一次 expansion fee 与 OOG 阈值都不同。
        """
        from x86_64.aot_profile import GO_HPC_EVM_PROFILE
        from x86_64.go_function_semantics import GoFunctionSemantics

        # IR 侧：MSTORE(0) 然后 MSTORE(32)，requested 32 → 64
        ir = SMTState.create_initial_state()          # symbolic_gas 默认 False
        assert not ir.host_gas_uf_enabled
        fees = []
        for offset in (0, 32):
            gas_before = simplify(ir.evm_gas.Gas)
            requested, branches = _calc_mem_size_64_with_uint(BitVecVal(offset, 256), 32)
            _charge_dynamic_gas(ir, requested, branches)
            ir.pending_errors = []
            fees.append(simplify(gas_before - ir.evm_gas.Gas))

        # x86 侧：memoryGrow builtin 收到同样的 rounded byte size
        x86 = SMTState.create_initial_state()
        sem = GoFunctionSemantics(GO_HPC_EVM_PROFILE)
        for rounded in (32, 64):
            x86.callengine_builtin_arg0 = BitVecVal(rounded, 64)
            x86 = sem._handle_builtin_memory_grow(sp=0, mstate=x86)

        assert simplify(ir.callengine_memory_size_bytes).eq(BitVecVal(64, 64))
        assert simplify(x86.callengine_memory_size_bytes).eq(BitVecVal(64, 64)), (
            "x86 侧 memory size 必须与 IR 侧一致（不再 <<5）"
        )
        # 增量计费：第一次 3（1 word），第二次 3（2 words 的 6 减去已付的 3）
        assert fees[0].eq(BitVecVal(3, 64)) and fees[1].eq(BitVecVal(3, 64)), (
            f"第二次必须只扣增量 newTotalFee-oldLastGasCost，实际 {fees}"
        )

    @pytest.mark.parametrize("gas,expect_status", [
        (9, int(EvmStatusCode.STOPPED)),      # 2 + 3 + 4 恰好够
        (8, int(EvmStatusCode.OUT_OF_GAS)),   # 少 1 → 第二个 block 入口 OOG
    ])
    def test_static_oog_after_dynamic_consumption_in_earlier_block(self, gas, expect_status):
        """跨 block 累计：前一 block 的动态 gas 花掉后，下一 block 静态 gas 不足 → OOG。

        走的是执行器路径（TAG 守卫 + 无条件扣减），而不是直接调 consume_static。
        曾经静态 OOG 分支 gate 在 oog_modeling_enabled 后面、扣减却无条件且钳零，
        于是这里 IR 会给 STOPPED 而 AOT 给 OUT_OF_GAS。
        """
        from evm_ir.json_parser import CompilerEVMResult
        from evm_ir.models import EVMBlock, EvmOperator
        from evm_ir.program import EVMProgram

        def _block(pc, static_gas, ops):
            blk = EVMBlock(pc=pc, stack_depth=0, min_depth=0, max_depth=1024,
                           static_gas=static_gas, is_jump_target=False,
                           is_inner_block=False, is_stop=False)
            blk.operations = [EvmOperator(kind="TAG", pc=pc, block=blk)] + [
                EvmOperator(block=blk, **kw) for kw in ops
            ]
            return blk

        # block0: static 2 + MSTORE(offset=0) 的动态 fee 3；无控制流 op → fallthrough
        first = _block(0, 2, [
            dict(kind="PUSH", pc=1, immediate=0xab, param=1),   # value
            dict(kind="PUSH", pc=2, immediate=0, param=1),      # offset（栈顶）
            dict(kind="MSTORE", pc=3),
        ])
        second = _block(4, 4, [dict(kind="STOP", pc=5)])
        evm = EVMProgram(CompilerEVMResult([first, second]))

        state = SMTState.create_initial_state(symbolic_gas=True)
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(gas, 64))
        observations = evm.to_z3_paths(state, use_reachability_check=False).observations

        live = [int(simplify(o.status_code).as_long()) for o in observations
                if Solver().check(o.condition) == sat]
        assert live == [expect_status], (
            f"gas={gas}: 期望唯一可行终态 status={expect_status}，实际 {live}"
        )

    def test_static_then_dynamic_gas_accumulates_before_oog(self):
        """block 静态 gas 与动态 fee 累加后才判 OOG。

        静态 gas 曾经也 gate 在 gas_modeling_enabled 后面：不扣它，动态 OOG 的阈值
        就偏大，会漏掉 AOT 在动态段处的 OOG。
        """
        # gas = 静态 5 + 动态 3 刚好够 → 不 OOG
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(8, 64)).consume_static(5)
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)
        assert not state.pending_errors, "5+3 == 8 恰好够，不该 OOG"

        # gas 少 1 → 动态段 OOG
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(7, 64)).consume_static(5)
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)
        assert [int(b.status_code) for b in state.pending_errors] == [OOG], (
            "扣掉静态 5 后只剩 2 < 3，必须在动态段 OOG"
        )


class TestCreateOpsStillFailClosedForGasValues:
    """EXTCODECOPY/CREATE/CREATE2：错误码已对齐，但 gas **数值**检查仍被拒绝。

    可见 fee 建了，所以 E2/E3/cap/E4 的状态码能验；但 host UF 与 returnGas 链的交互、
    MAX_INIT_CODE_SIZE_EXCEEDED(16) 都未核实。这条断言防止有人误以为 gas 数值也覆盖了。
    """

    @pytest.mark.parametrize("kind", ["EXTCODECOPY", "CREATE", "CREATE2"])
    def test_rejected_by_dynamic_gas_guard(self, kind):
        from evm_ir.models import EVMBlock, EvmOperator
        from verification.program_verifier import _find_unsupported_dynamic_gas_ops

        block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                         static_gas=0, is_jump_target=False,
                         is_inner_block=False, is_stop=False)
        block.operations = [EvmOperator(kind=kind, pc=0, block=block)]

        class _Prog:
            blocks = [block]

        # 拒绝与 gas_check 模式无关（HOST_GAS_UF_KINDS 已不再按模式加入拒绝集）。
        rejected = _find_unsupported_dynamic_gas_ops(_Prog())
        assert any(kind in item for item in rejected), (
            f"{kind} 的 gas 数值检查必须仍被 fail-closed 拒绝，实际 {rejected}"
        )


class TestReturnGasWindow:
    """CREATE/CREATE2 的可见 fee 必须落在 dealWithAdd/SubGas 窗口**之内**。

    compileEVMCREATE（impl_amd64.go:3940-3962）:
        dealWithAddGas(rg)                     // rg = Blk.StaticGas - op.Immediate
        checkMemoryAndCalcDynamicGasCreate()   // ← 可见 fee 在窗口内
        compileGoDefinedHostFunction(...)
        dealWithSubGas(rg)

    错序不改 gas 终值（加减相消），但会让可见 fee 的 OOG 阈值少算一个 rg：
    应判 `fee > gas + rg`，错序则判 `fee > gas`。现有测试固定 static_gas=0（rg=0）
    所以看不出来。
    """

    @staticmethod
    def _run_create(kind, *, gas, static_gas, immediate, offset=0, size=32):
        from evm_ir.models import EVMBlock, EvmOperator
        from evm_ir.semantics import evm_operator_to_z3

        block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                         static_gas=static_gas, is_jump_target=False,
                         is_inner_block=False, is_stop=False)
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(gas, 64))
        # 栈序：CREATE 是 value=Back(0)，故压栈顺序 [salt,] size, offset, value
        operands = [size, offset, 0] if kind == "CREATE" else [0, size, offset, 0]
        for value in operands:
            state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))
        op = EvmOperator(kind=kind, pc=0, block=block, immediate=immediate)
        out = evm_operator_to_z3(op, state)
        pending = list(out.pending_errors)
        out.pending_errors = []
        return pending

    @pytest.mark.parametrize("kind,word_gas", [("CREATE", 2), ("CREATE2", 8)])
    def test_return_gas_raises_oog_threshold(self, kind, word_gas):
        """rg 加回后 gas 够付可见 fee → 不该 OOG。

        offset=0/size=32 ⟹ memFee=3、wordFee=1 word × word_gas ⟹ 可见 fee=3+word_gas。
        取 gas = fee-1、rg = 1，则错序判 `fee > fee-1` 会误报 OOG，正确顺序判
        `fee > fee-1+1 = fee` 为假。
        """
        fee = 3 + word_gas
        pending = self._run_create(
            kind, gas=fee - 1, static_gas=1, immediate=0,   # rg = 1 - 0 = 1
        )
        assert OOG not in [int(b.status_code) for b in pending], (
            f"{kind}: rg 加回后 gas({fee}) 够付可见 fee({fee})，不该有 OOG 分支"
        )

    @pytest.mark.parametrize("kind,word_gas", [("CREATE", 2), ("CREATE2", 8)])
    def test_still_oog_when_return_gas_insufficient(self, kind, word_gas):
        """对照：rg 加回后仍不够 → 必须 OOG（防止把分支整个搞丢）。"""
        fee = 3 + word_gas
        pending = self._run_create(
            kind, gas=fee - 3, static_gas=1, immediate=0,   # rg=1，fee-3+1 < fee
        )
        assert OOG in [int(b.status_code) for b in pending], (
            f"{kind}: gas({fee - 3}) + rg(1) < fee({fee})，必须 OOG"
        )

    @pytest.mark.parametrize("kind", ["CREATE", "CREATE2"])
    def test_return_gas_cancels_in_final_value(self, kind):
        """rg 的 add/sub 成对相消：gas 终值与 rg 无关，只有 OOG 阈值受影响。

        这里关掉 host gas UF（`host_gas_uf_enabled=False`，即 symbolic_gas 默认态）来
        隔离 returnGas 本身。**开着 UF 时终值确实会随 rg 变**——因为 UF 走
        `consume_dynamic` 的钳零，而钳零阈值在 `+rg` 之后。那不是 bug：x86 侧
        `_consume_clamp_64` 在同一位置、同一阈值（真实 ADDQ 之后、SUBQ 之前），两侧相消。
        """
        from evm_ir.models import EVMBlock, EvmOperator
        from evm_ir.semantics import evm_operator_to_z3

        finals = []
        for static_gas, immediate in ((0, 0), (10, 3)):   # rg = 0 与 rg = 7
            block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                             static_gas=static_gas, is_jump_target=False,
                             is_inner_block=False, is_stop=False)
            state = SMTState.create_initial_state()        # host_gas_uf_enabled=False
            assert not state.host_gas_uf_enabled
            state.evm_gas = EVMGasState(initial_gas=BitVecVal(10 ** 6, 64))
            operands = [32, 0, 0] if kind == "CREATE" else [0, 32, 0, 0]
            for value in operands:
                state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))
            out = evm_operator_to_z3(
                EvmOperator(kind=kind, pc=0, block=block, immediate=immediate), state
            )
            out.pending_errors = []
            finals.append(out.evm_gas.Gas)

        solver = Solver()
        solver.add(finals[0] != finals[1])
        assert solver.check() == unsat, "rg 的 add/sub 必须相消，gas 终值不应随 rg 变化"


class TestReturndatacopySnapshotPoints:
    """RETURNDATACOPY 的两组错误分支快照点不同（gas 前言先于三次 popUint256）。"""

    @staticmethod
    def _run(mem_offset, data_offset, length, return_data_size, gas):
        from evm_ir.models import EvmOperator
        from evm_ir.semantics import evm_operator_to_z3

        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(gas, 64))
        state.callengine_return_data_size_bytes = BitVecVal(return_data_size, 64)
        for value in (length, data_offset, mem_offset):   # memOffset 在栈顶
            state.evm_stack = state.evm_stack.push(BitVecVal(value, 256))
        out = evm_operator_to_z3(EvmOperator(kind="RETURNDATACOPY", pc=0), state)
        pending = list(out.pending_errors)
        out.pending_errors = []
        return pending, out

    def test_gas_branch_snapshot_keeps_operands_on_stack(self):
        """gas 前言的 exit（impl_amd64.go:3124）早于 pop → 快照里三个参数仍在栈上。"""
        pending, out = self._run(1 << 200, 0, 1, 8, 10 ** 9)
        gas_branches = [b for b in pending if b.status_code == GUO]
        assert gas_branches, "memOffset=2^200 应产出 GAS_UINT_OVERFLOW 分支"
        assert simplify(gas_branches[0].terminal_state.evm_stack.SP).as_long() == 3, (
            "gas exit 在 pop 之前，快照 SP 应仍是 3"
        )

    def test_oob_branch_snapshot_is_after_pop(self):
        """errPoint 的 ReturnDataOutOfBounds（:3143+）在 pop 之后 → 快照已弹栈。"""
        pending, out = self._run(0, 10, 4, 8, 10 ** 9)   # 10+4 > 8 → 越界
        oob = [b for b in pending
               if b.status_code == EvmStatusCode.RETURN_DATA_OUT_OF_BOUNDS]
        assert oob, "应产出 ReturnDataOutOfBounds 分支"
        assert simplify(oob[0].terminal_state.evm_stack.SP).as_long() == 0, (
            "errPoint 在 pop 之后，快照 SP 应是 0"
        )


class TestPerOpcodeWiring:
    """逐指令：槽位、word 常量、以及 MCOPY 的 max 比较宽度。"""

    @staticmethod
    def _run(kind, operands, *, immediate=None, gas=10 ** 9):
        """压栈后跑一条 opcode，返回 (state, pending_errors)。

        operands 按压栈顺序给（最后一个在栈顶），与 Go 的 stack.Back(0) 对应。
        """
        from evm_ir.models import EVMBlock, EvmOperator
        from evm_ir.semantics import evm_operator_to_z3

        block = EVMBlock(pc=0, stack_depth=0, min_depth=0, max_depth=1024,
                         static_gas=0, is_jump_target=False,
                         is_inner_block=False, is_stop=False)
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(gas, 64))
        for value in operands:
            state.evm_stack = state.evm_stack.push(
                value if hasattr(value, "size") else BitVecVal(value, 256)
            )
        op = EvmOperator(kind=kind, pc=0, block=block, immediate=immediate)
        out = evm_operator_to_z3(op, state)
        pending = list(out.pending_errors)
        out.pending_errors = []
        return out, pending

    def test_mcopy_max_is_compared_at_256_bits(self):
        """MCOPY 的 `mStart = max(dest, source)` 必须在 256 位上比。

        Go memoryMcopy 用 256-bit `Gt`；x86 compileSubValuesForCompare
        （impl_amd64.go:848-866）是 SUBQ+SBBQ×3 的全 256 位借位链。
        旧实现先 `_truncate_to_64` 再比，`dst=2^200` 截断成 0 会误选 src=0，
        于是整条溢出分支消失。
        """
        # 栈序：length, src, dst（dst 在栈顶 = Back(0)）
        _, pending = self._run("MCOPY", [1, 0, 1 << 200])
        statuses = [int(b.status_code) for b in pending]
        assert GUO in statuses, (
            f"dst=2^200 应触发 GAS_UINT_OVERFLOW(13)，实际 statuses={statuses}"
        )

    def test_mcopy_picks_larger_offset(self):
        """对照：src 更大时应选 src（同样触发溢出）。"""
        _, pending = self._run("MCOPY", [1, 1 << 200, 0])
        assert GUO in [int(b.status_code) for b in pending]

    @pytest.mark.parametrize("kind,operands,immediate", [
        # 栈序按 Go 的 Back(n)：最后一个是栈顶
        ("MSTORE", [0xab, 1 << 200], None),
        ("MSTORE8", [0xab, 1 << 200], None),
        ("MLOAD", [1 << 200], None),
        ("RETURN", [1, 1 << 200], None),
        ("REVERT", [1, 1 << 200], None),
        # SHA3 的 length 取 32：sha3_semantics 在 length=1 时 Concat 参数不足（既有
        # 限制，与 gas 无关），换个合法长度即可，溢出仍由 offset=2^200 触发。
        ("SHA3", [32, 1 << 200], None),
        ("CALLDATACOPY", [1, 0, 1 << 200], None),
        ("CODECOPY", [1, 0, 1 << 200], None),
        ("RETURNDATACOPY", [1, 0, 1 << 200], None),
        ("LOG", [1, 1 << 200], 0),
        ("EXTCODECOPY", [1, 0, 1 << 200, 0xfeed], None),
        ("CREATE", [1, 1 << 200, 0], None),
        ("CREATE2", [0, 1, 1 << 200, 0], None),
    ])
    def test_offset_overflow_yields_gas_uint_overflow(self, kind, operands, immediate):
        """每条 A 类指令 + 三个 create/extcodecopy：memOffset 高位非零 → 13。

        操作数排布让被 memorySize 使用的那个 offset 落在 2^200，其余取合法小值。
        """
        _, pending = self._run(kind, operands, immediate=immediate)
        statuses = [int(b.status_code) for b in pending]
        assert GUO in statuses, f"{kind}: 期望 13，实际 {statuses}"


class TestChargeDynamicGasE4:
    """E4：`UseGas` 失败 → OUT_OF_GAS，gas 不扣、lastGasCost 已更新。"""

    def test_concrete_gas_prunes_branch(self):
        """具体 gas（功能等价模式的 1e9）+ 具体 fee ⟹ 条件静态判死，零额外路径。"""
        state = _state(symbolic_gas=False)
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)
        assert not state.pending_errors

    def test_symbolic_gas_forks_with_correct_condition(self):
        state = _state()
        gas_before = state.evm_gas.Gas
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)

        assert len(state.pending_errors) == 1
        branch = state.pending_errors[0]
        assert branch.status_code == OOG
        solver = Solver()
        solver.add(branch.condition != UGT(BitVecVal(3, 64), gas_before))
        assert solver.check() == unsat, "条件应是 UGT(total_fee, gas)（无符号！）"

    def test_snapshot_is_post_fee(self):
        """E4 快照：gas 未扣、lastGasCost 已更新、mem_size 未更新。

        依据：`memoryGasCost` 写完 lastGasCost（gas_dynamic:578）才轮到
        `makeUseGas`；后者的 SUBQ 在 JCS 之后（:402-408），所以 gas 不扣；
        `memoryGrow` 在 UseGas 之后（:60-63），所以 mem_size 不变。
        """
        state = _state()
        gas_before = state.evm_gas.Gas
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)

        snapshot = state.pending_errors[0].terminal_state
        assert snapshot.evm_gas.Gas.eq(gas_before), "gas 必须未扣"
        assert simplify(snapshot.callengine_memory_gas_used).eq(BitVecVal(3, 64)), (
            "lastGasCost 必须已更新"
        )
        assert simplify(snapshot.callengine_memory_size_bytes).eq(BitVecVal(0, 64)), (
            "mem_size 必须未更新"
        )

    @pytest.mark.parametrize("gas,expect_oog", [(3, False), (2, True)])
    def test_boundary_total_fee_versus_gas(self, gas, expect_oog):
        """`total_fee == gas` 不 OOG、`== gas+1` 才 OOG。

        解释器 `UseGas` 是 `if gas < cost` 失败；AOT `makeUseGas` 的
        `CompileRegisterToRegister(CMPQ, from, to)` 语义是 `from - to`
        （由 makeSafeMulWithOverFlow:304、memoryGasCost:516、:548 三处注释交叉印证），
        即同样是 `gas < cost → OOG`。
        """
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(gas, 64))
        requested, branches = _calc_mem_size_64_with_uint(BitVecVal(0, 256), 32)
        _charge_dynamic_gas(state, requested, branches)

        if expect_oog:
            assert len(state.pending_errors) == 1
            assert state.pending_errors[0].status_code == OOG
        else:
            assert not state.pending_errors

    def test_pre_fee_snapshot_keeps_old_last_gas_cost(self):
        """cap 支属于 PRE_FEE：lastGasCost 必须保持**旧值**。

        与 E4 的区别在 x86 的跳转拓扑：cap 的 jmpIfB(gas_dynamic:517) 目标设在 :581，
        直接跳到 :582 的 exit，**跳过** :578 的 lastGasCost 写入；而 makeUseGas 在
        memoryGasCost 返回之后才执行，那时 :578 已经跑过。两类快照不能混。
        """
        state = _state()
        state.evm_gas = EVMGasState(initial_gas=BitVecVal(10 ** 9, 64))  # 让 E4 静态判死
        state.callengine_memory_gas_used = BitVecVal(7, 64)              # 可辨识的旧值
        requested, branches = _calc_mem_size_64(
            BitVecVal(MEM_SIZE_CAP + 1, 256), BitVecVal(1, 256)
        )
        _charge_dynamic_gas(state, requested, branches)

        # append 顺序 = 解释器检查顺序：mem-size 分支在前、E4 在后。cap 超限时
        # memWords > 0xFFFFFFFF ⟹ fee > 2^55，所以 E4 必然跟着一起为真；生产里它被
        # executor 的互斥化（effective_E4 = E4 ∧ ¬cap）消掉，这里按位置取 cap 那条。
        cap_branch = state.pending_errors[0]
        assert cap_branch.status_code == OOG and is_true(simplify(cap_branch.condition))
        assert simplify(cap_branch.terminal_state.callengine_memory_gas_used).eq(
            BitVecVal(7, 64)
        ), "cap 支跳过了 lastGasCost 写入（gas_dynamic:517→:581 越过 :578），快照必须是旧值"
        # 对照：E4 那条是 POST_FEE，lastGasCost 已更新。
        e4_branch = state.pending_errors[-1]
        assert not simplify(
            e4_branch.terminal_state.callengine_memory_gas_used == BitVecVal(7, 64)
        ).eq(BoolVal(True)), "E4 快照的 lastGasCost 应已更新，不该还是旧值"

    def test_each_branch_owns_its_snapshot(self):
        """executor 的 shared_error_snapshot 检查要求每条分支有自己的 state 副本。

        顺带回归 `SMTState.copy()` 在 pending_errors 非空时 fail-closed 的约束：
        必须先把所有快照拍完再 append，边拍边 append 会在第二条上抛 LogicError。
        """
        state = _state()
        requested, branches = _calc_mem_size_64(BitVec("o", 256), BitVec("l", 256))
        _charge_dynamic_gas(state, requested, branches)

        pending = state.pending_errors
        assert len(pending) == len(branches) + 1, "5 条 mem-size 分支 + 1 条 E4"
        assert len({id(b.terminal_state) for b in pending}) == len(pending)
        assert [int(b.status_code) for b in pending] == [13, 13, 13, 13, 12, 12]

    def test_snapshot_works_when_other_branches_already_queued(self):
        """队列非空时也要能拍快照。

        `SMTState.copy()` 在 pending_errors 非空时 fail-closed（smt_state.py:263），
        但 RETURNDATACOPY 合法地有两组分支（gas 前言的 exit 在前、errPoint 的 oob 在后），
        故 `_snapshot_for_error_branch` 临时摘队列绕过该守卫。
        """
        from evm_ir.semantics import _snapshot_for_error_branch
        from evm_ir.status_code import EvmStatusCode as SC
        from state.smt_state import PendingErrorBranch

        state = _state()
        requested, branches = _calc_mem_size_64(BitVec("o", 256), BitVec("l", 256))
        _charge_dynamic_gas(state, requested, branches)
        assert state.pending_errors, "前置条件：队列里已有 gas 分支"

        before = len(state.pending_errors)
        snapshot = _snapshot_for_error_branch(state)
        assert snapshot.pending_errors == [], "快照自身不该带待分裂队列"
        assert len(state.pending_errors) == before, "拍完快照要把队列恢复原样"
        state.pending_errors.append(
            PendingErrorBranch(condition=BoolVal(True),
                               status_code=SC.RETURN_DATA_OUT_OF_BOUNDS,
                               terminal_state=snapshot)
        )
        assert len(state.pending_errors) == before + 1
