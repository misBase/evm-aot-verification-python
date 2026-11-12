#!/usr/bin/env python3
"""§4.8 OOG 谓词先证后桥接(docs/循环处理增强方案.md §4.8)。

守的是这条不可退让的纪律:

> 严禁表述成"两侧共享 OOG 判定"——直接让两侧用同一个 Boolean 就把待证命题
> 假设掉了:x86 静态 gas 常量编错导致 `oog_evm = gas < 10` 而
> `oog_x86 = gas < 11`,这类 codegen bug 会被完全掩盖。

因此本文件的**核心用例是验收基准 5**(§8):人为让 x86 侧静态 gas 常量与 EVM 侧
差 1,等价性查询必须给出 SAT ⇒ 桥接被拒绝。它是"两侧谓词确实各自独立生成"的
唯一哨兵——如果哪天有人把实现改成共享一个 Boolean,别的测试都不会红,只有它会。
"""

from z3 import BitVec, BitVecVal, ULT

from common.oog_bridge import (
    OogPartition,
    evm_oog_predicate,
    evm_oog_threshold,
    verified_oog_bridge,
    x86_oog_predicate,
    x86_tag_gas_guard,
)
from state.smt_state import SMTState
from x86_64.aot_profile import AOT_COMPILER_PROFILE

GAS_OFF = AOT_COMPILER_PROFILE.offsets["gas_remaining"]


# ---------------------------------------------------------------------------
# 测试替身:最小的 EVM block / x86 block 形状
# ---------------------------------------------------------------------------

class _Op:
    def __init__(self, kind):
        self.kind = kind


class _EvmBlock:
    """EVM 块替身。

    **必须带 TAG 操作**:`evm_ir/cfg_executor.py` 只在「块含 TAG 且
    static_gas 非 0」时才建 OOG 分支,`evm_oog_threshold` 与之逐字对齐。
    少了 TAG 就没有分叉可桥接。
    """

    def __init__(self, static_gas, has_tag=True):
        self.static_gas = static_gas
        self.operations = [_Op("TAG")] if has_tag else []


class _Insn:
    def __init__(self, mnemonic, op_str):
        self.mnemonic = mnemonic
        self.op_str = op_str


class _X86Block:
    """TAG 序言的 gas 守卫三条:mov / cmp / jb。"""

    def __init__(self, threshold, reg="rax", offset=GAS_OFF, target=0x1234,
                 jcc="jb"):
        self.instructions = [
            _Insn("mov", f"{reg}, qword ptr [r13 + {hex(offset)}]"),
            _Insn("cmp", f"{reg}, {hex(threshold)}"),
            _Insn(jcc, hex(target)),
        ]


def _states():
    """两侧状态:gas 是**同一个**符号(R 的 gas 分量保证两侧相等)。

    注意这不是"共享判定"——共享的是 gas **这个状态量**(那正是 R 钉住的),
    而两侧的**谓词**仍各自用各自的阈值构造。阈值才是可能编错的东西。
    """
    gas = BitVec("cut_gas", 64)
    evm_state = SMTState.create_initial_state()
    x86_state = SMTState.create_initial_state()
    evm_state.evm_gas.Gas = gas
    x86_state.callengine_gas_remaining = gas
    return evm_state, x86_state


def _bridge(evm_gas_const, x86_gas_const):
    evm_state, x86_state = _states()
    evm_pred = evm_oog_predicate(_EvmBlock(evm_gas_const), evm_state)
    x86_pred = x86_oog_predicate(
        _X86Block(x86_gas_const), x86_state, gas_offset=GAS_OFF
    )
    return verified_oog_bridge(
        evm_pred, x86_pred, assumptions=(),
        evm_threshold=evm_gas_const, x86_threshold=x86_gas_const,
    )


# ---------------------------------------------------------------------------
# 验收基准 5:常量差 1 必须拒绝桥接
# ---------------------------------------------------------------------------

class TestAcceptance5ConstantMismatch:
    """人为让 x86 侧静态 gas 常量与 EVM 差 1 ⇒ 桥接必须被拒。"""

    def test_off_by_one_is_refuted(self):
        report = _bridge(evm_gas_const=10, x86_gas_const=11)
        assert not report.bridged
        assert report.status == "refuted", (
            "两侧阈值差 1 时存在 gas 让判定分叉(gas==10),等价性查询必须 SAT。"
            "拿到 bridged 说明实现把两侧当成了同一个谓词——正是 §4.8 禁止的那件事"
        )
        # 反向也一样:方向不影响结论
        assert _bridge(evm_gas_const=11, x86_gas_const=10).status == "refuted"

    def test_refuted_is_not_reported_as_a_counterexample(self):
        """`refuted` 只表示"放弃这项优化",不是"发现了 bug"。

        §4.8 与 §6 的纪律:桥接失败必须退回完整枚举,真正的等价义务由
        ②(a)/②(d) 的主证明负责报告。所以这里只该看到一个状态字与理由,
        不该出现任何"counterexample"式的结论。
        """
        report = _bridge(evm_gas_const=10, x86_gas_const=11)
        assert report.partition is None
        assert report.reason
        assert "counterexample" not in report.reason.lower()

    def test_matching_constants_bridge(self):
        report = _bridge(evm_gas_const=30, x86_gas_const=30)
        assert report.bridged
        assert report.status == "bridged"

    def test_partition_keeps_both_predicates_separate(self):
        """分区必须保留两侧各自的谓词,不合并成一个 Boolean(§4.8)。"""
        partition = _bridge(30, 30).partition
        assert isinstance(partition, OogPartition)
        assert partition.evm_predicate is not partition.x86_predicate
        assert partition.evm_threshold == partition.x86_threshold == 30


# ---------------------------------------------------------------------------
# 谓词来源:x86 侧必须读机器码里的立即数
# ---------------------------------------------------------------------------

class TestPredicateSources:
    def test_x86_threshold_comes_from_the_machine_code(self):
        """x86 阈值来自 `cmp` 的立即数,与 EVM 的 static_gas 无关。

        图省事复用 EVM 的 `static_gas` 就是"共享判定"的变体——常量编错的
        codegen bug 会被一并掩盖。
        """
        guard = x86_tag_gas_guard(_X86Block(0x1E), gas_offset=GAS_OFF)
        assert guard is not None
        assert guard.threshold == 0x1E
        assert guard.oog_target == 0x1234

    def test_evm_threshold_comes_from_the_ir_block(self):
        assert evm_oog_threshold(_EvmBlock(0x1E)) == 0x1E

    def test_block_without_static_gas_has_no_oog_fork(self):
        """没有静态 gas 的块不产生 OOG 分叉 ⇒ 无谓词可桥接。"""
        assert evm_oog_threshold(_EvmBlock(0)) is None
        evm_state, _ = _states()
        assert evm_oog_predicate(_EvmBlock(0), evm_state) is None

    def test_block_without_tag_has_no_oog_fork(self):
        """没有 TAG 的块**也**不产生 OOG 分叉,即使 static_gas 非 0。

        执行器的 OOG 分支挂在 TAG 序言上;对无 TAG 的块给出谓词,就是对一个
        **不存在的分支**做断言——桥接会把一个从未发生的分叉当成分区键。
        """
        assert evm_oog_threshold(_EvmBlock(30, has_tag=False)) is None


# ---------------------------------------------------------------------------
# fail-closed:解析不出来一律不桥接
# ---------------------------------------------------------------------------

class TestFailClosed:
    def test_wrong_gas_field_offset_does_not_match(self):
        """读的不是 gas 字段 ⇒ 这不是 gas 守卫,不能冒充 OOG 分区键。"""
        assert x86_tag_gas_guard(
            _X86Block(30, offset=0x18), gas_offset=GAS_OFF
        ) is None

    def test_cmp_against_a_different_register_does_not_match(self):
        block = _X86Block(30)
        block.instructions[1] = _Insn("cmp", "rbx, 0x1e")  # 比的不是刚读出的 gas
        assert x86_tag_gas_guard(block, gas_offset=GAS_OFF) is None

    def test_non_jb_branch_does_not_match(self):
        assert x86_tag_gas_guard(
            _X86Block(30, jcc="jne"), gas_offset=GAS_OFF
        ) is None

    def test_alignment_nops_do_not_break_parsing(self):
        """codegen 会在序言中间插对齐 nop —— 解析必须跳过它们。

        实测:CErc20 的 0x1e65b / 0xbe03b 就是 `mov ; nop ; cmp ; jb`。不滤 nop
        时这两个循环头拿不到谓词,桥接覆盖率从 9/9 掉到 7/9。方向上是
        fail-closed(解析不出就不桥接),但白丢覆盖率。
        """
        block = _X86Block(30)
        block.instructions.insert(1, _Insn("nop", ""))
        guard = x86_tag_gas_guard(block, gas_offset=GAS_OFF)
        assert guard is not None and guard.threshold == 30

    def test_oog_stub_callback_can_reject_a_shape_match(self):
        """形状对但 `jb` 跳去的不是 OOG stub ⇒ "这是 OOG 分支"就是未经核实的断言。"""
        assert x86_tag_gas_guard(
            _X86Block(30), gas_offset=GAS_OFF, oog_stub_ok=lambda _t: False
        ) is None
        assert x86_tag_gas_guard(
            _X86Block(30), gas_offset=GAS_OFF, oog_stub_ok=lambda _t: True
        ) is not None

    def test_missing_predicate_is_unavailable_not_bridged(self):
        evm_state, x86_state = _states()
        evm_pred = evm_oog_predicate(_EvmBlock(30), evm_state)
        report = verified_oog_bridge(evm_pred, None)
        assert not report.bridged
        assert report.status == "unavailable"

    def test_assumptions_can_make_two_different_thresholds_equivalent(self):
        """前提足够强时不同阈值也可等价——桥接依据的是**证明**而非常量相等。

        这里加一条 `gas >= 100`,于是 `gas<10` 与 `gas<11` 在该域内同为假。
        它同时说明:桥接结论是**相对于 assumptions** 的,换前提必须重证。
        """
        evm_state, x86_state = _states()
        gas = evm_state.evm_gas.Gas
        report = verified_oog_bridge(
            evm_oog_predicate(_EvmBlock(10), evm_state),
            x86_oog_predicate(_X86Block(11), x86_state, gas_offset=GAS_OFF),
            assumptions=(ULT(BitVecVal(99, 64), gas),),
        )
        assert report.bridged
