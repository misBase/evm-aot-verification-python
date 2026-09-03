#!/usr/bin/env python3
"""循环折叠编排测试(docs/循环处理增强方案.md §4.7 / §6 管线第 0–3 步)。

聚焦**编排逻辑**本身:守卫失败怎么办、部分循环拿不到证书怎么办、截断态落在
未登记深度类上怎么办。证书内部的证明力由 test_loop_certificate_prover.py 覆盖,
这里用依赖注入替换掉分钟级的真实求解。

另有一组**反向哨兵**(验收基准 12,§8):人为交换两个同 latch 数的配对,折叠必须
拒绝。§6 的顺序配对允许这种置换直接进 `pairs`,其 fail-safe 论证此前从未被测过。
"""

from dataclasses import dataclass
from typing import Tuple

import pytest

from evm_ir.models import EVMBlock
from verification import loop_folding
from verification.loop_folding import (
    FoldedLoop,
    FoldingPlan,
    loop_exit_targets,
    pair_fingerprint_defect,
    plan_loop_folding,
    verify_cut_coverage,
)
from x86_64.loop_analysis import NaturalLoop
from x86_64.models import X86Block, X86Instruction


# ---------------------------------------------------------------------------
# loop_exit_targets:出口是"循环外的第一个节点",不是"出口边的源"
# ---------------------------------------------------------------------------

def test_exit_targets_are_outside_the_body():
    #  0 → 1 ⇄ 2 → 3
    loop = NaturalLoop(header=1, back_edges=((2, 1),), body=frozenset({1, 2}))
    succs = {0: [1], 1: [2], 2: [1, 3], 3: []}
    assert loop_exit_targets(loop, succs) == (3,)


def test_multiple_exits_are_sorted_and_deduped():
    loop = NaturalLoop(header=1, back_edges=((3, 1),), body=frozenset({1, 2, 3}))
    succs = {1: [2, 9], 2: [3, 7], 3: [1, 9], 9: [], 7: []}
    assert loop_exit_targets(loop, succs) == (7, 9)


def test_loop_without_exit_reports_empty():
    """无出口的循环必须能被上层识别出来,而不是给一个空集合就当没事。"""
    loop = NaturalLoop(header=0, back_edges=((0, 0),), body=frozenset({0}))
    assert loop_exit_targets(loop, {0: [0]}) == ()


# ---------------------------------------------------------------------------
# plan_loop_folding 的编排:用假的守卫/证书隔离出编排逻辑
# ---------------------------------------------------------------------------

@dataclass
class _FakeReport:
    pairs: Tuple = ()
    _reasons: Tuple[str, ...] = ()
    _notes: Tuple[str, ...] = ()
    evm_analysis: object = None
    x86_analysis: object = None

    def reasons(self):
        return list(self._reasons)

    def notes(self):
        return list(self._notes)

    @property
    def ok(self):
        return not self._reasons


@dataclass
class _FakeOutcome:
    _proved: bool = True
    depth_classes: Tuple[int, ...] = (2,)
    _unmet: Tuple[str, ...] = ()

    @property
    def proved(self):
        return self._proved

    @property
    def unmet_obligations(self):
        return self._unmet


# 两个"同 latch 数"的循环。指纹只差在 static_gas / min_depth 上——这正是
# 顺序配对看不见、而 TAG 序言里刻着的那两个字段。
_LOOP_A = dict(evm_pc=1, x86_addr=0x1000, static_gas=26, min_depth=2)
_LOOP_B = dict(evm_pc=2, x86_addr=0x2000, static_gas=26, min_depth=3)


def _evm_block(pc, static_gas=0, min_depth=0):
    return EVMBlock(
        pc=pc, stack_depth=0, min_depth=min_depth, max_depth=1024,
        static_gas=static_gas, is_jump_target=True, is_inner_block=False,
        is_stop=False,
    )


def _insn(addr, mnemonic, op_str):
    return X86Instruction(
        addr=addr, mnemonic=mnemonic, op_str=op_str, bytes=b"\x90" * 4, size=4
    )


def _tag_blocks(addr, static_gas, min_depth):
    """TAG 序言的两块:循环头(gas 检查)+ 落空块(栈下溢检查)。

    形状照抄 `compileEVMTag` → `makeStaticUseGas` 的实际发射;两个立即数就是
    EVM 块的 `static_gas` 与 `min_depth * 0x20`。
    """
    header = X86Block(start_addr=addr, end_addr=addr + 12, instructions=[
        _insn(addr, "mov", "rax, qword ptr [r13 + 0x70]"),
        _insn(addr + 4, "cmp", f"rax, {hex(static_gas)}"),
        _insn(addr + 8, "jb", hex(addr + 0x40)),
    ])
    fallthrough = X86Block(start_addr=addr + 12, end_addr=addr + 32, instructions=[
        _insn(addr + 12, "sub", f"rax, {hex(static_gas)}"),
        _insn(addr + 16, "mov", "qword ptr [r13 + 0x70], rax"),
        _insn(addr + 20, "mov", "rax, qword ptr [r13 + 0x30]"),
        _insn(addr + 24, "cmp", f"rax, {hex(min_depth * 0x20)}"),
        _insn(addr + 28, "jb", hex(addr + 0x50)),
    ])
    return [header, fallthrough]


def _evm_blocks():
    return [
        _evm_block(0),
        _evm_block(_LOOP_A["evm_pc"], _LOOP_A["static_gas"], _LOOP_A["min_depth"]),
        _evm_block(_LOOP_B["evm_pc"], _LOOP_B["static_gas"], _LOOP_B["min_depth"]),
    ]


def _x86_blocks():
    return (
        _tag_blocks(_LOOP_A["x86_addr"], _LOOP_A["static_gas"], _LOOP_A["min_depth"])
        + _tag_blocks(_LOOP_B["x86_addr"], _LOOP_B["static_gas"], _LOOP_B["min_depth"])
    )


def _natural_loop(header, latch):
    return NaturalLoop(header, ((latch, header),), frozenset({header, latch}))


def _patch(monkeypatch, report, outcome=None, cfg=True):
    monkeypatch.setattr(
        loop_folding, "analyze_program_pair", lambda *a, **k: report
    )
    if cfg:
        monkeypatch.setattr(
            loop_folding, "build_evm_cfg", lambda blocks: ({1: [2], 2: [1, 3]}, None)
        )
        monkeypatch.setattr(
            loop_folding, "build_x86_cfg",
            lambda blocks: ({0x1000: [0x1008], 0x1008: [0x1000, 0x1020]}, []),
        )
    if outcome is not None:
        monkeypatch.setattr(
            loop_folding, "prove_loop_certificate", lambda **kw: outcome
        )


def test_guard_failure_blocks_folding(monkeypatch):
    """守卫不过就不折叠——unpaired 回边意味着有循环既没配对也没命中引理。"""
    _patch(monkeypatch, _FakeReport(_reasons=("x86 loop without pair",)))
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert not plan.ok
    assert any("guard:" in r for r in plan.reasons)
    assert plan.folded == ()
    assert plan.evm_stop_pcs == frozenset()


def test_program_without_tier1_loops_is_a_successful_plan(monkeypatch):
    """没有 Tier-1 循环 ⇒ 计划成立且折叠为空,不是失败。"""
    _patch(monkeypatch, _FakeReport(pairs=()), cfg=False)
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert plan.ok
    assert plan.folded == ()


def test_unproved_certificate_blocks_the_whole_plan(monkeypatch):
    """一个循环拿不到证书 ⇒ 整体不折叠,而不是"折叠成功的那部分"。

    部分折叠会让未折叠的循环头也不进 stop 集合、照常展开,同时调用方却以为
    折叠已生效——这正是"看起来验过了"的那类错误。
    """
    evm_loop = NaturalLoop(1, ((2, 1),), frozenset({1, 2}))
    x86_loop = NaturalLoop(0x1000, ((0x1008, 0x1000),), frozenset({0x1000, 0x1008}))
    _patch(
        monkeypatch,
        _FakeReport(pairs=((evm_loop, x86_loop),)),
        outcome=_FakeOutcome(_proved=False, _unmet=("depth=2: base inconclusive",)),
    )
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert not plan.ok
    assert plan.folded == ()
    assert any("base inconclusive" in r for r in plan.reasons)


def test_loop_without_exit_is_rejected(monkeypatch):
    """无出口的循环不能静默折叠:要么是无限循环,要么是 CFG 分析漏了边。"""
    evm_loop = NaturalLoop(1, ((1, 1),), frozenset({1}))
    x86_loop = NaturalLoop(0x1000, ((0x1000, 0x1000),), frozenset({0x1000}))
    _patch(monkeypatch, _FakeReport(pairs=((evm_loop, x86_loop),)))
    monkeypatch.setattr(loop_folding, "build_evm_cfg", lambda b: ({1: [1]}, None))
    monkeypatch.setattr(loop_folding, "build_x86_cfg", lambda b: ({0x1000: [0x1000]}, []))
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert not plan.ok
    assert any("no exit target" in r for r in plan.reasons)


def test_proved_certificate_yields_stop_sets(monkeypatch):
    evm_loop = NaturalLoop(1, ((2, 1),), frozenset({1, 2}))
    x86_loop = NaturalLoop(0x1000, ((0x1008, 0x1000),), frozenset({0x1000, 0x1008}))
    _patch(
        monkeypatch,
        _FakeReport(pairs=((evm_loop, x86_loop),), _notes=("residual cycles",)),
        outcome=_FakeOutcome(depth_classes=(2, 3)),
    )
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert plan.ok
    assert plan.evm_stop_pcs == frozenset({1})
    assert plan.x86_stop_addrs == frozenset({0x1000})
    assert plan.folded[0].depth_classes == (2, 3)
    assert "residual cycles" in plan.notes
    assert any("folded:" in line for line in plan.describe())


def test_empty_program_is_rejected():
    plan = plan_loop_folding([], [], initial_state=None)
    assert not plan.ok


# ---------------------------------------------------------------------------
# 反向哨兵(验收基准 12):同 latch 数的配对被交换,折叠必须拒绝
#
# §6 的顺序配对按 header 排序后逐位比对 latch 数,**同 latch 数的错误置换可以
# 直接进 pairs**。这里把置换喂给折叠编排,并让证书生成一律"成功"——即模拟
# "错配的证书恰好也证出来了"这一最坏情形,以免拒绝只是搭了求解器失败的便车。
# ---------------------------------------------------------------------------

def _two_loop_report(swapped: bool):
    """两个同 latch 数(各 1 条回边)的配对;swapped 时把两侧 x86 头对调。"""
    evm_a = _natural_loop(_LOOP_A["evm_pc"], 0x11)
    evm_b = _natural_loop(_LOOP_B["evm_pc"], 0x12)
    x86_a = _natural_loop(_LOOP_A["x86_addr"], 0x1100)
    x86_b = _natural_loop(_LOOP_B["x86_addr"], 0x2100)
    assert len(evm_a.back_edges) == len(evm_b.back_edges), "前提:同 latch 数"
    pairs = ((evm_a, x86_b), (evm_b, x86_a)) if swapped else (
        (evm_a, x86_a), (evm_b, x86_b)
    )
    return _FakeReport(pairs=pairs)


def _patch_two_loop_cfg(monkeypatch):
    """两个循环各有一条出口边,保证拒绝不是"没有出口"顺带产生的。"""
    monkeypatch.setattr(
        loop_folding, "build_evm_cfg",
        lambda blocks: ({1: [0x11, 0x20], 0x11: [1], 2: [0x12, 0x21], 0x12: [2]}, None),
    )
    monkeypatch.setattr(
        loop_folding, "build_x86_cfg",
        lambda blocks: (
            {
                0x1000: [0x1100, 0x1200], 0x1100: [0x1000],
                0x2000: [0x2100, 0x2200], 0x2100: [0x2000],
            },
            [],
        ),
    )


def test_correctly_paired_loops_are_planned(monkeypatch):
    """对照组:同一对循环正确配对时必须照常折叠。

    没有这一条,上面那个哨兵可能只是因为新加的核对过严而变红——过严的核对会
    把可证的循环一并拒掉,那是达成率归零而不是健全性提升。
    """
    _patch(monkeypatch, _two_loop_report(swapped=False), outcome=_FakeOutcome(), cfg=False)
    _patch_two_loop_cfg(monkeypatch)
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert plan.ok, plan.reasons
    assert plan.evm_stop_pcs == frozenset({_LOOP_A["evm_pc"], _LOOP_B["evm_pc"]})
    assert plan.x86_stop_addrs == frozenset({_LOOP_A["x86_addr"], _LOOP_B["x86_addr"]})


def test_swapped_same_latch_pairs_are_rejected(monkeypatch):
    """哨兵:交换两个同 latch 数的 pair ⇒ 折叠计划必须失败。

    拒绝的依据是**结构指纹**:x86 循环头的 TAG 序言里刻着它编译自哪个 EVM 块
    (static_gas 与 min_depth 两个立即数),置换后对不上。不是"看起来像错配"的
    启发式,也不是靠证书求解失败——本用例里证书一律"证成功"。
    """
    _patch(monkeypatch, _two_loop_report(swapped=True), outcome=_FakeOutcome(), cfg=False)
    _patch_two_loop_cfg(monkeypatch)
    plan = plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None)
    assert not plan.ok
    assert plan.folded == ()
    assert plan.evm_stop_pcs == frozenset(), "拒绝了就不能还留 stop 集合"
    assert all("not a compiled pair" in r for r in plan.reasons), plan.reasons
    # 两条配对都错了,两条都要报出来,不能只报第一条
    assert len(plan.reasons) == 2


def test_swapped_pairs_are_rejected_before_any_certificate_is_proved(monkeypatch):
    """置换必须在**证明之前**挡掉:错配的定理讲的是另一对程序点的事,证它纯属浪费。"""
    def _boom(**kwargs):
        raise AssertionError("mispaired loops must be rejected before proving")

    _patch(monkeypatch, _two_loop_report(swapped=True), cfg=False)
    _patch_two_loop_cfg(monkeypatch)
    monkeypatch.setattr(loop_folding, "prove_loop_certificate", _boom)
    assert not plan_loop_folding(_evm_blocks(), _x86_blocks(), initial_state=None).ok


def test_unreadable_tag_prologue_is_rejected(monkeypatch):
    """取不出指纹一律拒绝——"认不出就放行"会让这条核对在 codegen 变形后静默失效。"""
    stripped = _x86_blocks()
    stripped[0] = X86Block(
        start_addr=_LOOP_A["x86_addr"], end_addr=_LOOP_A["x86_addr"] + 4,
        instructions=[_insn(_LOOP_A["x86_addr"], "jmp", hex(_LOOP_A["x86_addr"]))],
    )
    _patch(
        monkeypatch,
        _FakeReport(pairs=((
            _natural_loop(_LOOP_A["evm_pc"], 0x11),
            _natural_loop(_LOOP_A["x86_addr"], 0x1100),
        ),)),
        outcome=_FakeOutcome(),
        cfg=False,
    )
    _patch_two_loop_cfg(monkeypatch)
    plan = plan_loop_folding(_evm_blocks(), stripped, initial_state=None)
    assert not plan.ok
    assert any("no readable TAG prologue" in r for r in plan.reasons)


def test_fingerprint_reads_static_gas_and_min_depth():
    """指纹的两个分量都要参与比对:只比 gas 时,同 gas 不同 min_depth 的两个头就分不开。

    CErc20 里 pc=0x36aa 与 pc=0x3731 正是这种情形(static_gas 都是 26,
    min_depth 分别是 2/3),Permit2 的 0x1f71/0x1f9a 同理。
    """
    header, fallthrough = _tag_blocks(0x1000, 26, 2)
    assert pair_fingerprint_defect(_evm_block(1, 26, 2), header, fallthrough) is None
    assert "not a compiled pair" in pair_fingerprint_defect(
        _evm_block(1, 26, 3), header, fallthrough
    )
    assert "not a compiled pair" in pair_fingerprint_defect(
        _evm_block(1, 25, 2), header, fallthrough
    )


def test_fingerprint_requires_the_header_blocks_to_exist():
    """块表里查不到循环头 ⇒ 无法核对 ⇒ 拒绝,而不是"查不了就放行"。"""
    header, fallthrough = _tag_blocks(0x1000, 26, 2)
    assert pair_fingerprint_defect(None, header, fallthrough) is not None
    assert pair_fingerprint_defect(_evm_block(1, 26, 2), None, None) is not None
    # 落空块缺失 ⇒ min_depth 取不到 ⇒ 同样拒绝
    assert pair_fingerprint_defect(_evm_block(1, 26, 2), header, None) is not None


# ---------------------------------------------------------------------------
# verify_cut_coverage:§4.7 消费四步里"核对适用域"那一步
# ---------------------------------------------------------------------------

def _plan_with(depth_classes=(2,)):
    return FoldingPlan(
        folded=(
            FoldedLoop(
                evm_header=1,
                x86_header=0x1000,
                evm_exits=(3,),
                x86_exits=(0x1020,),
                outcome=_FakeOutcome(depth_classes=depth_classes),
            ),
        )
    )


def test_cut_state_in_certified_depth_class_is_covered():
    result = verify_cut_coverage(
        _plan_with((2, 5)), evm_cut_depths=[(1, 2), (1, 5)],
        x86_cut_headers=[0x1000],
    )
    assert result.ok
    assert result.covered == 2


def test_cut_state_outside_certified_depth_class_is_rejected():
    """深度类是定理的实例化参数,落在登记集合外就不在任何定理的适用域内。"""
    result = verify_cut_coverage(
        _plan_with((2,)), evm_cut_depths=[(1, 7)], x86_cut_headers=[],
    )
    assert not result.ok
    assert any("outside the certified classes" in r for r in result.reasons)


def test_symbolic_cut_depth_is_rejected():
    """取不出具体栈深时必须拒绝,不能当成"某个已登记的类"放行。"""
    result = verify_cut_coverage(
        _plan_with(), evm_cut_depths=[(1, None)], x86_cut_headers=[],
    )
    assert not result.ok
    assert any("symbolic stack depth" in r for r in result.reasons)


def test_cut_at_uncertified_header_is_rejected():
    result = verify_cut_coverage(
        _plan_with(), evm_cut_depths=[(0x99, 2)], x86_cut_headers=[],
    )
    assert not result.ok
    assert any("no certificate" in r for r in result.reasons)


def test_x86_cut_at_uncertified_address_is_rejected():
    result = verify_cut_coverage(
        _plan_with(), evm_cut_depths=[], x86_cut_headers=[0x2222],
    )
    assert not result.ok
    assert any("0x2222" in r for r in result.reasons)


def test_no_cut_states_is_trivially_covered():
    """程序没进循环 ⇒ 没有截断态要核对,这本身是成立的。"""
    result = verify_cut_coverage(_plan_with(), evm_cut_depths=[], x86_cut_headers=[])
    assert result.ok
    assert result.covered == 0


# ---------------------------------------------------------------------------
# 消费端的程序点核对必须是**成对**的(§4.7 消费第 1 步)
# ---------------------------------------------------------------------------

def _two_cutpoint_plan(swapped: bool):
    """两张证书。swapped 时把两个 x86 头对调,EVM 侧不动。"""
    x86_first, x86_second = (0x2000, 0x1000) if swapped else (0x1000, 0x2000)
    return FoldingPlan(
        folded=(
            FoldedLoop(1, x86_first, (3,), (0x1020,), _FakeOutcome(depth_classes=(2,))),
            FoldedLoop(2, x86_second, (4,), (0x2020,), _FakeOutcome(depth_classes=(2,))),
        )
    )


def test_paired_cutpoint_arrival_is_covered():
    """对照组:两侧都停在**同一张证书**记录的那一对程序点上 ⇒ 覆盖成立。"""
    result = verify_cut_coverage(
        _two_cutpoint_plan(swapped=False),
        evm_cut_depths=[(1, 2)], x86_cut_headers=[0x1000],
    )
    assert result.ok, result.reasons
    assert result.covered == 1


def test_one_sided_cutpoint_arrival_is_rejected():
    """哨兵:配对被交换后,实际执行只到达证书那一对程序点的一半 ⇒ 必须拒绝。

    这是 §4.7 消费第 1 步("EVM pc 与 x86 addr 必须同时匹配证书记录的那一对")
    的反向用例。只按单侧成员资格核对时,EVM 停在 pc=1(计划里有)、x86 停在
    0x1000(计划里也有),两个单侧断言都成立,置换就这么溜过去了——那正是
    §6 fail-safe 论证里"错配的证书永远不会被消费"没有被兑现的地方。
    """
    result = verify_cut_coverage(
        _two_cutpoint_plan(swapped=True),
        evm_cut_depths=[(1, 2)], x86_cut_headers=[0x1000],
    )
    assert not result.ok
    assert any("on the EVM side only" in r for r in result.reasons), result.reasons
    assert any("on the x86 side only" in r for r in result.reasons), result.reasons


def test_unreached_certificate_is_not_a_coverage_gap():
    """两侧都没到达某张证书 ⇒ 它只是没被用上,不构成覆盖缺口。

    把"未消费"也算成缺口会误伤:折叠后每条路径只在**第一个**循环头截断,
    循环之后的循环头本来就到不了。
    """
    result = verify_cut_coverage(
        _two_cutpoint_plan(swapped=False),
        evm_cut_depths=[(1, 2)], x86_cut_headers=[0x1000],
    )
    assert result.ok


def test_plan_with_duplicate_headers_is_rejected():
    """两张证书共用一个循环头 ⇒ 按 header 建的索引会静默丢掉一张 ⇒ 拒绝。"""
    plan = FoldingPlan(
        folded=(
            FoldedLoop(1, 0x1000, (3,), (0x1020,), _FakeOutcome(depth_classes=(2,))),
            FoldedLoop(2, 0x1000, (4,), (0x2020,), _FakeOutcome(depth_classes=(2,))),
        )
    )
    result = verify_cut_coverage(plan, evm_cut_depths=[], x86_cut_headers=[])
    assert not result.ok
    assert any("one-to-one" in r for r in result.reasons)
