"""``tools/call_provenance.py`` 回归：深度类倍增、100% 恢复率与两个哨兵。

锁死的是 docs/块级lockstep等价验证方案.md §3.2 / §6 阶段 0 的验收数字。两个哨兵
（压栈顺序、强制保守回退）不是锦上添花——它们分别证明"模型没有被过度拟合"和
"结构前提确实是悬崖而不是可退让的近似"，删掉它们这份分析就退化成一堆无从证伪的
数字。
"""

import copy
from dataclasses import replace
from functools import lru_cache
from typing import Dict, List, Sequence, Tuple

import pytest

from evm_ir.models import GO_MAX_INT64, EVMBlock, EvmOperator
from verification.loop_pairing import build_evm_cfg

from tools.call_provenance import (
    DEFAULT_OPTIONS,
    CallProvenance,
    DepthClassNotClosed,
    ShadowStackMiss,
    UnsupportedJumpShape,
    _collect_facts,
    analyze_call_provenance,
    build_call_provenance,
    format_report,
    load_evm_blocks,
    provenance_fingerprint,
)


# ---------------------------------------------------------------------------
# 三合约实测基线（§3.2 表格 + §6 阶段 0 验收）
#
# 这些数是**不动点**，与遍历顺序无关，所以逐个锁死整数而不是给宽松区间：
# 松一位就检不出"影子栈少压了一帧"这类退化（它的表现正是倍增从 2.55 跳到 1080）。
# ---------------------------------------------------------------------------

EXT = "tests/data/ext_contracts"

MEASURED: Dict[str, dict] = {
    "ENSRegistry": dict(
        path=f"{EXT}/ens_registry/ENSRegistry.json",
        total_blocks=127,
        return_points=22,
        return_pads=33,
        call_sites=30,
        static_recovered=30,
        return_edges=46,
        depth_class_total=161,
        max_depth_class=4,
        single_depth_blocks=103,
        multiplier=1.27,
        max_depth_seen=19,
    ),
    "CErc20": dict(
        path=f"{EXT}/compound_cerc20/CErc20.json",
        total_blocks=723,
        return_points=83,
        return_pads=192,
        call_sites=230,
        static_recovered=215,
        return_edges=915,
        depth_class_total=1842,
        max_depth_class=37,
        single_depth_blocks=483,
        multiplier=2.55,
        max_depth_seen=50,
    ),
    "Safe": dict(
        path=f"{EXT}/safe/Safe.json",
        total_blocks=742,
        return_points=83,
        return_pads=166,
        call_sites=154,
        static_recovered=148,
        return_edges=378,
        depth_class_total=1644,
        max_depth_class=31,
        single_depth_blocks=510,
        multiplier=2.22,
        max_depth_seen=53,
    ),
}

CONTRACTS = sorted(MEASURED)


@lru_cache(maxsize=None)
def _blocks(name: str) -> Tuple[EVMBlock, ...]:
    return tuple(load_evm_blocks(MEASURED[name]["path"]))


@lru_cache(maxsize=None)
def _provenance(name: str) -> CallProvenance:
    return build_call_provenance(list(_blocks(name)))


# ---------------------------------------------------------------------------
# 合成程序构造器（不依赖 fixture，用来精确控制形态）
# ---------------------------------------------------------------------------


def _push(pc: int, value: int) -> EvmOperator:
    return EvmOperator(kind="PUSH", pc=pc, immediate=value, param=1)


def _static_jump(pc: int, target: int) -> EvmOperator:
    return EvmOperator(kind="JUMP", pc=pc, immediate=target, is_static=True)


def _return_jump(pc: int, targets: Sequence[int]) -> EvmOperator:
    return EvmOperator(kind="JUMP", pc=pc, immediate_set=list(targets))


def _block(
    pc: int, stack_depth: int, ops: List[EvmOperator], min_depth: int = 0
) -> EVMBlock:
    return EVMBlock(
        pc=pc,
        stack_depth=stack_depth,
        min_depth=min_depth,
        max_depth=GO_MAX_INT64,
        static_gas=0,
        is_jump_target=True,
        is_inner_block=False,
        is_stop=False,
        operations=list(ops),
    )


def _two_caller_program() -> List[EVMBlock]:
    """两个调用点共享一个函数 f，f 的返回跳带两元 ``immediate_set``。

        0  : PUSH 20 ; JUMP 100      (call f, 返回到 20)
        20 : PUSH 40 ; JUMP 100      (再 call f, 返回到 40)
        40 : STOP
        100: JUMP {20, 40}           (f 的返回点)

    朴素 CFG 里 100 连回两个 caller，影子栈把它按上下文分开。
    """
    return [
        _block(0, 1, [_push(0, 20), _static_jump(1, 100)]),
        _block(20, 1, [_push(20, 40), _static_jump(21, 100)]),
        _block(40, 0, [EvmOperator(kind="STOP", pc=40)]),
        _block(100, -1, [_return_jump(100, [20, 40])], min_depth=1),
    ]


def _recursive_program() -> List[EVMBlock]:
    """无基例递归：块 100 每轮压一帧 pad 再尾调自己，影子栈无界增长。"""
    return [
        _block(0, 1, [_push(0, 10), _static_jump(1, 100)]),
        _block(10, 0, [EvmOperator(kind="STOP", pc=10)]),
        _block(100, 1, [_push(100, 200), _static_jump(101, 100)]),
        _block(200, -1, [_return_jump(200, [10, 200])], min_depth=1),
    ]


# ---------------------------------------------------------------------------
# A. 三合约主回归
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", CONTRACTS)
def test_measured_depth_class_numbers(name: str) -> None:
    """§3.2 的深度类倍增 1.27× / 2.55× / 2.22×，以及支撑它的每一项计数。"""
    expected = MEASURED[name]
    stats = _provenance(name).stats

    assert stats.total_blocks == expected["total_blocks"]
    assert stats.reached_blocks == expected["total_blocks"]  # 块覆盖 100%
    assert stats.return_points == expected["return_points"]
    assert stats.return_pads == expected["return_pads"]
    assert stats.call_sites == expected["call_sites"]
    assert stats.depth_class_total == expected["depth_class_total"]
    assert stats.max_depth_class == expected["max_depth_class"]
    assert stats.single_depth_blocks == expected["single_depth_blocks"]
    assert stats.depth_class_multiplier == pytest.approx(
        expected["multiplier"], abs=0.005
    )


@pytest.mark.parametrize("name", CONTRACTS)
def test_recovery_is_total_and_fixpoint_converges(name: str) -> None:
    """动态 provenance 恢复率 100%、零回退、收敛、零发散块。"""
    provenance = _provenance(name)
    stats = provenance.stats

    assert provenance.converged
    assert stats.return_edges == MEASURED[name]["return_edges"]
    assert stats.return_edges_matched == stats.return_edges
    assert stats.dynamic_recovery_rate == 1.0
    assert stats.fallback_returns == 0
    assert stats.shadow_stack_overflows == 0
    # 发散块 = 深度类撞上上限的块；实测最大 37 类，离 4096 的上限极远
    assert stats.max_depth_class < DEFAULT_OPTIONS.depth_class_cap


@pytest.mark.parametrize("name", CONTRACTS)
def test_static_intersection_criterion_is_report_only(name: str) -> None:
    """坑 1：静态交集判据在 CErc20 上只有 93%，建图不能靠它。

    它必须仍被算出来（报告要用），但恢复率允许 < 100%，而动态影子栈必须 100%。
    """
    stats = _provenance(name).stats
    assert stats.static_recovered == MEASURED[name]["static_recovered"]
    assert stats.static_recovered <= stats.call_sites
    assert stats.dynamic_recovery_rate == 1.0


@pytest.mark.parametrize("name", CONTRACTS)
def test_depth_never_below_block_min_depth(name: str) -> None:
    """自校验：``d >= block.min_depth``，且全局最小深度恒为 0。

    朴素分析沿假返回环给出 -41001 这种不可能值；这条判据是最便宜的证伪手段，
    必须保留为回归（``build_call_provenance`` 内部也强制它）。
    """
    provenance = _provenance(name)
    by_pc = {block.pc: block for block in _blocks(name)}

    for pc, depths in provenance.depth_classes.items():
        assert depths, f"块 {pc} 在 depth_classes 里却是空集"
        assert min(depths) >= by_pc[pc].min_depth, (
            f"块 {pc} 深度 {min(depths)} < min_depth {by_pc[pc].min_depth}"
        )

    assert provenance.stats.min_depth_seen == 0
    assert provenance.stats.max_depth_seen == MEASURED[name]["max_depth_seen"]


@pytest.mark.parametrize("name", CONTRACTS)
def test_context_sensitive_edges_refine_static_cfg(name: str) -> None:
    """provenance 的边只会是朴素 CFG 边的子集，且在 (pc, k) 粒度上真的更细。"""
    provenance = _provenance(name)
    naive, _ = build_evm_cfg(list(_blocks(name)))

    for pc, targets in provenance.succs.items():
        assert set(targets) <= set(naive.get(pc, ())), f"块 {pc} 冒出了静态 CFG 之外的边"

    strict = [
        key
        for key, targets in provenance.depth_succs.items()
        if set(targets) < set(naive.get(key[0], ()))
    ]
    assert strict, "depth_succs 相对静态 CFG 毫无剪枝，说明上下文敏感没生效"
    # 后继块的入口深度 = k + 本块净栈效应（与上下文无关）
    by_pc = {block.pc: block for block in _blocks(name)}
    for (pc, k), targets in provenance.depth_succs.items():
        out_depth = k + by_pc[pc].stack_depth
        for target in targets:
            assert out_depth in provenance.depth_classes[target]


@pytest.mark.parametrize("name", CONTRACTS)
def test_fingerprint_is_deterministic(name: str) -> None:
    """同一份 IR 两次分析给同一个指纹（它要进 theorem key）。"""
    first = build_call_provenance(list(_blocks(name)))
    second = build_call_provenance(list(_blocks(name)))
    assert provenance_fingerprint(first) == provenance_fingerprint(second)
    assert len(provenance_fingerprint(first)) == 16


def test_format_report_carries_the_acceptance_numbers() -> None:
    report = format_report(_provenance("ENSRegistry"), name="ENSRegistry")
    assert "1.27×" in report
    assert "46/46" in report
    assert "127/127" in report


# ---------------------------------------------------------------------------
# B. 哨兵一：同块内 pad 的压栈顺序是 load-bearing 的
#
# 反转顺序后匹配率必须塌陷。这证明"按程序序压入全部 pad"是被数据验证的机制，
# 而不是"怎么排都能凑出好看的数字"的过拟合。
# ---------------------------------------------------------------------------

# 反序哨兵用 2048 类上限 + 200 万预算跑（原型口径）；影子栈上限放开，
# 否则一旦触顶就分不清"塌陷"与"被截断"。
_REVERSED = replace(
    DEFAULT_OPTIONS,
    fail_closed=False,
    reverse_pad_push_order=True,
    depth_class_cap=2048,
    state_budget=2_000_000,
    shadow_stack_cap=10 ** 9,
)

# 实测塌陷值（动态匹配率, 倍增, 是否仍收敛）
_REVERSED_MEASURED = {
    "ENSRegistry": (0.325, 1.35, True),
    "CErc20": (0.475, 527.45, False),
    "Safe": (0.678, 796.19, True),
}


@pytest.mark.parametrize(
    "name",
    [
        "ENSRegistry",
        pytest.param("CErc20", marks=pytest.mark.slow),  # 反序展开 ~37 万条返回边
        "Safe",
    ],
)
def test_pad_push_order_is_load_bearing(name: str) -> None:
    rate, multiplier, converged = _REVERSED_MEASURED[name]
    reversed_run = analyze_call_provenance(list(_blocks(name)), _REVERSED)
    stats = reversed_run.stats

    # 正序是 100%；反序塌到三分之一到三分之二
    assert stats.dynamic_recovery_rate < 0.70
    assert stats.dynamic_recovery_rate == pytest.approx(rate, abs=0.02)
    # 倍增：ENS 1.35×，两个大合约爆到三位数
    assert stats.depth_class_multiplier == pytest.approx(multiplier, rel=0.05)
    assert stats.depth_class_multiplier > _provenance(name).stats.depth_class_multiplier
    assert reversed_run.converged is converged


def test_reversed_order_is_rejected_under_fail_closed() -> None:
    """反序在 fail-closed 模式下不是"更差的结果"，而是**直接拒绝**。"""
    options = replace(DEFAULT_OPTIONS, reverse_pad_push_order=True)
    with pytest.raises(ShadowStackMiss):
        analyze_call_provenance(list(_blocks("ENSRegistry")), options)


# ---------------------------------------------------------------------------
# C. 哨兵二：悬崖（方案 §8 验收基准 5）
#
# 强制一次保守回退，系统必须 fail-closed，而不是静默产出错误深度类。
# ---------------------------------------------------------------------------


def _widest_return_point(name: str) -> int:
    """immediate_set 最宽的返回点——回退代价最大的那一个。"""
    facts = _collect_facts(list(_blocks(name)), DEFAULT_OPTIONS)
    return max(sorted(facts.return_points), key=lambda pc: len(facts.return_points[pc]))


@pytest.mark.parametrize(
    "name", ["ENSRegistry", pytest.param("CErc20", marks=pytest.mark.slow)]
)
def test_forced_conservative_fallback_is_rejected(name: str) -> None:
    """一次强制回退 ⇒ ``ShadowStackMiss``，绝不退回"连回全部 caller"。"""
    victim = _widest_return_point(name)
    options = replace(DEFAULT_OPTIONS, distrust_return_points=frozenset({victim}))

    with pytest.raises(ShadowStackMiss) as excinfo:
        analyze_call_provenance(list(_blocks(name)), options)
    assert excinfo.value.pc == victim
    assert "不采信" in excinfo.value.reason


def test_conservative_fallback_would_corrupt_silently() -> None:
    """把同一次回退放行（``fail_closed=False``）会静默产出**错误**深度类。

    这是"必须 fail-closed"的正面证据：ENS 上一次回退就让若干块拿到负的绝对栈深
    （不可能值），倍增从 1.27 涨到 3 以上，且大批块的深度类与正确结果不同。
    """
    name = "ENSRegistry"
    victim = _widest_return_point(name)
    lenient = analyze_call_provenance(
        list(_blocks(name)),
        replace(
            DEFAULT_OPTIONS,
            fail_closed=False,
            distrust_return_points=frozenset({victim}),
        ),
    )
    baseline = _provenance(name)

    assert lenient.stats.fallback_returns > 0
    assert lenient.stats.min_depth_seen < 0, "回退没造成负深度，哨兵失去意义"
    assert lenient.stats.depth_class_multiplier > 3 * baseline.stats.depth_class_multiplier / 2
    corrupted = [
        pc
        for pc, depths in lenient.depth_classes.items()
        if depths != baseline.depth_classes.get(pc, frozenset())
    ]
    assert len(corrupted) > 50, "污染范围过小，说明未复现级联效应"


@pytest.mark.slow
def test_conservative_fallback_cliff_on_cerc20() -> None:
    """CErc20 上同一次回退直接把不动点打崩：不收敛 + 可达块大跌 + 深度荒谬。"""
    name = "CErc20"
    victim = _widest_return_point(name)
    lenient = analyze_call_provenance(
        list(_blocks(name)),
        replace(
            DEFAULT_OPTIONS,
            fail_closed=False,
            distrust_return_points=frozenset({victim}),
            depth_class_cap=2048,
            state_budget=2_000_000,
            shadow_stack_cap=10 ** 9,
        ),
    )
    assert not lenient.converged
    assert lenient.stats.reached_blocks < MEASURED[name]["total_blocks"] * 0.7
    assert lenient.stats.depth_class_multiplier > 100
    assert lenient.stats.min_depth_seen < -100


def test_build_rejects_unsound_options() -> None:
    """生产入口拒绝三个反面开关——哨兵配置不能从正门溜进来。"""
    blocks = list(_blocks("ENSRegistry"))
    for options in (
        replace(DEFAULT_OPTIONS, fail_closed=False),
        replace(DEFAULT_OPTIONS, reverse_pad_push_order=True),
        replace(DEFAULT_OPTIONS, distrust_return_points=frozenset({195})),
    ):
        with pytest.raises(ValueError):
            build_call_provenance(blocks, options)


# ---------------------------------------------------------------------------
# D. 合成程序：机制的最小可控用例
# ---------------------------------------------------------------------------


def test_two_caller_program_separates_contexts() -> None:
    provenance = build_call_provenance(_two_caller_program())

    assert provenance.converged
    assert provenance.depth_classes == {
        0: frozenset({0}),
        20: frozenset({0}),
        40: frozenset({0}),
        100: frozenset({1}),
    }
    assert provenance.succs[100] == (20, 40)  # pc 粒度是两条边的并
    # (pc, k) 粒度下每个上下文只走一条返回边——上下文敏感体现在这里
    assert provenance.depth_succs[(100, 1)] == (20, 40)
    assert provenance.stats.return_edges_matched == 2
    assert provenance.stats.fallback_returns == 0


def test_missing_pad_push_breaks_the_shadow_stack() -> None:
    """丢一帧（少压一个 pad）必须被抓住——这正是"只压本次调用的 pad"的故障形态。"""
    blocks = _two_caller_program()
    blocks[1].operations = [op for op in blocks[1].operations if op.kind != "PUSH"]

    with pytest.raises(ShadowStackMiss) as excinfo:
        build_call_provenance(blocks)
    assert excinfo.value.pc == 100


def test_all_pads_are_pushed_not_just_the_call_target_one() -> None:
    """坑 1 的最小复现：块提前压入后续调用的 continuation（CErc20 块 836 形态）。

        0  : PUSH 40 ; PUSH 20 ; JUMP 100   —— 40 是留给**后续**调用的 pad
        20 : JUMP 100                        —— 第二次调用，复用已压好的 40
        40 : STOP
        100: JUMP {20, 40}

    只压"本次调用那一个 pad"会在第二次返回时见底；压全部 pad 才对得上。
    """
    blocks = [
        _block(0, 2, [_push(0, 40), _push(1, 20), _static_jump(2, 100)]),
        _block(20, 0, [_static_jump(20, 100)]),
        _block(40, 0, [EvmOperator(kind="STOP", pc=40)]),
        _block(100, -1, [_return_jump(100, [20, 40])], min_depth=1),
    ]
    provenance = build_call_provenance(blocks)

    assert provenance.stats.return_edges_matched == 2
    assert provenance.depth_classes[40] == frozenset({0})
    # 该块不是"调用点形态"（静态判据只看到一个 pad 交集也可能歧义），
    # 但影子栈照样把两帧都记住了 —— 静态判据只进报告
    assert provenance.stats.call_sites == 1


def test_recursion_is_reported_as_not_closed() -> None:
    """递归 ⇒ 影子栈无界 ⇒ 不动点不封闭 ⇒ fail-closed 拒绝。"""
    options = replace(DEFAULT_OPTIONS, shadow_stack_cap=16)
    with pytest.raises(DepthClassNotClosed) as excinfo:
        build_call_provenance(_recursive_program(), options)
    assert "递归" in str(excinfo.value)
    assert excinfo.value.pc == 100


def test_state_budget_exhaustion_is_not_closed() -> None:
    """预算耗尽同样算不封闭（不得当成"分析完了"）。"""
    options = replace(DEFAULT_OPTIONS, state_budget=3)
    with pytest.raises(DepthClassNotClosed) as excinfo:
        build_call_provenance(list(_blocks("CErc20")), options)
    assert "预算" in str(excinfo.value)


def test_dynamic_unresolved_jump_is_rejected() -> None:
    """动态未解析 JUMP 会让 CFG 静默缺边 ⇒ 深度类不完备 ⇒ 拒绝。"""
    blocks = _two_caller_program()
    blocks[0].operations = [EvmOperator(kind="JUMP", pc=0)]
    with pytest.raises(UnsupportedJumpShape):
        build_call_provenance(blocks)


def test_jumpi_with_immediate_set_is_rejected() -> None:
    """返回形态出现在条件跳转上，影子栈模型不覆盖（三合约实测 0 例）。"""
    blocks = _two_caller_program()
    blocks[3].operations = [
        EvmOperator(kind="JUMPI", pc=100, immediate_set=[20, 40])
    ]
    with pytest.raises(UnsupportedJumpShape):
        build_call_provenance(blocks)


def test_min_depth_violation_is_rejected() -> None:
    """自校验在生产入口生效：人为抬高 min_depth 必须当场拒绝。"""
    blocks = _two_caller_program()
    blocks[2].min_depth = 3  # 块 40 实际入口深度是 0
    from tools.call_provenance import DepthClassInvariantViolated

    with pytest.raises(DepthClassInvariantViolated):
        build_call_provenance(blocks)


def test_analysis_does_not_mutate_input_blocks() -> None:
    blocks = _two_caller_program()
    snapshot = copy.deepcopy([block.to_json() for block in blocks])
    build_call_provenance(blocks)
    assert [block.to_json() for block in blocks] == snapshot
