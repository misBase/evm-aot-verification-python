#!/usr/bin/env python3
"""P1：支配分析、natural loop 识别、EVM/x86 循环配对与 §6 结构守卫测试。

关键语义（docs/循环处理增强方案.md §3.1/§6）：
- natural loop 回边 = 边 u→h 且 h 支配 u；"目标地址在前"不是循环
  （Solidity 函数调用/返回伪回边严禁误判）。
- 不可归约 CFG（去掉 back edges 后仍有环）必须显式暴露。
- dynamic_unresolved 跳转（无 immediate 也无 immediate_set）必须计数并记录站点。
"""

import os

import pytest

from evm_ir.models import EVMBlock, EvmOperator
from verification.loop_pairing import (
    LoopGuardReport,
    NaturalLoop,
    analyze_evm_blocks,
    build_evm_cfg,
    classify_raw_jump_ops,
    compute_idoms,
    count_backward_target_edges,
    find_natural_loops,
    pair_natural_loops,
)


# ---------------------------------------------------------------------------
# 图算法层
# ---------------------------------------------------------------------------

def test_diamond_has_no_loops():
    succs = {0: [1, 2], 1: [3], 2: [3], 3: []}
    analysis = find_natural_loops(succs, entry=0)
    assert analysis.loops == ()
    assert not analysis.irreducible


def test_self_loop_is_natural_loop():
    succs = {0: [1], 1: [1, 2], 2: []}
    analysis = find_natural_loops(succs, entry=0)
    assert len(analysis.loops) == 1
    loop = analysis.loops[0]
    assert loop.header == 1
    assert loop.back_edges == ((1, 1),)
    assert loop.body == frozenset({1})


def test_while_loop_header_latch_body():
    # 0 → 1(header) → 2(latch) → 1；1 → 3 出口
    succs = {0: [1], 1: [2, 3], 2: [1], 3: []}
    analysis = find_natural_loops(succs, entry=0)
    assert len(analysis.loops) == 1
    loop = analysis.loops[0]
    assert loop.header == 1
    assert loop.back_edges == ((2, 1),)
    assert loop.body == frozenset({1, 2})


def test_call_return_pseudo_back_edge_is_not_loop():
    """共享子例程位于前部块：按序回跳 ≠ 循环。

    0 → 1(子例程) → 3；0 → 2 → 1（按地址序回跳，但 1 不支配 2）。
    """
    succs = {0: [1, 2], 1: [3], 2: [1], 3: []}
    analysis = find_natural_loops(succs, entry=0)
    assert analysis.loops == ()
    # 按序回跳统计能看到这 1 条
    assert count_backward_target_edges(succs, order=[0, 1, 2, 3]) == 1


def test_nested_loops_two_headers():
    # 外层 1..3（latch 3），内层 2 自环
    succs = {0: [1], 1: [2], 2: [2, 3], 3: [1, 4], 4: []}
    analysis = find_natural_loops(succs, entry=0)
    headers = {loop.header for loop in analysis.loops}
    assert headers == {1, 2}
    outer = next(l for l in analysis.loops if l.header == 1)
    assert outer.body == frozenset({1, 2, 3})


def test_multi_latch_loops_share_header():
    succs = {0: [1], 1: [2, 3], 2: [1], 3: [1, 4], 4: []}
    analysis = find_natural_loops(succs, entry=0)
    assert len(analysis.loops) == 1
    loop = analysis.loops[0]
    assert loop.header == 1
    assert set(loop.back_edges) == {(2, 1), (3, 1)}


def test_irreducible_cfg_is_flagged():
    # 双入口环 1↔2：没有 natural loop back edge，但有环 → irreducible
    succs = {0: [1, 2], 1: [2, 3], 2: [1, 3], 3: []}
    analysis = find_natural_loops(succs, entry=0)
    assert analysis.loops == ()
    assert analysis.irreducible


def test_idom_basic():
    succs = {0: [1, 2], 1: [3], 2: [3], 3: []}
    idoms = compute_idoms(succs, entry=0)
    assert idoms[3] == 0
    assert idoms[1] == 0 and idoms[2] == 0


# ---------------------------------------------------------------------------
# EVM CFG 构建层
# ---------------------------------------------------------------------------

def _block(pc, ops):
    block = EVMBlock(
        pc=pc, stack_depth=0, min_depth=0, max_depth=1024, static_gas=0,
        is_jump_target=False, is_inner_block=False, is_stop=False,
        operations=ops,
    )
    for op in ops:
        op.block = block
    return block


def test_build_evm_cfg_static_jump_and_jumpi():
    blocks = [
        _block(0, [EvmOperator(kind="JUMPI", pc=0, immediate=20, is_static=True)]),
        _block(10, [EvmOperator(kind="JUMP", pc=10, immediate=0, is_static=True)]),
        _block(20, [EvmOperator(kind="STOP", pc=20)]),
    ]
    succs, classification = build_evm_cfg(blocks)
    assert succs[0] == [20, 10]  # taken + fallthrough
    assert succs[10] == [0]
    assert succs[20] == []
    assert classification.static_single == 2
    assert classification.dynamic_unresolved == 0


def test_build_evm_cfg_jumpi_immediate_set_is_resolved_multi():
    """JUMPI 带 immediate_set 必须按 resolved_multi 处理（taken 边显式 +
    fallthrough），不得计成 dynamic_unresolved。"""
    blocks = [
        _block(0, [EvmOperator(kind="JUMPI", pc=0, immediate_set=[20, 30])]),
        _block(10, [EvmOperator(kind="STOP", pc=10)]),
        _block(20, [EvmOperator(kind="STOP", pc=20)]),
        _block(30, [EvmOperator(kind="STOP", pc=30)]),
    ]
    succs, classification = build_evm_cfg(blocks)
    assert sorted(succs[0]) == [10, 20, 30]  # taken×2 + fallthrough
    assert classification.resolved_multi == 1
    assert classification.dynamic_unresolved == 0


def test_build_evm_cfg_immediate_set_and_dynamic():
    blocks = [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate_set=[10, 20])]),
        _block(10, [EvmOperator(kind="JUMP", pc=10)]),  # dynamic_unresolved
        _block(20, [EvmOperator(kind="STOP", pc=20)]),
    ]
    succs, classification = build_evm_cfg(blocks)
    assert sorted(succs[0]) == [10, 20]
    assert succs[10] == []
    assert classification.resolved_multi == 1
    assert classification.dynamic_unresolved == 1
    assert classification.dynamic_sites == [10]


def test_analyze_evm_blocks_finds_source_loop():
    # 0 → 10(header) → 20(body,latch) → 10；10 → 30 出口
    blocks = [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate=10, is_static=True)]),
        _block(10, [EvmOperator(kind="JUMPI", pc=10, immediate=30, is_static=True)]),
        _block(20, [EvmOperator(kind="JUMP", pc=20, immediate=10, is_static=True)]),
        _block(30, [EvmOperator(kind="STOP", pc=30)]),
    ]
    analysis, classification = analyze_evm_blocks(blocks)
    assert len(analysis.loops) == 1
    assert analysis.loops[0].header == 10
    assert analysis.loops[0].back_edges == ((20, 10),)


# ---------------------------------------------------------------------------
# 配对层
# ---------------------------------------------------------------------------

def _loop(header, *latches):
    return NaturalLoop(
        header=header,
        back_edges=tuple((latch, header) for latch in latches),
        body=frozenset({header, *latches}),
    )


def test_pairing_by_order_with_structure_check():
    evm_loops = (_loop(10, 20), _loop(50, 60, 70))
    x86_loops = (_loop(0x100, 0x120), _loop(0x500, 0x520, 0x540))
    pairs, unpaired_evm, unpaired_x86 = pair_natural_loops(evm_loops, x86_loops)
    assert len(pairs) == 2
    assert not unpaired_evm and not unpaired_x86


def test_pairing_latch_count_mismatch_fails_closed():
    evm_loops = (_loop(10, 20),)
    x86_loops = (_loop(0x100, 0x120, 0x140),)  # latch 数不同
    pairs, unpaired_evm, unpaired_x86 = pair_natural_loops(evm_loops, x86_loops)
    assert pairs == []
    assert list(unpaired_evm) == [evm_loops[0]]
    assert list(unpaired_x86) == [x86_loops[0]]


def test_pairing_count_mismatch_fails_closed():
    evm_loops = (_loop(10, 20),)
    x86_loops = ()
    pairs, unpaired_evm, unpaired_x86 = pair_natural_loops(evm_loops, x86_loops)
    assert pairs == []
    assert list(unpaired_evm) == [evm_loops[0]]


# ---------------------------------------------------------------------------
# §3.1 验收基准：CErc20 / Safe fixture 统计复现
# ---------------------------------------------------------------------------

_CERC20 = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.json",
)
_SAFE = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts", "safe", "Safe.json",
)


@pytest.mark.skipif(not os.path.exists(_CERC20), reason="CErc20 fixture missing")
def test_cerc20_stats_match_design_doc():
    from evm_ir.json_parser import load_ir_from_json

    blocks = load_ir_from_json(_CERC20).blocks
    assert len(blocks) == 723

    # §3.1 原始口径（含终止指令后的死代码尾跳）
    raw = classify_raw_jump_ops(blocks)
    assert raw.static_single == 640
    assert raw.resolved_multi == 83
    assert raw.dynamic_unresolved == 0

    # 守卫口径（仅活控制流）也必须无 dynamic
    _, classification = build_evm_cfg(blocks)
    assert classification.dynamic_unresolved == 0
    assert classification.missing_targets == []

    analysis, _ = analyze_evm_blocks(blocks)
    assert len(analysis.loops) == 9  # 约 8/9 个循环头（§3.1）
    assert analysis.back_edge_count == 18
    # 多 latch 共享头（§3.1："一个循环头对 4–6 个 latch"）
    assert max(len(l.back_edges) for l in analysis.loops) == 6
    # immediate_set 调用/返回过近似必然产生残环——信息性，不是守卫失败
    assert analysis.irreducible


_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_cerc20_full_pairing_with_tier2_templates():
    """P1+P3(i) 验收：TAG 序言分层 + 模板过滤后，CErc20 两侧 9↔9 全配对。"""
    from evm_ir.json_parser import load_ir_from_json
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from x86_64.loop_templates import make_tier2_matcher
    from verification.loop_pairing import analyze_program_pair

    evm_blocks = load_ir_from_json(_CERC20).blocks
    hex_str = open(_CERC20_HEX).read().strip()
    x86_blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    by_addr = {b.start_addr: b for b in x86_blocks}

    # 实验模式：模板匹配即放行——验证匹配器覆盖全部 39 条 codegen 循环
    report = analyze_program_pair(
        evm_blocks, x86_blocks,
        tier2_matcher=make_tier2_matcher(by_addr, require_proven_lemma=False),
    )
    assert len(report.pairs) == 9
    assert not report.unpaired_evm and not report.unpaired_x86
    assert report.ok
    # latch 轮廓逐对相等（结构校验实际生效）
    for evm_loop, x86_loop in report.pairs:
        assert len(evm_loop.back_edges) == len(x86_loop.back_edges)

    # fail-closed 模式（默认）：P3(ii) 六条形态引理已证
    # （tests/integration/test_tier2_lemmas.py），精确匹配 39/39 放行
    strict = analyze_program_pair(
        evm_blocks, x86_blocks, tier2_matcher=make_tier2_matcher(by_addr),
    )
    assert strict.ok
    assert len(strict.pairs) == 9
    assert not strict.unpaired_evm and not strict.unpaired_x86


@pytest.mark.skipif(not os.path.exists(_SAFE), reason="Safe fixture missing")
def test_safe_stats_match_design_doc():
    from evm_ir.json_parser import load_ir_from_json

    blocks = load_ir_from_json(_SAFE).blocks
    assert len(blocks) == 742

    raw = classify_raw_jump_ops(blocks)
    assert raw.static_single == 659
    assert raw.resolved_multi == 83
    assert raw.dynamic_unresolved == 0

    _, classification = build_evm_cfg(blocks)
    assert classification.dynamic_unresolved == 0
    assert classification.missing_targets == []

    analysis, _ = analyze_evm_blocks(blocks)
    assert len(analysis.loops) == 4
    assert analysis.back_edge_count == 4
