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
    analyze_x86_blocks,
    classify_evm_call_return_edge,
    classify_raw_jump_ops,
    classify_x86_call_return_edge,
    compute_idoms,
    count_backward_target_edges,
    evm_resolved_return_sites,
    find_natural_loops,
    is_evm_tag_header,
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
# back_edge_filter：把回边排除出 loop 检测（图算法层）
# ---------------------------------------------------------------------------

def test_back_edge_filter_defaults_to_keeping_everything():
    succs = {0: [1], 1: [2, 3], 2: [1], 3: []}
    default = find_natural_loops(succs, entry=0)
    explicit = find_natural_loops(succs, entry=0, back_edge_filter=lambda l, h: True)
    assert default.loops == explicit.loops
    assert default.excluded_back_edges == () == explicit.excluded_back_edges


def test_back_edge_filter_drops_loop_but_keeps_irreducible_verdict():
    """排除只作用于 loop 构造：``irreducible`` 口径必须逐字不变。

    被判掉的边照旧算回边、照旧不进 forward 子图，否则"少了一个 natural loop"
    会被误报成"多了一个不可归约残环"。
    """
    succs = {0: [1], 1: [2, 3], 2: [1], 3: []}
    analysis = find_natural_loops(succs, entry=0, back_edge_filter=lambda l, h: False)
    assert analysis.loops == ()
    assert analysis.excluded_back_edges == ((2, 1),)
    assert not analysis.irreducible


def test_back_edge_filter_partial_exclusion_shrinks_body():
    """同一 header 上只排除部分 latch 时，循环保留、body 相应缩小。"""
    succs = {0: [1], 1: [2, 3], 2: [1], 3: [1, 4], 4: []}
    analysis = find_natural_loops(
        succs, entry=0, back_edge_filter=lambda latch, header: latch != 2
    )
    assert len(analysis.loops) == 1
    loop = analysis.loops[0]
    assert loop.back_edges == ((3, 1),)
    assert loop.body == frozenset({1, 3})
    assert analysis.excluded_back_edges == ((2, 1),)


# ---------------------------------------------------------------------------
# EVM CFG 构建层
# ---------------------------------------------------------------------------

def _block(pc, ops, stack_depth=0):
    block = EVMBlock(
        pc=pc, stack_depth=stack_depth, min_depth=0, max_depth=1024, static_gas=0,
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
# 按形态疑似 internal-call/return 的回边识别（EVM 侧，§6）
#
# 全部用小合成 CFG，形态照抄 CErc20 实测：
# - 调用边      ← 0x32b7 那组（PUSH 返回标签 + 静态 JUMP 到 callee + 非零帧 delta）
# - 单目标返回边 ← 0x1a49 → 0x7c7（immediate_set 恰好一个目标）
# - 多目标返回边 ← 0xb39 自环（immediate_set 21 个目标，属过近似，**不排除**）
# ---------------------------------------------------------------------------

def _call_edge_program(stack_depth=2, pushed_tag=20):
    """共享子例程 100 被调用两次：0 调一次，返回站点 10 再调一次。

    返回站点 10 → 100 这条边被支配分析判成回边，实际是第二次调用。
    """
    return [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate=100, is_static=True)]),
        _block(10, [EvmOperator(kind="PUSH", pc=10, immediate=pushed_tag),
                    EvmOperator(kind="JUMP", pc=11, immediate=100, is_static=True)],
               stack_depth=stack_depth),
        _block(20, [EvmOperator(kind="STOP", pc=20)]),
        _block(100, [EvmOperator(kind="JUMP", pc=100, immediate=200, is_static=True)]),
        # 子例程返回跳：目标集就是两个返回站点，令 10/20 成为 resolved 返回站点
        _block(200, [EvmOperator(kind="JUMP", pc=200, immediate_set=[10, 20])],
               stack_depth=-2),
    ]


def _real_loop_program():
    """真实 for 循环：header 做条件判断，latch 无条件跳回、同帧、无返回标签。"""
    return [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate=10, is_static=True)]),
        _block(10, [EvmOperator(kind="JUMPI", pc=10, immediate=30, is_static=True)]),
        _block(20, [EvmOperator(kind="PUSH", pc=20, immediate=1),
                    EvmOperator(kind="JUMP", pc=21, immediate=10, is_static=True)]),
        _block(30, [EvmOperator(kind="STOP", pc=30)]),
    ]


def test_evm_resolved_return_sites_comes_from_immediate_set():
    blocks = _call_edge_program()
    assert evm_resolved_return_sites(blocks) == frozenset({10, 20})


def test_evm_call_edge_is_call_return_shaped():
    blocks = _call_edge_program()
    latch = next(b for b in blocks if b.pc == 10)
    sites = evm_resolved_return_sites(blocks)
    assert classify_evm_call_return_edge(latch, header=100, return_sites=sites) == "call"


def test_evm_call_edge_needs_nonzero_stack_frame_delta():
    """帧 delta 为 0 = 回到同一个栈帧 = 循环回边的形态，不排除。"""
    blocks = _call_edge_program(stack_depth=0)
    latch = next(b for b in blocks if b.pc == 10)
    sites = evm_resolved_return_sites(blocks)
    assert classify_evm_call_return_edge(latch, header=100, return_sites=sites) is None


def test_evm_call_edge_needs_a_resolved_return_tag():
    """PUSH 的是普通常量（不是任何已解析返回站点）⇒ 不是调用边。"""
    blocks = _call_edge_program(pushed_tag=1)
    latch = next(b for b in blocks if b.pc == 10)
    sites = evm_resolved_return_sites(blocks)
    assert 1 not in sites
    assert classify_evm_call_return_edge(latch, header=100, return_sites=sites) is None


def test_evm_real_loop_latch_is_not_call_return_shaped():
    blocks = _real_loop_program()
    latch = next(b for b in blocks if b.pc == 20)
    sites = evm_resolved_return_sites(blocks)
    assert classify_evm_call_return_edge(latch, header=10, return_sites=sites) is None


def test_evm_single_target_return_edge_is_call_return_shaped():
    """`JUMP immediate_set` 精确解析到唯一目标 ⇒ 这条边就是某次调用的返回腿。"""
    blocks = [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate=100, is_static=True)]),
        _block(100, [EvmOperator(kind="JUMP", pc=100, immediate=200, is_static=True)]),
        _block(200, [EvmOperator(kind="JUMP", pc=200, immediate_set=[100])],
               stack_depth=-3),
    ]
    latch = next(b for b in blocks if b.pc == 200)
    sites = evm_resolved_return_sites(blocks)
    assert classify_evm_call_return_edge(latch, header=100, return_sites=sites) == "return"

    analysis, _ = analyze_evm_blocks(blocks)
    assert [l.header for l in analysis.loops] == [100]
    excluded, _ = analyze_evm_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert excluded.loops == ()


def test_evm_multi_target_return_edge_is_kept():
    """目标集 ≥2 是跨调用点的并集过近似，单条边不对应确定的调用/返回配对。

    形态取自 CErc20 0xb39 / Safe 0x10bb 的自环：返回块的 immediate_set 里含它
    自己。这类边保守保留——排除判据只吃"已精确解析"的返回腿。
    """
    blocks = [
        _block(0, [EvmOperator(kind="JUMP", pc=0, immediate=100, is_static=True)]),
        _block(100, [EvmOperator(kind="JUMP", pc=100, immediate_set=[100, 200])],
               stack_depth=-4),
        _block(200, [EvmOperator(kind="STOP", pc=200)]),
    ]
    latch = next(b for b in blocks if b.pc == 100)
    sites = evm_resolved_return_sites(blocks)
    assert classify_evm_call_return_edge(latch, header=100, return_sites=sites) is None

    analysis, _ = analyze_evm_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert [l.header for l in analysis.loops] == [100]
    assert analysis.excluded_back_edges == ()


def test_analyze_evm_blocks_default_keeps_call_return_edges():
    """默认语义必须原样：开关关着时调用边照旧算 natural loop。"""
    blocks = _call_edge_program()
    analysis, _ = analyze_evm_blocks(blocks)
    assert [l.header for l in analysis.loops] == [100]
    assert analysis.excluded_back_edges == ()


def test_analyze_evm_blocks_excludes_call_edge_when_enabled():
    blocks = _call_edge_program()
    analysis, _ = analyze_evm_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert analysis.loops == ()
    assert analysis.excluded_back_edges == ((10, 100),)


def test_analyze_evm_blocks_keeps_real_loop_when_enabled():
    blocks = _real_loop_program()
    analysis, _ = analyze_evm_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert [l.header for l in analysis.loops] == [10]
    assert analysis.excluded_back_edges == ()


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
# 按形态疑似 internal-call/return 的回边识别（x86 侧，§6）
#
# 用真机器码而非手搓 X86Instruction：``parse_operands`` 依赖 Capstone 操作数结构，
# 判据里的正则也依赖 Capstone 的 op_str 排版，伪造对象两者都测不到。
# 下面每段字节序列都照抄 CErc20 实测形态（见各测试 docstring）。
# ---------------------------------------------------------------------------

def _le32(value):
    return (value & 0xFFFFFFFF).to_bytes(4, "little").hex()


# 定长指令：(字节数, emit(下一条指令地址, 标签表) -> hex)
_MOV_RAX_GAS = (4, lambda nxt, lab: "498b4570")      # mov rax, qword ptr [r13+0x70]
_MOV_GAS_RAX = (4, lambda nxt, lab: "49894570")      # mov qword ptr [r13+0x70], rax
_MOV_RAX_DEPTH = (4, lambda nxt, lab: "498b4530")    # mov rax, qword ptr [r13+0x30]
_MOV_RAX_MEMSIZE = (4, lambda nxt, lab: "498b4518")  # mov rax, qword ptr [r13+0x18]
_ADD_FRAME_RCX = (4, lambda nxt, lab: "49014d30")    # add qword ptr [r13+0x30], rcx
_LOAD_RETURN_PC = (4, lambda nxt, lab: "498b4680")   # mov rax, qword ptr [r14-0x80]
_NOP5 = (5, lambda nxt, lab: "0f1f440000")           # nop dword ptr [rax+rax]
_UD2 = (2, lambda nxt, lab: "0f0b")


def _cmp_rax(imm):
    return (6, lambda nxt, lab: "483d" + _le32(imm))


def _sub_rax(imm):
    return (6, lambda nxt, lab: "482d" + _le32(imm))


def _mov_rcx(imm):
    return (7, lambda nxt, lab: "48c7c1" + _le32(imm))


def _jb(label):
    return (6, lambda nxt, lab: "0f82" + _le32(lab[label] - nxt))


def _je(label):
    return (6, lambda nxt, lab: "0f84" + _le32(lab[label] - nxt))


def _jmp(label):
    return (5, lambda nxt, lab: "e9" + _le32(lab[label] - nxt))


def _x86_blocks(items):
    """两遍汇编 + 反汇编 + 分块。``items`` 里的 str 元素定义标签。"""
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex

    labels, addr = {}, 0
    for item in items:
        if isinstance(item, str):
            labels[item] = addr
        else:
            addr += item[0]
    out, addr = [], 0
    for item in items:
        if isinstance(item, str):
            continue
        size, emit = item
        addr += size
        out.append(emit(addr, labels))
    return identify_basic_blocks(disassemble_hex("".join(out), base_addr=0))


def _tag_prologue(static_gas=0x14, min_depth=0):
    """compileEVMTag 的前两节：gas 检查 + 扣 gas/栈深检查。

    ``identify_basic_blocks`` 会在 gas 检查的 ``jb`` 处切断，于是这 8 条指令
    横跨两个块——``is_evm_tag_header`` 必须跨块才认得出来。
    """
    return [
        _MOV_RAX_GAS, _cmp_rax(static_gas), _jb("oog"),
        _sub_rax(static_gas), _MOV_GAS_RAX, _MOV_RAX_DEPTH,
        _cmp_rax(min_depth), _jb("underflow"),
    ]


def _gas_only_prologue(static_gas=0x14):
    """只有 ``makeStaticUseGas`` 的公共前缀：扣完 gas 直接算内存扩展。

    这正是 ``checkMemoryAndCalcDynamicGas*`` 的形状——与 TAG 序言共享前三条，
    但 fallthrough 里读的是 memory_size 而不是 stackBasePointerInBytes。
    """
    return [
        _MOV_RAX_GAS, _cmp_rax(static_gas), _jb("oog"),
        _sub_rax(static_gas), _MOV_GAS_RAX, _MOV_RAX_MEMSIZE,
        _cmp_rax(0x20), _jb("oog"),
    ]


def _x86_call_edge_program(delta=0x40, tag_header=True):
    """调用边形态（CErc20 0xad63d 组）：``mov rcx, delta; add [r13+0x30], rcx; jmp header``。"""
    return _x86_blocks([
        "header", *(_tag_prologue() if tag_header else _gas_only_prologue()),
        "latch", _mov_rcx(delta), _ADD_FRAME_RCX, _jmp("header"),
        "oog", _UD2,
        "underflow", _UD2,
    ])


def _x86_return_edge_program(first_insn=_LOAD_RETURN_PC):
    """返回派发形态（CErc20 0x514fc → 0x12bca）：装载返回 pc + cmp + je header。"""
    return _x86_blocks([
        "header", *_tag_prologue(),
        "mid", _jmp("latch"),
        "latch", first_insn, _cmp_rax(0x7c7), _je("header"),
        "oog", _UD2,
        "underflow", _UD2,
    ])


def _only_back_edge(blocks):
    analysis, _ = analyze_x86_blocks(blocks)
    assert len(analysis.loops) == 1, [hex(l.header) for l in analysis.loops]
    loop = analysis.loops[0]
    assert len(loop.back_edges) == 1
    return loop.back_edges[0]


def _classify(blocks, latch, header):
    by_addr = {b.start_addr: b for b in blocks}
    return classify_x86_call_return_edge(by_addr[latch], header, by_addr)


# ---------------------------------------------------------------------------
# TAG 序言判别（Tier 1 / Tier 2 分层的唯一依据）
# ---------------------------------------------------------------------------

def _header_and_table(items):
    blocks = _x86_blocks(items)
    return blocks[0], {b.start_addr: b for b in blocks}


def test_static_use_gas_prefix_alone_is_not_a_tag_header():
    """只有 ``makeStaticUseGas`` 公共前缀的块**不是** EVM 块边界。

    ``mov TMP,[r13+gas]; cmp TMP,IMM; jb`` 是 makeStaticUseGas 的开头，动态 gas
    路径（``checkMemoryAndCalcDynamicGas*``）逐字生成同样三条。只认这三条会严重
    过匹配：CErc20 34445 个块里命中 1522、Safe 30869 个里命中 1264，而真实 EVM
    块只有 723 / 742。
    """
    header, table = _header_and_table([
        "header", *_gas_only_prologue(),
        _UD2,
        "oog", _UD2,
    ])
    # 前三条与真 TAG 序言逐字相同 —— 松判据在这里必然判 True
    assert [i.mnemonic for i in header.instructions] == ["mov", "cmp", "jb"]
    assert is_evm_tag_header(header, table) is False


def test_full_tag_prologue_spans_two_blocks_and_matches():
    """完整 compileEVMTag 序言（跨块）判 True。"""
    header, table = _header_and_table([
        "header", *_tag_prologue(static_gas=0x14),
        _UD2,
        "oog", _UD2,
        "underflow", _UD2,
    ])
    # 序言在 gas 检查的 jb 处被切断：判据拿不到块表就不可能认全
    assert len(header.instructions) == 3
    assert is_evm_tag_header(header, table) is True
    # 拿不到 fallthrough 上下文时 fail-closed 判 False，而不是退回松判据
    assert is_evm_tag_header(header, {header.start_addr: header}) is False


def test_tag_prologue_requires_matching_static_gas_immediate():
    """CMPQ 与 SUBQ 的 staticGas 必须同值——同一次 makeStaticUseGas 调用的两半。"""
    header, table = _header_and_table([
        "header", _MOV_RAX_GAS, _cmp_rax(0x14), _jb("oog"),
        _sub_rax(0x15), _MOV_GAS_RAX, _MOV_RAX_DEPTH, _cmp_rax(0), _jb("underflow"),
        _UD2,
        "oog", _UD2,
        "underflow", _UD2,
    ])
    assert is_evm_tag_header(header, table) is False


def test_x86_call_edge_is_call_return_shaped():
    blocks = _x86_call_edge_program(delta=0x40)
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) == "call"


def test_x86_call_edge_needs_nonzero_stack_frame_delta():
    """delta=0 是真实循环回边的形态（CErc20 0xbe03b / 0xbfa87 就是 ``mov rcx, 0``）。"""
    blocks = _x86_call_edge_program(delta=0)
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) is None


def test_x86_call_edge_needs_tag_header():
    """目标不是 EVM 块边界（只有 makeStaticUseGas 公共前缀）⇒ 保留。

    这一条也是 Tier 2 codegen 内生循环的护栏：它们的头没有完整 TAG 序言。
    """
    blocks = _x86_call_edge_program(delta=0x40, tag_header=False)
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) is None


def test_x86_single_link_return_chain_is_call_return_shaped():
    blocks = _x86_return_edge_program()
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) == "return"


def test_x86_multi_link_return_chain_is_kept():
    """链中节点只有 ``cmp/je``、不装载返回 pc ⇒ 目标集 ≥2 的过近似，保留。

    形态取自 CErc20 0x1e838（``nop; cmp rax, 0xb39; je 0x1e65b``）：它是 21 目标
    比较链的中间一节，前面的装载在别的块里。
    """
    blocks = _x86_return_edge_program(first_insn=_NOP5)
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) is None

    # 换成"有 mov 但不是 EVM 栈槽装载"同样保留（排除 r13 侧字段读的误判）
    blocks = _x86_return_edge_program(first_insn=_MOV_RAX_GAS)
    latch, header = _only_back_edge(blocks)
    assert _classify(blocks, latch, header) is None


def test_analyze_x86_blocks_default_keeps_call_return_edges():
    blocks = _x86_call_edge_program(delta=0x40)
    analysis, _ = analyze_x86_blocks(blocks)
    assert len(analysis.loops) == 1
    assert analysis.excluded_back_edges == ()


def test_analyze_x86_blocks_excludes_call_edge_when_enabled():
    blocks = _x86_call_edge_program(delta=0x40)
    analysis, _ = analyze_x86_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert analysis.loops == ()
    assert len(analysis.excluded_back_edges) == 1


def test_analyze_program_pair_flag_is_opt_in_and_symmetric():
    """默认不变；打开后两侧同时缩减，配对仍然成立。"""
    from verification.loop_pairing import analyze_program_pair

    evm_blocks = _call_edge_program()
    x86_blocks = _x86_call_edge_program(delta=0x40)

    default = analyze_program_pair(evm_blocks, x86_blocks)
    assert len(default.pairs) == 1
    assert default.call_return_shaped_evm_edges == ()
    assert default.call_return_shaped_x86_edges == ()

    excluded = analyze_program_pair(
        evm_blocks, x86_blocks, exclude_call_return_shaped_edges=True
    )
    assert excluded.pairs == []
    assert not excluded.unpaired_evm and not excluded.unpaired_x86
    assert excluded.ok
    assert len(excluded.call_return_shaped_evm_edges) == 1
    assert len(excluded.call_return_shaped_x86_edges) == 1
    assert any("call/return shaped" in note for note in excluded.notes())


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


@pytest.mark.slow
@pytest.mark.skipif(
    not (os.path.exists(_CERC20) and os.path.exists(_CERC20_HEX)),
    reason="CErc20 fixture missing",
)
def test_cerc20_call_return_shaped_exclusion():
    """§6 验收：CErc20 上排除后剩下的正是 §3.3 那 4 个按形态疑似真实循环。

    §3.3 把 9 个候选按形态分成两组；本用例锁死判据的落点：
    - 疑似 call/return 的 5 个头（0x7c7 / 0x32b7 / 0x333e / 0x35e7 / 0x3643）
      的回边全部排除；
    - 疑似真实循环的 4 个头（0x739 / 0xb39 / 0x36aa / 0x3731）一条不动。

    两侧独立判定却排除同样条数，是判据互为镜像的交叉证据；数不等时
    ``pair_natural_loops`` 会数量不等而全部不配对，守卫如实失败。
    """
    from evm_ir.json_parser import load_ir_from_json
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from x86_64.loop_templates import make_tier2_matcher
    from verification.loop_pairing import analyze_program_pair

    evm_blocks = load_ir_from_json(_CERC20).blocks
    x86_blocks = identify_basic_blocks(
        disassemble_hex(open(_CERC20_HEX).read().strip(), base_addr=0)
    )
    by_addr = {b.start_addr: b for b in x86_blocks}

    baseline = analyze_program_pair(
        evm_blocks, x86_blocks, tier2_matcher=make_tier2_matcher(by_addr),
    )
    assert [l.header for l in baseline.evm_analysis.loops] == [
        0x739, 0x7C7, 0xB39, 0x32B7, 0x333E, 0x35E7, 0x3643, 0x36AA, 0x3731
    ]
    assert len(baseline.pairs) == 9
    assert baseline.call_return_shaped_evm_edges == ()

    report = analyze_program_pair(
        evm_blocks, x86_blocks,
        tier2_matcher=make_tier2_matcher(by_addr),
        exclude_call_return_shaped_edges=True,
    )
    assert [l.header for l in report.evm_analysis.loops] == [
        0x739, 0xB39, 0x36AA, 0x3731
    ]
    excluded_headers = {h for _, h in report.call_return_shaped_evm_edges}
    assert excluded_headers == {0x7C7, 0x32B7, 0x333E, 0x35E7, 0x3643}
    # 5 个头共 1+6+2+1+4 = 14 条回边；两侧独立判定必须同数
    assert len(report.call_return_shaped_evm_edges) == 14
    assert len(report.call_return_shaped_x86_edges) == 14

    # 排除后仍 4↔4 全配对，守卫照旧通过
    assert len(report.pairs) == 4
    assert not report.unpaired_evm and not report.unpaired_x86
    assert report.ok


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

    # §3.3：Safe 的 4 个候选全部单 latch、body ≤ 2，无疑似 call/return 形态。
    # 判据在这里必须一条都不排除——它是"不误伤"方向的哨兵。
    excluded, _ = analyze_evm_blocks(blocks, exclude_call_return_shaped_edges=True)
    assert excluded.excluded_back_edges == ()
    assert [l.header for l in excluded.loops] == [l.header for l in analysis.loops]


_SAFE_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts", "safe", "Safe.hex",
)


@pytest.mark.slow
@pytest.mark.skipif(
    not (os.path.exists(_SAFE) and os.path.exists(_SAFE_HEX)),
    reason="Safe fixture missing",
)
def test_safe_call_return_shaped_exclusion_is_empty_on_both_sides():
    """Safe 上两侧都应识别出 0 条：判据不该对没有该形态的合约产生任何影响。"""
    from evm_ir.json_parser import load_ir_from_json
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from x86_64.loop_templates import make_tier2_matcher
    from verification.loop_pairing import analyze_program_pair

    evm_blocks = load_ir_from_json(_SAFE).blocks
    x86_blocks = identify_basic_blocks(
        disassemble_hex(open(_SAFE_HEX).read().strip(), base_addr=0)
    )
    by_addr = {b.start_addr: b for b in x86_blocks}

    report = analyze_program_pair(
        evm_blocks, x86_blocks,
        tier2_matcher=make_tier2_matcher(by_addr),
        exclude_call_return_shaped_edges=True,
    )
    assert report.call_return_shaped_evm_edges == ()
    assert report.call_return_shaped_x86_edges == ()
    assert len(report.pairs) == 4
    assert report.ok


@pytest.mark.slow
@pytest.mark.parametrize(
    "ir_path,hex_path,evm_block_count,tier1_headers",
    [
        (_CERC20, _CERC20_HEX, 723, 9),
        (_SAFE, _SAFE_HEX, 742, 4),
    ],
    ids=["cerc20", "safe"],
)
def test_tag_header_criterion_is_exact_on_real_contracts(
    ir_path, hex_path, evm_block_count, tier1_headers
):
    """收紧后的 TAG 序言判据在真实合约上与 EVM 块数**逐块相等**。

    两条断言各盯一件事：

    - 全块命中数 == IR ``control_frames`` 数。松判据（只看 gas 检查三条）在这里
      是 1522 / 1264，因为 ``makeStaticUseGas`` 的公共前缀被动态 gas 路径复用；
      补上 fallthrough 的栈深检查后正好落到 723 / 742。**入口块也要数进去**：
      它的 TAG 序言前面压着保留寄存器初始化，判据锚"块尾"才不会差 1。
    - Tier 1 循环头数 == 9 / 4，与收紧前一致。过匹配一直没造成分层错误，收紧
      是把"碰巧没错"变成"结构上不会错"；这个数变了就是实现 bug。
    """
    import json

    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex

    if not (os.path.exists(ir_path) and os.path.exists(hex_path)):
        pytest.skip("fixture missing")

    with open(ir_path, encoding="utf-8") as fh:
        assert len(json.load(fh)["control_frames"]) == evm_block_count

    x86_blocks = identify_basic_blocks(
        disassemble_hex(open(hex_path).read().strip(), base_addr=0)
    )
    by_addr = {b.start_addr: b for b in x86_blocks}

    assert sum(is_evm_tag_header(b, by_addr) for b in x86_blocks) == evm_block_count

    analysis, _ = analyze_x86_blocks(x86_blocks)
    tier1 = [
        loop for loop in analysis.loops
        if loop.header in by_addr and is_evm_tag_header(by_addr[loop.header], by_addr)
    ]
    assert len(tier1) == tier1_headers
