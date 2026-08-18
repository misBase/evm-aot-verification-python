#!/usr/bin/env python3
"""P3(ii)：Tier 2 模板逐指令精确匹配器（v2）单测。

正例锚点 = 真实 codegen 字节（CErc20 39 条循环 + CALLDATACOPY core）；
负例验证 fail-closed（改立即数 / 错误头地址均不得命中）。
"""

import os
from collections import Counter

import pytest

from verification.loop_pairing import analyze_x86_blocks
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.loop_templates import (
    PROVEN_TIER2_LEMMAS,
    TEMPLATES,
    make_tier2_matcher,
    match_body_blocks_exact,
)

_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)

# compileMakeDataCopy 真实产物（tests/integration/test_single_ins_equivalence.py
# 的 X86_CALLDATACOPY_CORE_HEX_SEQUENCE）；循环头 0x41，出口 0x71。
_CDC_HEX = (
    "498b76c048c7c000000000490b46c8490b46d0490b46d84885c0740748c7c6ffff"
    "ffff498b8d98000000498bbd90000000498b46a04d8b46e04839f173034889ce66"
    "904883f80172284883e8014889f24801c24839ca73060fb61c17eb0748c7c30000"
    "00004889c24c01c241881c17ebd041c685e00000000249c74528f4ffffffc3"
)


def _loops_with_bodies(hex_str):
    blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    by_addr = {b.start_addr: b for b in blocks}
    analysis, _ = analyze_x86_blocks(blocks)
    out = []
    for loop in analysis.loops:
        body = [by_addr[a] for a in sorted(loop.body) if a in by_addr]
        out.append((loop, body))
    return blocks, by_addr, out


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_cerc20_all_codegen_loops_match_exactly():
    """CErc20 全部 39 条 codegen 循环逐指令精确命中，按形态计数与实证一致。"""
    _, _, loops = _loops_with_bodies(open(_CERC20_HEX).read().strip())

    names = []
    for loop, body in loops:
        m = match_body_blocks_exact(body, loop.header)
        if m is not None:
            names.append(m[0])
    counts = Counter(names)
    # v1 特征匹配把 34 条统称 byte-copy；精确匹配区分出 6 条
    # MakeDataCopy（CALLDATACOPY/CODECOPY，带越界补 0 分支）
    assert counts == {
        "returndata-byte-copy": 28,
        "makedata-byte-copy": 6,
        "mcopy-low-word": 1,
        "mcopy-high-word": 1,
        "mcopy-byte-tail": 2,
        "mcopy-shr-align": 1,
    }


def test_makedata_loop_matches_exactly():
    _, _, loops = _loops_with_bodies(_CDC_HEX)
    assert len(loops) == 1
    loop, body = loops[0]
    m = match_body_blocks_exact(body, loop.header)
    assert m is not None
    name, binding = m
    assert name == "makedata-byte-copy"
    # 寄存器角色（compileMakeDataCopy 的 allocateRegisters 结果）
    assert binding["S"] == "rax"
    assert binding["OFF"] == "rsi"
    assert binding["LEN"] == "rcx"
    assert binding["INP"] == "rdi"
    assert binding["DST"] == "r8"


def test_perturbed_immediate_fails_closed():
    """步进立即数 1→2（语义变化）后模板不得命中。"""
    perturbed = _CDC_HEX.replace("4883e801", "4883e802")
    assert perturbed != _CDC_HEX
    _, _, loops = _loops_with_bodies(perturbed)
    assert len(loops) == 1
    loop, body = loops[0]
    assert match_body_blocks_exact(body, loop.header) is None


def test_wrong_header_fails_closed():
    """头地址不落在 (nop 容忍的) 循环头上 ⇒ 不命中。

    注意 +2 会落在头部 2 字节 nop 之后的首条真指令上——那是合法的
    等价入口（codegen NOP 头容忍），因此取 +8（循环体中部）作负例。"""
    _, _, loops = _loops_with_bodies(_CDC_HEX)
    loop, body = loops[0]
    assert match_body_blocks_exact(body, loop.header + 8) is None


def test_registry_matches_template_table():
    """注册表与模板表一致；每个键都有离线证明
    （tests/integration/test_tier2_lemmas.py 固化）。"""
    assert PROVEN_TIER2_LEMMAS == frozenset(TEMPLATES)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_strict_matcher_accepts_all_cerc20_loops():
    """fail-closed 匹配器（默认模式）放行全部 39 条已证模板循环。"""
    _, by_addr, loops = _loops_with_bodies(open(_CERC20_HEX).read().strip())
    matcher = make_tier2_matcher(by_addr)
    assert sum(1 for loop, _ in loops if matcher(loop)) == 39
