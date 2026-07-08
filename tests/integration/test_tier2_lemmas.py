#!/usr/bin/env python3
"""P3(ii)：Tier 2 模板引理离线证明固化（docs/循环处理增强方案.md §5）。

七条回边（六种形态）逐条在**真实 codegen 字节**上证明 ①②③，外加
FromLow/FromHigh 构造级复合（glue 段实跑 + 复合恒等式）。这组测试是
`PROVEN_TIER2_LEMMAS` 注册表的证明依据：任何一条失败即注册表过期
（codegen 变更时精确匹配同时失效，运行时守卫 fail-closed）。

证明锚点：
- CErc20 fixture：returndata(0x1590f)、MCOPY 五连簇(0xad254 起)
- CALLDATACOPY core（compileMakeDataCopy，单指令测试同款 hex）
"""

import os

import pytest

from verification import tier2_lemmas as t2
from verification.loop_pairing import analyze_x86_blocks
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.loop_templates import PROVEN_TIER2_LEMMAS, TEMPLATES

_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)

# compileMakeDataCopy 真实产物（test_single_ins_refinement.py 的
# X86_CALLDATACOPY_CORE_HEX_SEQUENCE）；循环头 0x41。
_CDC_HEX = (
    "498b76c048c7c000000000490b46c8490b46d0490b46d84885c0740748c7c6ffff"
    "ffff498b8d98000000498bbd90000000498b46a04d8b46e04839f173034889ce66"
    "904883f80172284883e8014889f24801c24839ca73060fb61c17eb0748c7c30000"
    "00004889c24c01c241881c17ebd041c685e00000000249c74528f4ffffffc3"
)

# CErc20 MCOPY 五连簇的构造内地址（唯一一处 MCOPY，0xad21d 起）
_MCOPY_HIGH_WORD = 0xAD254
_MCOPY_HIGH_PREAMBLE = 0xAD23D
_MCOPY_SHR = 0xAD284
_MCOPY_HIGH_TAIL = 0xAD294
_MCOPY_LOW_WORD = 0xAD2AC
_MCOPY_LOW_TAIL = 0xAD2CF
_RETURNDATA_LOOP = 0x1590F

pytestmark = pytest.mark.skipif(
    not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing"
)


@pytest.fixture(scope="module")
def cerc20():
    hex_str = open(_CERC20_HEX).read().strip()
    blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    by_addr = {b.start_addr: b for b in blocks}
    analysis, _ = analyze_x86_blocks(blocks)
    loops = {l.header: l for l in analysis.loops}
    return blocks, by_addr, loops


def _bind(by_addr, loops, header, expect_name):
    body = [by_addr[a] for a in sorted(loops[header].body) if a in by_addr]
    m = t2.match_body_blocks_exact(body, header)
    assert m is not None, f"no exact match at {hex(header)}"
    name, binding = m
    assert name == expect_name, (name, expect_name)
    return binding


def _assert_proved(result):
    assert result.proved, (
        f"{result.name} not proved: {result.reasons}\n"
        + "\n".join(f"  {q}: {v}" for q, v in result.queries)
    )
    # 所有查询必须真 unsat（防 vacuous：查询列表非空）
    assert result.queries


def test_lemma_shr_align(cerc20):
    blocks, by_addr, loops = cerc20
    b = _bind(by_addr, loops, _MCOPY_SHR, "mcopy-shr-align")
    _assert_proved(t2.prove_shr_align(blocks, _MCOPY_SHR, b["@EXIT"], b))


@pytest.mark.parametrize("header", [_MCOPY_HIGH_TAIL, _MCOPY_LOW_TAIL])
def test_lemma_byte_tail(cerc20, header):
    """byte-tail 形态出现在 FromHigh/FromLow 两条回边，逐实例证明。"""
    blocks, by_addr, loops = cerc20
    b = _bind(by_addr, loops, header, "mcopy-byte-tail")
    _assert_proved(t2.prove_byte_tail(blocks, header, b["@EXIT"], b))


def test_lemma_low_word(cerc20):
    blocks, by_addr, loops = cerc20
    b = _bind(by_addr, loops, _MCOPY_LOW_WORD, "mcopy-low-word")
    _assert_proved(
        t2.prove_low_word(blocks, _MCOPY_LOW_WORD, b["@EXIT"], b["@TAIL"], b)
    )


def test_lemma_high_word(cerc20):
    blocks, by_addr, loops = cerc20
    b = _bind(by_addr, loops, _MCOPY_HIGH_WORD, "mcopy-high-word")
    _assert_proved(
        t2.prove_high_word(blocks, _MCOPY_HIGH_WORD, b["@EXIT"], b["@EXIT2"], b)
    )


def test_lemma_returndata_byte_copy(cerc20):
    blocks, by_addr, loops = cerc20
    b = _bind(by_addr, loops, _RETURNDATA_LOOP, "returndata-byte-copy")
    _assert_proved(
        t2.prove_returndata_byte_copy(blocks, _RETURNDATA_LOOP, b["@EXIT"], b)
    )


def test_lemma_makedata_byte_copy():
    blocks = identify_basic_blocks(disassemble_hex(_CDC_HEX, base_addr=0))
    by_addr = {b.start_addr: b for b in blocks}
    analysis, _ = analyze_x86_blocks(blocks)
    loops = {l.header: l for l in analysis.loops}
    assert list(loops) == [0x41]
    b = _bind(by_addr, loops, 0x41, "makedata-byte-copy")
    _assert_proved(t2.prove_makedata_byte_copy(blocks, 0x41, b["@EXIT"], b))


def test_mcopy_low_composition(cerc20):
    """FromLow 两段复合：word-jl 出口 → glue 载入跨界 qword → tail 基例
    + 满覆盖恒等式 == MCOPY 闭式。"""
    blocks, by_addr, loops = cerc20
    b_word = _bind(by_addr, loops, _MCOPY_LOW_WORD, "mcopy-low-word")
    b_tail = _bind(by_addr, loops, _MCOPY_LOW_TAIL, "mcopy-byte-tail")
    _assert_proved(
        t2.prove_mcopy_low_composition(
            blocks, b_word["@TAIL"], _MCOPY_LOW_TAIL, b_word, b_tail,
        )
    )


def test_mcopy_high_composition(cerc20):
    """FromHigh 三段复合（§5.1）：preamble 基例 → word-jl 出口 → glue
    （dst 回退 + 跨界 qword + 移位计数）→ SHR → tail 满覆盖恒等式。"""
    blocks, by_addr, loops = cerc20
    b_word = _bind(by_addr, loops, _MCOPY_HIGH_WORD, "mcopy-high-word")
    b_shr = _bind(by_addr, loops, _MCOPY_SHR, "mcopy-shr-align")
    b_tail = _bind(by_addr, loops, _MCOPY_HIGH_TAIL, "mcopy-byte-tail")
    _assert_proved(
        t2.prove_mcopy_high_composition(
            blocks, _MCOPY_HIGH_PREAMBLE, _MCOPY_HIGH_WORD,
            b_word["@EXIT2"], _MCOPY_SHR, _MCOPY_HIGH_TAIL,
            b_word, b_shr, b_tail,
        )
    )


def test_registry_is_backed_by_proofs():
    """注册表键 == 模板表键 == 本文件证明覆盖的六种形态。"""
    assert PROVEN_TIER2_LEMMAS == frozenset(TEMPLATES)
    assert frozenset(TEMPLATES) == {
        "returndata-byte-copy", "makedata-byte-copy",
        "mcopy-low-word", "mcopy-high-word",
        "mcopy-byte-tail", "mcopy-shr-align",
    }
