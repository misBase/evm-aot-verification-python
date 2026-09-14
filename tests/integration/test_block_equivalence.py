"""阶段 3 验收：muti_block 上的逐块 lock-step 等价证明。

docs/块级lockstep等价验证方案.md §6 阶段 3 —— 在小 fixture 上跑通 ②③④ 四条
义务，验收标准是 40 块全部 proved。

本文件同时是两个**实现修正**的回归（两处方案原文写错，PoC 暴露）：

- **entry 块的 x86 区间从程序起点开始**，而不是从第一个 TAG 开始。保留寄存器
  序言执行必经、与第一个 TAG 同属一个 basic block，剔除它会让 entry 入口落在
  块中间（`Entry block not found`）。
- **`R` 在块出口与入口不是同一组义务**（`site="exit"`）：x86 块内不维护 R14 与
  `[R13+0x30]` 的同步，R14 由后继块的 TAG 序言重建。不做区分，每个有净栈效应
  的块都会假失败。
"""

import pytest

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from tools.tag_align import build_block_alignment
from verification.block_equivalence import BlockEquivalenceProver
from verification.block_specialization import BlockSpecialization
from x86_64.cfg import identify_basic_blocks
from x86_64.program import X86Program

# muti_block 的入口内存态：MSize 与 free pointer 的静态推断值。
MSIZE, FMP = 0x60, 0x80
BASE_ADDR = 0x1000


@pytest.fixture(scope="module")
def program():
    evm = sorted(
        EVMProgram(load_ir_from_json("tests/data/muti_block.json")).blocks,
        key=lambda b: b.pc,
    )
    with open("tests/data/muti_block.hex") as fh:
        x86p = X86Program.from_hex(fh.read().strip(), base_addr=BASE_ADDR)
    basic_blocks = identify_basic_blocks(x86p.instructions)
    alignment = build_block_alignment(evm, x86p.instructions, basic_blocks)
    return evm, x86p, basic_blocks, alignment


@pytest.fixture(scope="module")
def pc_to_addr(program):
    """把 entry 块的起点前移到程序起点（含保留寄存器序言）。

    `BlockAlignment` 把序言登记为 `non_block_regions`——那是 ④(b) 的记账口径
    （每条指令恰属于一个区间）。但**执行**口径不同：序言是 entry 块的前缀，
    段执行必须从它开始。两个口径都对，转换点在这里。
    """
    evm, x86p, _bb, alignment = program
    mapping = dict(alignment.pc_to_addr)
    entry_pc = evm[0].pc
    program_start = x86p.instructions[0].addr
    if any(start <= program_start < end for start, end in
           alignment.non_block_regions):
        mapping[entry_pc] = program_start
    return mapping


def test_alignment_is_one_to_one(program):
    evm, _x86p, _bb, alignment = program
    assert len(alignment) == len(evm) == 40


def test_reserved_register_prologue_is_registered_not_dropped(program):
    """④(b)：序言必须被显式登记，"落在所有区间外"是 fail-closed 的缺陷形态。"""
    _evm, _x86p, _bb, alignment = program
    assert alignment.non_block_regions, "保留寄存器序言未被登记"


def test_every_block_is_proved(program, pc_to_addr):
    """阶段 3 验收：40 块全部 proved。"""
    evm, _x86p, basic_blocks, _alignment = program
    prover = BlockEquivalenceProver(
        evm, basic_blocks, pc_to_addr, timeout_ms=30_000
    )
    failures = []
    for block in evm:
        spec = BlockSpecialization(block.pc, block.min_depth, MSIZE, FMP)
        result = prover.prove(spec)
        if not result.proved:
            failures.append(
                (block.pc, result.reasons + result.control_flow_defects)
            )
    assert not failures, f"{len(failures)}/{len(evm)} 块未证出: {failures[:3]}"


def test_block_with_net_stack_effect_is_proved(program, pc_to_addr):
    """pc=13 是 dispatcher，净栈效应非零、x86 侧 98 条路径。

    它是 `site="exit"` 修正的直接回归：用 entry 口径求出口义务时，这里的 97 条
    转移会全部卡在 `stack_geometry`（R14 尚未被后继 TAG 重建）。
    """
    evm, _x86p, basic_blocks, _alignment = program
    prover = BlockEquivalenceProver(
        evm, basic_blocks, pc_to_addr, timeout_ms=30_000
    )
    result = prover.prove(BlockSpecialization(13, 0, MSIZE, FMP))
    assert result.proved, result.reasons + result.control_flow_defects
    assert result.transitions_proved > 1, "该块应有多条转移出边"


def test_unmapped_block_is_rejected(program, pc_to_addr):
    """块不在权威映射里时必须 inconclusive，不得凭顺序猜一个地址。"""
    evm, _x86p, basic_blocks, _alignment = program
    prover = BlockEquivalenceProver(evm, basic_blocks, pc_to_addr)
    result = prover.prove(BlockSpecialization(0xDEAD, 0, MSIZE, FMP))
    assert not result.proved
    assert "authoritative mapping" in result.reasons[0]
