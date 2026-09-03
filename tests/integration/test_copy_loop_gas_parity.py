"""Tier 2 copy-loop summary 的 gas 中立性:开关两档结论必须逐字相同。

## 这条测试守的是什么

copy-loop summary 把整个拷贝循环替换成闭式内存变换、直接跳到 continuation。
它这么做的**前提**是:这四条 opcode 的 gas 全部在循环**之外**扣完,循环体内
一条 gas 指令都没有——所以跳过循环体不会让两侧 gas 账本分叉。

依据(x86 侧,go-hpc-evm `evm/aot/impl_amd64.go`):

- `compileEVMCALLDATACOPY` 先 `checkMemoryAndCalcDynamicGasCallDataCopy()`,
  再 `compileMakeDataCopy(...)` 发拷贝循环;CODECOPY 走同一个 `compileMakeDataCopy`
- `compileEVMRETURNDATACOPY` 函数第一句就是 gas 前言
- `compileEVMMCOPY` 第一句 `checkMemoryAndCalcDynamicGasMCopy()`,之后才 pop
  操作数、dispatch 到 FromHigh/FromLow
- gas 前言自身没有回边(`makeCalcCopyIns` → `makeCalcMemSize64` → `makeSafeMul`
  → `compileMemoryCopierGasN` → `makeUseGas`,全是前向分支)
- FromHigh 整个 cluster(preamble/align/word/glue/shr/tail)零 gas 指令——
  **一次 `[r13+...]` 访问都没有**

依据(EVM IR 侧,develop):`evm_ir/semantics.py` 四条 opcode 都是先
`charge_memory_and_word_gas` / `charge_mcopy_gas`,再写内存。

**这个结论是 summary 安全性的地基,但它是对当前 codegen 的观察,不是定理。**
若将来编译器把某段 gas 挪进循环体,本测试会立刻红——那正是它存在的理由。
单元测试压不出这个:只有端到端跑一遍 gas 一致性检查才看得到 gas 终值。
"""

import os

import pytest

from evm_ir.json_parser import load_ir_from_json
from evm_ir.program import EVMProgram
from state.smt_state import SMTState
from verification.program_verifier import GasCheck, ProgramEquivalenceChecker
from x86_64.program import X86Program
from x86_64.summaries.registry import (
    TRUSTED_SUMMARY_CONFIG,
    TRUSTED_SUMMARY_CONFIG_WITH_TIER2,
)


def _load_pair(name: str):
    test_dir = os.path.dirname(__file__)
    ir_path = os.path.join(test_dir, "..", "data", f"{name}.json")
    hex_path = os.path.join(test_dir, "..", "data", f"{name}.hex")
    evm_program = EVMProgram(load_ir_from_json(ir_path))
    x86_program = X86Program.from_hex(
        open(hex_path, encoding="utf-8").read().strip(), base_addr=0
    )
    return evm_program, x86_program


def _verify(name: str, summary_config, **kwargs):
    evm_program, x86_program = _load_pair(name)
    checker = ProgramEquivalenceChecker(
        timeout_ms=180000, gas_check=GasCheck.FIXED_BUDGET
    )
    initial_state = SMTState.create_initial_state(**kwargs)
    return checker.verify_program_pair(
        evm_program,
        x86_program,
        initial_state,
        stack_check=None,
        summary_config=summary_config,
    )


# RETURNDATACOPY 需要非零 return-data size 才走正常路径(默认 0 会走越界分支)
_EXTRA_STATE = {"gas_returndatacopy": {"return_data_size_bytes": 0x100}}


@pytest.mark.parametrize(
    "fixture",
    ["gas_calldatacopy", "gas_codecopy", "gas_returndatacopy", "gas_mcopy"],
)
def test_copy_loop_summary_is_gas_neutral(fixture):
    """开/关 copy-loop 折叠,gas 一致性结论必须相同。

    两档都应 VERIFIED。若折叠让 gas 分叉,开启档会给出 gas 反例而关闭档不会
    ——那正是"gas 被挪进循环体"的信号。
    """
    extra = _EXTRA_STATE.get(fixture, {})

    off_verified, off_msg = _verify(fixture, TRUSTED_SUMMARY_CONFIG, **extra)
    on_verified, on_msg = _verify(
        fixture, TRUSTED_SUMMARY_CONFIG_WITH_TIER2, **extra
    )

    assert off_verified, f"{fixture}: baseline (copy_loop off) failed: {off_msg}"
    assert on_verified, (
        f"{fixture}: copy_loop 折叠后 gas 一致性失败——很可能有 gas 被挪进了"
        f"循环体,summary 跳过循环体就会让两侧账本分叉。detail: {on_msg}"
    )


def test_copy_loop_summary_actually_fires_on_a_copy_fixture():
    """防 vacuous:上面那条要有意义,summary 必须真的命中过。

    若 discovery 一个都没匹配上,两档结论当然相同——那时测试什么也没验到。
    """
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from x86_64.summaries.base import SummaryDiscoveryContext
    from x86_64.summaries.copy_loop import discover_copy_loop_summaries

    test_dir = os.path.dirname(__file__)
    hex_path = os.path.join(test_dir, "..", "data", "gas_calldatacopy.hex")
    blocks = identify_basic_blocks(
        disassemble_hex(open(hex_path, encoding="utf-8").read().strip(), base_addr=0)
    )
    ctx = SummaryDiscoveryContext(
        blocks=blocks,
        blocks_by_addr={b.start_addr: b for b in blocks},
        block_index={b.start_addr: i for i, b in enumerate(blocks)},
    )
    summaries = list(discover_copy_loop_summaries(ctx))

    assert summaries, "gas_calldatacopy 上没有发现任何 copy-loop summary"
    assert any(
        s.payload.template == "makedata-byte-copy" for s in summaries
    ), f"期望 makedata-byte-copy 模板,实得 {[s.payload.template for s in summaries]}"
