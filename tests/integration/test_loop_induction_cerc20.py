#!/usr/bin/env python3
"""P2 验收基准：Compound CErc20 string 存储循环的 Tier 1 锁步归纳。

目标循环（docs/循环处理增强方案.md §7 验收基准）：
- EVM pc=0x739：`DUP SLOAD DUP MSTORE SWAP PUSH ADD SWAP PUSH ADD DUP DUP
  GT JUMPI` 单块自环——name/symbol getter 的动态 string 存储读循环，
  trip count = ceil(len/32)，len 为符号值（有界展开永远无法封闭）。
- x86 0x107a2：对应编译产物（TAG 序言 + SLOAD host 桥 + 内存扩展逻辑
  + MSTORE bswap 写 + 4-limb GT 比较链，28 个基本块）。

归纳步 ② 在 havoc 后的循环头 cutpoint 上证明：任意第 n 轮到达时若 R
成立，则一轮之后 R 保持（回边/出口），分支决策两侧一致——**符号 bound
被归纳吞掉，不调 max_depth**。

结论携带 no-OOG/no-stack-limit envelope 标注（§4.3：现有全程序抽象的
显式化，OOG 错误终止路径被排除并逐条记录）。

**运行方式（显式 opt-in）**：本测试实测约 8–9 分钟（约 170 条 Z3 查询，
单条 budget 120s），默认 skip 以免拖垮常规 pytest/CI::

    RUN_LOOP_INDUCTION_ACCEPTANCE=1 poetry run pytest \
        tests/integration/test_loop_induction_cerc20.py
"""

import os

import pytest

_CERC20_JSON = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.json",
)
_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)

pytestmark = [
    pytest.mark.skipif(
        not os.environ.get("RUN_LOOP_INDUCTION_ACCEPTANCE"),
        reason=(
            "~9 min acceptance run; set RUN_LOOP_INDUCTION_ACCEPTANCE=1 "
            "to enable"
        ),
    ),
    pytest.mark.skipif(
        not (os.path.exists(_CERC20_JSON) and os.path.exists(_CERC20_HEX)),
        reason="CErc20 fixture missing",
    ),
]


def _loop_exits(loop, succs):
    out = set()
    for node in loop.body:
        for target in succs.get(node, []):
            if target not in loop.body:
                out.add(target)
    return sorted(out)


def test_cerc20_string_loop_inductive_step_proved():
    from evm_ir.json_parser import load_ir_from_json
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from verification.loop_induction import Tier1LoopInduction
    from verification.loop_pairing import (
        analyze_evm_blocks,
        analyze_x86_blocks,
        build_evm_cfg,
        build_x86_cfg,
    )

    evm_blocks = load_ir_from_json(_CERC20_JSON).blocks
    hex_str = open(_CERC20_HEX).read().strip()
    x86_blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))

    evm_succs, _ = build_evm_cfg(evm_blocks)
    x86_succs, _ = build_x86_cfg(x86_blocks)
    evm_analysis, _ = analyze_evm_blocks(evm_blocks)
    x86_analysis, _ = analyze_x86_blocks(x86_blocks)

    evm_loop = next(l for l in evm_analysis.loops if l.header == 0x739)
    x86_loop = next(l for l in x86_analysis.loops if l.header == 0x107A2)

    checker = Tier1LoopInduction(
        evm_blocks,
        x86_blocks,
        evm_header=0x739,
        x86_header=0x107A2,
        evm_exits=_loop_exits(evm_loop, evm_succs),
        x86_exits=_loop_exits(x86_loop, x86_succs),
        stack_depth=3,  # IR block min_depth：循环体触碰的栈窗口
        timeout_ms=120000,
        evm_body=set(evm_loop.body),
    )
    result = checker.check_inductive_step()

    assert result.proved, (
        f"expected proved, got {result.status}: {result.reasons[:3]}\n"
        f"queries tail: {result.queries[-6:]}"
    )
    # envelope 排除必须显式记录（§4.3——不是无条件证明）
    assert any("envelope" in reason for reason in result.reasons)
    # ②(b) 回边 R 保持确实被证明过（非空洞）
    assert any("②(b)" in label for label, _ in result.queries)
