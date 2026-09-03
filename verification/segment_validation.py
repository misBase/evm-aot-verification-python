"""havoc-origin 证明段的静态健全性检查（docs/循环处理增强方案.md §4.3/§6）。

归纳步从 havoc 状态出发，因此段内某些指令的语义前提与全程序模式不同：

- `GAS` opcode 读的是 cutpoint 上的 gas。**gas 已进 R** 后两侧取值相等，这条
  拒绝其实可以放宽；保守起见先保留（方向只多降级不假绿），放宽前需要确认
  `compileEVMGAS` 的 `Blk.StaticGas - Immediate` 在 havoc 的符号 gas 下与 EVM
  侧逐字对齐。
- `MSIZE` 只有在 `MSize` 已进 cutpoint 关系时才允许（schema 的 `memory_size`
  分量）。
- x86 侧要挡住"把真实 gas 值物化到栈上"的块——那是 GAS opcode 的 codegen，与
  普通 TAG 静态 gas 检查不同（后者读完就比较，不写栈）。

从 develop-cycle 吸收，按 develop 的现实调整：`supports_msize` 由
`CutpointRelationSchema` 提供。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Sequence, Set

from evm_ir.models import EVMBlock
from verification.loop_pairing import build_evm_cfg
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import X86Block


@dataclass(frozen=True)
class SegmentValidationResult:
    reachable_nodes: frozenset[int]
    reasons: tuple[str, ...]

    @property
    def ok(self) -> bool:
        return not self.reasons


def _reachable_until_stops(
    succs: Dict[int, Sequence[int]],
    entry: int,
    stops: Set[int],
) -> frozenset[int]:
    seen: set[int] = set()
    worklist = [entry]
    while worklist:
        node = worklist.pop()
        if node in seen:
            continue
        seen.add(node)
        if node != entry and node in stops:
            continue
        worklist.extend(succs.get(node, ()))
    return frozenset(seen)


class SegmentStructuralValidator:
    """Reject gas-dependent havoc segments and relation-incomplete MSIZE."""

    def validate_evm(
        self,
        blocks: Sequence[EVMBlock],
        *,
        entry_pc: int,
        stop_pcs: Iterable[int],
        supports_msize: bool,
    ) -> SegmentValidationResult:
        succs, classification = build_evm_cfg(blocks)
        reachable = _reachable_until_stops(succs, entry_pc, set(stop_pcs))
        reasons: list[str] = []
        if classification.dynamic_unresolved:
            reasons.append(
                "EVM segment has unresolved jumps at "
                f"{classification.dynamic_sites}"
            )
        if classification.missing_targets:
            reasons.append(
                "EVM segment has jump targets outside the block table: "
                f"{classification.missing_targets}"
            )
        by_pc = {block.pc: block for block in blocks}
        for pc in sorted(reachable):
            block = by_pc.get(pc)
            if block is None:
                continue
            for op in block.operations:
                kind = op.kind.upper()
                if kind == "GAS":
                    reasons.append(
                        f"havoc segment reaches GAS opcode at pc={op.pc}"
                    )
                elif kind == "MSIZE" and not supports_msize:
                    reasons.append(
                        f"havoc segment reaches MSIZE at pc={op.pc} without "
                        "MSize in the cutpoint relation"
                    )
        return SegmentValidationResult(reachable, tuple(reasons))

    def validate_x86(
        self,
        blocks: Sequence[X86Block],
        *,
        entry_addr: int,
        stop_addrs: Iterable[int],
    ) -> SegmentValidationResult:
        succs, unresolved = build_x86_cfg(blocks)
        reachable = _reachable_until_stops(succs, entry_addr, set(stop_addrs))
        reasons: list[str] = []
        if unresolved:
            reasons.append(
                "x86 segment has unresolved jumps at "
                f"{[hex(addr) for addr in unresolved]}"
            )
        by_addr = {block.start_addr: block for block in blocks}
        for addr in sorted(reachable):
            block = by_addr.get(addr)
            if block is not None and _looks_like_gas_value_materialization(block):
                reasons.append(
                    f"havoc segment reaches x86 real-gas value materialization "
                    f"at 0x{addr:x}"
                )
        return SegmentValidationResult(reachable, tuple(reasons))


def _looks_like_gas_value_materialization(block: X86Block) -> bool:
    """Distinguish GAS-value pushes from normal TAG static-gas checks."""

    reads_gas = any(
        insn.mnemonic == "mov" and "[r13 + 0x70]" in insn.op_str
        for insn in block.instructions
    )
    writes_gas = any(
        insn.mnemonic == "mov"
        and insn.op_str.strip().startswith("qword ptr [r13 + 0x70]")
        for insn in block.instructions
    )
    writes_stack = any(
        insn.mnemonic == "mov" and "[r14" in insn.op_str
        for insn in block.instructions
    )
    return reads_gas and writes_stack and not writes_gas


__all__ = ["SegmentStructuralValidator", "SegmentValidationResult"]
