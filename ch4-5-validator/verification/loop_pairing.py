"""P1：两侧支配分析、natural loop 识别、Tier 1 循环头配对与 §6 结构守卫。

设计依据 docs/循环处理增强方案.md §3.1/§6：

- natural loop 回边 = 边 u→h 且 h 支配 u。真实合约中多数"按序回跳"是
  Solidity 内部函数的调用/返回伪回边（共享子例程位于前部块），**严禁**
  用朴素"目标地址在前"判定循环。
- ``irreducible``（去掉全部 back edge 后仍有环）在真实合约上**恒为 True**：
  resolved_multi 返回跳的 immediate_set 边是过近似（指向所有可能返回点），
  必然产生"调用-返回"假环——它们不是可执行循环（每条路径返回地址具体）。
  因此该标志只作信息暴露、不作守卫失败理由；真被漏掉的可执行环会在
  执行期撞 depth 剪枝 → P0 coverage 证书 incomplete → 验证失败（fail-closed
  链条闭合在执行层而非静态层）。
- EVM JUMP/JUMPI 三种形态：immediate+is_static（static_single）、
  immediate_set（resolved_multi，函数返回跳）、二者皆无（dynamic_unresolved，
  将编译为 jumpCode dispatcher，不建模 ⇒ 守卫失败）。
- x86 侧 go-bridge `ret` 站点带静态 RIP 相对返回地址（compileCallGoFunction
  的 `lea REG, [rip+disp]` 模式）；无该模式的 `ret` 是错误码终止出口。

本模块只做**检测与报告**（P1 范围）；enforcement 由验证管线在 P2/P4 接入。
"""

import re
from dataclasses import dataclass, field
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

from evm_ir.models import EVMBlock, EvmOperator
from x86_64.disassembler import parse_operands
from x86_64.models import X86Block


# ---------------------------------------------------------------------------
# 通用图算法与 x86 侧分析已提取到 x86_64/loop_analysis.py
#
# 提取理由是解开 import 环（Tier 2 copy-loop 发现要用这些函数，经
# `verification/__init__.py` 走回来会成环）。这里 re-export 保持既有调用点与
# 测试不变；**行为逐字未改**。
# ---------------------------------------------------------------------------

from x86_64.loop_analysis import (  # noqa: F401  (re-export)
    LoopAnalysis,
    NaturalLoop,
    _bridge_return_target,
    _dominates,
    _reverse_postorder,
    analyze_x86_blocks,
    build_x86_cfg,
    classify_x86_call_return_edge,
    compute_idoms,
    count_backward_target_edges,
    find_natural_loops,
    is_evm_tag_header,
    x86_call_return_back_edge_filter,
)



@dataclass
class EvmJumpClassification:
    """§3.1 的 JUMP/JUMPI 形态统计。"""

    static_single: int = 0
    resolved_multi: int = 0
    dynamic_unresolved: int = 0
    dynamic_sites: List[int] = field(default_factory=list)
    missing_targets: List[Tuple[int, int]] = field(default_factory=list)  # (pc, target)



_EVM_SKIP_OPS = frozenset({"TAG", "BLOCKEND"})
_EVM_TERMINAL_OPS = frozenset({"STOP", "RETURN", "REVERT", "SELFDESTRUCT", "INVALID"})
_EVM_CONTROL_OPS = _EVM_TERMINAL_OPS | frozenset({"JUMP", "JUMPI"})


def _evm_control_op(block: EVMBlock) -> Optional[EvmOperator]:
    """块的活控制流操作：过滤 TAG/BLOCKEND 后的第一个控制流操作。

    与 ``evm_ir.cfg_executor`` 的约定一致——其后的指令是死代码。
    """
    ops = (op for op in block.operations if op.kind.upper() not in _EVM_SKIP_OPS)
    return next((op for op in ops if op.kind.upper() in _EVM_CONTROL_OPS), None)


def build_evm_cfg(
    blocks: Sequence[EVMBlock],
) -> Tuple[Dict[int, List[int]], EvmJumpClassification]:
    """从 EVM IR blocks 构建静态块级 CFG。

    控制流约定与 ``evm_ir.cfg_executor`` 一致：过滤 TAG/BLOCKEND 后，
    第一个控制流操作决定后继；其后指令视为死代码。
    """
    blocks_by_pc = {block.pc: block for block in blocks}
    classification = EvmJumpClassification()
    succs: Dict[int, List[int]] = {}

    def _add_target(source_pc: int, target: int, out: List[int]) -> None:
        if target in blocks_by_pc:
            out.append(target)
        else:
            classification.missing_targets.append((source_pc, target))

    for i, block in enumerate(blocks):
        next_pc = blocks[i + 1].pc if i + 1 < len(blocks) else None
        ctrl = _evm_control_op(block)

        out: List[int] = []
        if ctrl is None:
            if next_pc is not None:
                out.append(next_pc)
        else:
            kind = ctrl.kind.upper()
            if kind in _EVM_TERMINAL_OPS:
                pass
            elif kind == "JUMP":
                if ctrl.immediate is not None and ctrl.is_static:
                    classification.static_single += 1
                    _add_target(ctrl.pc, ctrl.immediate, out)
                elif ctrl.immediate_set:
                    classification.resolved_multi += 1
                    for target in dict.fromkeys(ctrl.immediate_set):
                        _add_target(ctrl.pc, target, out)
                else:
                    classification.dynamic_unresolved += 1
                    classification.dynamic_sites.append(ctrl.pc)
            elif kind == "JUMPI":
                if ctrl.immediate is not None and ctrl.is_static:
                    classification.static_single += 1
                    _add_target(ctrl.pc, ctrl.immediate, out)
                elif ctrl.immediate_set:
                    # 与 JUMP/classify_raw_jump_ops 口径一致：immediate_set
                    # 是 resolved_multi，taken 边逐一显式
                    classification.resolved_multi += 1
                    for target in dict.fromkeys(ctrl.immediate_set):
                        _add_target(ctrl.pc, target, out)
                else:
                    classification.dynamic_unresolved += 1
                    classification.dynamic_sites.append(ctrl.pc)
                if next_pc is not None:
                    out.append(next_pc)
        succs[block.pc] = out

    return succs, classification


# ---------------------------------------------------------------------------
# 按形态疑似 internal-call/return 的回边识别（EVM 侧）
#
# 定位与 fail-safe 论证见 `x86_64/loop_analysis.py` 同名小节：这是**达成率优化，
# 不是健全性机制**；排除只作用于 loop-backedge 检测，**执行 CFG 不删除任何边**。
#
# 两侧判据互为镜像（同一条 codegen 事实的 IR 面与机器码面），因此排除数在两侧
# 必须一致；不一致时 ``pair_natural_loops`` 会因数量不等而全部不配对、守卫如实
# 失败——错配方向仍是 fail-closed，不需要额外断言。
# ---------------------------------------------------------------------------


def evm_resolved_return_sites(blocks: Sequence[EVMBlock]) -> FrozenSet[int]:
    """全程序**已解析的返回站点**集合 = 所有 resolved_multi JUMP 的目标并集。

    这是 Go 侧 `resolveSymbolicJumps` 的产物：某个 pc 出现在某条返回跳的
    ``immediate_set`` 里，就等于 IR 自己作证"这个 pc 是某次函数调用的返回地址"。
    用它判定"某个 PUSH 立即数是不是返回标签"，依据来自 IR 事实而非常量猜测。

    口径与 ``build_evm_cfg`` 一致，只取每块的活控制流操作（终止指令之后的
    IR 导出尾跳是死代码，不作为证据）。
    """
    sites: set = set()
    for block in blocks:
        ctrl = _evm_control_op(block)
        if ctrl is not None and ctrl.immediate_set:
            sites.update(ctrl.immediate_set)
    return frozenset(sites)


def classify_evm_call_return_edge(
    latch_block: EVMBlock,
    header: int,
    return_sites: FrozenSet[int],
) -> Optional[str]:
    """判断回边 ``latch → header`` 在 EVM 侧是否呈 internal-call/return 形态。

    Returns:
        ``"call"`` / ``"return"`` / None（认不出 ⇒ 保留为循环回边）。

    **call**（``PUSH <resolved return tag>; …; JUMP <callee>``）三个条件同时成立：

    1. 活控制流是**无条件** ``JUMP``、静态单目标且目标就是 ``header``
       （``header`` 即被调函数入口）。条件跳转不可能是调用边——codegen 对
       JUMPI 走的是另一条下降路径。
    2. 块内某个 ``PUSH`` 的立即数落在 ``return_sites`` 里且不等于 ``header``：
       它就是压给被调函数的返回标签，且这一身份由 IR 里真实存在的返回跳作证。
    3. 块的 ``stack_depth != 0``。codegen 在 JUMP 处按 ``StackDepth*stackBytesSize``
       调整栈帧基址；循环回边回到同一个栈帧（delta 恒为 0），调用边要为被调函数
       压出新帧。这一条与 x86 侧的"非零 stack-frame delta"是同一个事实。

    三条都要求，是为了把"循环体里恰好 PUSH 了一个与某返回站点同值的常量"
    这类巧合挡在门外。

    **return**（``JUMP immediate_set``）：活控制流是 resolved_multi ``JUMP``，
    且去重后的目标集**恰好只有 ``header`` 一个**。此时 `resolveSymbolicJumps`
    把这条返回跳精确解析到了唯一目标，边与"某次调用的返回"一一对应。目标集有
    ≥2 个元素时它是跨调用点的并集过近似，单条边不再对应确定的调用/返回配对，
    保留不排除（保守方向；这也正是设计文档说 immediate_set 必然造出残环的原因）。
    """
    ctrl = _evm_control_op(latch_block)
    if ctrl is None or ctrl.kind.upper() != "JUMP":
        return None

    if ctrl.immediate_set:
        targets = list(dict.fromkeys(ctrl.immediate_set))
        return "return" if targets == [header] else None

    if not (ctrl.is_static and ctrl.immediate == header):
        return None
    if latch_block.stack_depth == 0:
        return None
    for op in latch_block.operations:
        if op.kind.upper() != "PUSH" or op.immediate is None:
            continue
        if op.immediate != header and op.immediate in return_sites:
            return "call"
    return None


def evm_call_return_back_edge_filter(
    blocks: Sequence[EVMBlock],
) -> Callable[[int, int], bool]:
    """构造 ``find_natural_loops`` 用的回边谓词：call/return 形态的边返回 False。"""
    blocks_by_pc = {block.pc: block for block in blocks}
    return_sites = evm_resolved_return_sites(blocks)

    def keep(latch: int, header: int) -> bool:
        latch_block = blocks_by_pc.get(latch)
        if latch_block is None:
            return True  # 认不出就保留
        return classify_evm_call_return_edge(latch_block, header, return_sites) is None

    return keep


def analyze_evm_blocks(
    blocks: Sequence[EVMBlock],
    exclude_call_return_shaped_edges: bool = False,
) -> Tuple[LoopAnalysis, EvmJumpClassification]:
    """EVM 侧一站式：静态 CFG + natural loop 分析。

    Args:
        exclude_call_return_shaped_edges: 打开后，按形态疑似 Solidity 内部函数
            调用/返回的回边不再计入 natural loop（见
            ``classify_evm_call_return_edge``）。默认 False ⇒ 行为不变。
    """
    succs, classification = build_evm_cfg(blocks)
    entry = blocks[0].pc
    back_edge_filter = (
        evm_call_return_back_edge_filter(blocks)
        if exclude_call_return_shaped_edges
        else None
    )
    return (
        find_natural_loops(succs, entry, back_edge_filter=back_edge_filter),
        classification,
    )


def classify_raw_jump_ops(blocks: Sequence[EVMBlock]) -> EvmJumpClassification:
    """§3.1 原始口径：统计**所有** JUMP/JUMPI 操作（含终止指令后的死代码尾跳）。

    ``build_evm_cfg`` 的分类只计入活控制流（每块第一个控制流操作），
    两个口径的差 = 终止指令后的 IR 导出尾部 JUMP。守卫用活口径；
    本函数仅用于与设计文档统计对账。
    """
    classification = EvmJumpClassification()
    for block in blocks:
        for op in block.operations:
            kind = op.kind.upper()
            if kind not in ("JUMP", "JUMPI"):
                continue
            if op.immediate is not None and op.is_static:
                classification.static_single += 1
            elif op.immediate_set:
                classification.resolved_multi += 1
            else:
                classification.dynamic_unresolved += 1
                classification.dynamic_sites.append(op.pc)
    return classification


# ---------------------------------------------------------------------------
# x86 静态 CFG
# ---------------------------------------------------------------------------



def pair_natural_loops(
    evm_loops: Sequence[NaturalLoop],
    x86_loops: Sequence[NaturalLoop],
) -> Tuple[List[Tuple[NaturalLoop, NaturalLoop]], List[NaturalLoop], List[NaturalLoop]]:
    """按 header 顺序 + latch 数结构校验配对两侧 natural loops。

    配不上不猜：数量不等 ⇒ 全部不配对；逐位 latch 数不等 ⇒ 该位不配对。
    错误方向是安全的——错配/漏配只会让后续归纳失败并降级，不会假绿。
    """
    evm_sorted = sorted(evm_loops, key=lambda l: l.header)
    x86_sorted = sorted(x86_loops, key=lambda l: l.header)

    if len(evm_sorted) != len(x86_sorted):
        return [], list(evm_sorted), list(x86_sorted)

    pairs: List[Tuple[NaturalLoop, NaturalLoop]] = []
    unpaired_evm: List[NaturalLoop] = []
    unpaired_x86: List[NaturalLoop] = []
    for evm_loop, x86_loop in zip(evm_sorted, x86_sorted):
        if len(evm_loop.back_edges) == len(x86_loop.back_edges):
            pairs.append((evm_loop, x86_loop))
        else:
            unpaired_evm.append(evm_loop)
            unpaired_x86.append(x86_loop)
    return pairs, unpaired_evm, unpaired_x86


@dataclass
class LoopGuardReport:
    """§6 结构守卫的检测报告（P1 只报告，enforcement 在管线层接入）。"""

    evm_classification: EvmJumpClassification
    evm_analysis: LoopAnalysis
    x86_analysis: LoopAnalysis
    x86_unresolved_jump_sites: List[int]
    pairs: List[Tuple[NaturalLoop, NaturalLoop]]
    unpaired_evm: List[NaturalLoop]
    unpaired_x86: List[NaturalLoop]

    def reasons(self) -> List[str]:
        out: List[str] = []
        cls = self.evm_classification
        if cls.dynamic_unresolved:
            out.append(
                "dynamic_unresolved JUMP/JUMPI (jumpCode dispatcher, not modeled) "
                f"at pc={cls.dynamic_sites}"
            )
        if cls.missing_targets:
            out.append(f"EVM jump targets outside block table: {cls.missing_targets}")
        if self.x86_unresolved_jump_sites:
            out.append(
                "x86 jumps with unresolved static targets at "
                f"{[hex(a) for a in self.x86_unresolved_jump_sites]}"
            )
        if self.unpaired_x86:
            headers = [hex(l.header) for l in self.unpaired_x86]
            out.append(f"x86 natural loops without Tier-1 pair / Tier-2 lemma: {headers}")
        if self.unpaired_evm:
            headers = [hex(l.header) for l in self.unpaired_evm]
            out.append(f"EVM natural loops without x86 counterpart: {headers}")
        return out

    @property
    def call_return_shaped_evm_edges(self) -> Tuple[Tuple[int, int], ...]:
        """EVM 侧按形态疑似 call/return、已排除出 loop-backedge 检测的回边。"""
        return self.evm_analysis.excluded_back_edges

    @property
    def call_return_shaped_x86_edges(self) -> Tuple[Tuple[int, int], ...]:
        """x86 侧按形态疑似 call/return、已排除出 loop-backedge 检测的回边。"""
        return self.x86_analysis.excluded_back_edges

    def notes(self) -> List[str]:
        """信息性观察（不影响守卫结论）。"""
        out: List[str] = []
        if self.call_return_shaped_evm_edges or self.call_return_shaped_x86_edges:
            # 达成率优化的痕迹必须可见：排除是形态推断，不是已证的语义分类。
            out.append(
                "back edges excluded from loop detection as call/return shaped "
                f"(execution CFG unchanged): EVM {len(self.call_return_shaped_evm_edges)}, "
                f"x86 {len(self.call_return_shaped_x86_edges)}"
            )
        if self.evm_analysis.irreducible:
            out.append(
                "EVM CFG has residual cycles beyond natural-loop back edges "
                "(expected: immediate_set call/return over-approximation)"
            )
        if self.x86_analysis.irreducible:
            out.append(
                "x86 CFG has residual cycles beyond natural-loop back edges"
            )
        return out

    @property
    def ok(self) -> bool:
        return not self.reasons()


def analyze_program_pair(
    evm_blocks: Sequence[EVMBlock],
    x86_blocks: Sequence[X86Block],
    tier2_matcher: Optional[Callable[[NaturalLoop], bool]] = None,
    exclude_call_return_shaped_edges: bool = False,
) -> LoopGuardReport:
    """对一对 (EVM IR, x86) 程序执行完整的 P1 检测：

    两侧支配分析 → natural loop 识别 → **Tier 1/Tier 2 分层**（TAG 序言
    判别：带 compileEVMTag 跨块序言的 x86 循环头是 EVM 级循环，其余是
    codegen 内生循环；见 ``is_evm_tag_header``）→ Tier 2 模板匹配 →
    Tier 1 配对 → 守卫报告。

    fail-closed 语义：
    - Tier 2 候选（无 TAG 序言）必须命中 ``tier2_matcher``（已证引理的
      模板），否则计入 unpaired_x86 → 守卫失败。
    - Tier 1 候选（带 TAG 序言）进入与 EVM 循环的顺序+结构配对。

    Args:
        tier2_matcher: 判断某条 x86 natural loop 是否命中**已证** Tier 2
            引理模板（P3 提供；默认 None ⇒ 无引理可用，Tier 2 候选全部
            落入 unpaired_x86，守卫如实失败）。
        exclude_call_return_shaped_edges: 打开后，两侧按形态疑似 Solidity 内部
            函数调用/返回的回边不再计入 natural loop（§6"调用/返回形态候选的
            处置"）。**默认 False ⇒ 行为逐字不变。**

            这是**达成率优化，不是健全性机制**：收益是不对函数调用边徒劳跑
            Tier 1 归纳、不让守卫因它们拒绝整个合约。排除只作用于
            loop-backedge 检测，**执行 CFG 不删除任何边**；误排除方向 fail-safe
            ——被排除的边照常展开执行，真藏着符号 bound 循环时 depth-pruning 的
            coverage 证书会 fail-closed 抓住。

            两侧独立判定、判据互为镜像，因此排除数天然互为交叉校验：一侧多排
            一条就会让 ``pair_natural_loops`` 数量不等而全部不配对、守卫如实失败。
    """
    evm_analysis, evm_classification = analyze_evm_blocks(
        evm_blocks, exclude_call_return_shaped_edges=exclude_call_return_shaped_edges
    )
    x86_analysis, x86_unresolved = analyze_x86_blocks(
        x86_blocks, exclude_call_return_shaped_edges=exclude_call_return_shaped_edges
    )

    blocks_by_addr = {block.start_addr: block for block in x86_blocks}
    tier1_candidates: List[NaturalLoop] = []
    unmatched_tier2: List[NaturalLoop] = []
    for loop in x86_analysis.loops:
        header_block = blocks_by_addr.get(loop.header)
        if header_block is not None and is_evm_tag_header(header_block, blocks_by_addr):
            tier1_candidates.append(loop)
        elif tier2_matcher is not None and tier2_matcher(loop):
            continue  # 命中已证 Tier 2 引理：由引理替换，无需 Tier 1 配对
        else:
            unmatched_tier2.append(loop)

    pairs, unpaired_evm, unpaired_x86 = pair_natural_loops(
        evm_analysis.loops, tier1_candidates
    )
    unpaired_x86 = list(unpaired_x86) + unmatched_tier2

    return LoopGuardReport(
        evm_classification=evm_classification,
        evm_analysis=evm_analysis,
        x86_analysis=x86_analysis,
        x86_unresolved_jump_sites=x86_unresolved,
        pairs=pairs,
        unpaired_evm=unpaired_evm,
        unpaired_x86=unpaired_x86,
    )
