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

from evm_ir.models import EVMBlock
from x86_64.disassembler import parse_operands
from x86_64.models import X86Block


# ---------------------------------------------------------------------------
# 数据结构
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class NaturalLoop:
    """一个 natural loop：唯一 header + 全部回边（可多 latch）。"""

    header: int
    back_edges: Tuple[Tuple[int, int], ...]  # (latch, header)，按 latch 升序
    body: FrozenSet[int]

    @property
    def latches(self) -> Tuple[int, ...]:
        return tuple(latch for latch, _ in self.back_edges)


@dataclass(frozen=True)
class LoopAnalysis:
    """一侧 CFG 的循环分析结果。"""

    loops: Tuple[NaturalLoop, ...]  # 按 header 升序
    irreducible: bool  # 去掉 back edges 后仍有环
    unreachable_nodes: Tuple[int, ...]  # 入口不可达的节点（不参与支配分析）

    @property
    def back_edge_count(self) -> int:
        return sum(len(loop.back_edges) for loop in self.loops)


@dataclass
class EvmJumpClassification:
    """§3.1 的 JUMP/JUMPI 形态统计。"""

    static_single: int = 0
    resolved_multi: int = 0
    dynamic_unresolved: int = 0
    dynamic_sites: List[int] = field(default_factory=list)
    missing_targets: List[Tuple[int, int]] = field(default_factory=list)  # (pc, target)


# ---------------------------------------------------------------------------
# 支配分析（Cooper-Harvey-Kennedy）
# ---------------------------------------------------------------------------

def _reverse_postorder(succs: Dict[int, Sequence[int]], entry: int) -> List[int]:
    """迭代式 DFS 后序再反转；只含入口可达节点。"""
    visited = set()
    postorder: List[int] = []
    stack: List[Tuple[int, int]] = [(entry, 0)]
    visited.add(entry)
    while stack:
        node, child_idx = stack[-1]
        children = succs.get(node, ())
        if child_idx < len(children):
            stack[-1] = (node, child_idx + 1)
            child = children[child_idx]
            if child not in visited:
                visited.add(child)
                stack.append((child, 0))
        else:
            stack.pop()
            postorder.append(node)
    postorder.reverse()
    return postorder


def compute_idoms(succs: Dict[int, Sequence[int]], entry: int) -> Dict[int, int]:
    """经典 CHK 迭代算法求 immediate dominators（仅入口可达子图）。

    Returns:
        idom 映射；``idom[entry] == entry``。
    """
    rpo = _reverse_postorder(succs, entry)
    rpo_index = {node: i for i, node in enumerate(rpo)}
    reachable = set(rpo)

    preds: Dict[int, List[int]] = {node: [] for node in rpo}
    for node in rpo:
        for succ in succs.get(node, ()):
            if succ in reachable:
                preds[succ].append(node)

    idom: Dict[int, int] = {entry: entry}

    def _intersect(a: int, b: int) -> int:
        while a != b:
            while rpo_index[a] > rpo_index[b]:
                a = idom[a]
            while rpo_index[b] > rpo_index[a]:
                b = idom[b]
        return a

    changed = True
    while changed:
        changed = False
        for node in rpo[1:]:
            new_idom: Optional[int] = None
            for pred in preds[node]:
                if pred in idom:
                    new_idom = pred if new_idom is None else _intersect(pred, new_idom)
            if new_idom is not None and idom.get(node) != new_idom:
                idom[node] = new_idom
                changed = True
    return idom


def _dominates(idom: Dict[int, int], dominator: int, node: int) -> bool:
    """沿 idom 链上爬判断 dominator 是否支配 node。"""
    current = node
    while True:
        if current == dominator:
            return True
        parent = idom.get(current)
        if parent is None or parent == current:
            return False
        current = parent


# ---------------------------------------------------------------------------
# natural loop 识别
# ---------------------------------------------------------------------------

def find_natural_loops(succs: Dict[int, Sequence[int]], entry: int) -> LoopAnalysis:
    """识别 natural loops，并检测不可归约残环。"""
    rpo = _reverse_postorder(succs, entry)
    reachable = set(rpo)
    all_nodes = set(succs.keys())
    for targets in succs.values():
        all_nodes.update(targets)
    unreachable = tuple(sorted(all_nodes - reachable))

    idom = compute_idoms(succs, entry)

    preds: Dict[int, List[int]] = {node: [] for node in reachable}
    back_edges: List[Tuple[int, int]] = []
    forward_succs: Dict[int, List[int]] = {node: [] for node in reachable}
    for node in reachable:
        for succ in succs.get(node, ()):
            if succ not in reachable:
                continue
            preds[succ].append(node)
            if _dominates(idom, succ, node):
                back_edges.append((node, succ))
            else:
                forward_succs[node].append(succ)

    # 按 header 聚合回边并计算 loop body（latch 反向可达闭包，不越过 header）
    edges_by_header: Dict[int, List[Tuple[int, int]]] = {}
    for latch, header in back_edges:
        edges_by_header.setdefault(header, []).append((latch, header))

    loops: List[NaturalLoop] = []
    for header in sorted(edges_by_header):
        header_edges = sorted(edges_by_header[header])
        body = {header}
        stack = [latch for latch, _ in header_edges]
        while stack:
            node = stack.pop()
            if node in body:
                continue
            body.add(node)
            stack.extend(preds.get(node, ()))
        loops.append(
            NaturalLoop(
                header=header,
                back_edges=tuple(header_edges),
                body=frozenset(body),
            )
        )

    # 不可归约检测：去掉 back edges 后的可达子图必须无环（Kahn 拓扑排序）
    indegree = {node: 0 for node in reachable}
    for node in reachable:
        for succ in forward_succs[node]:
            indegree[succ] += 1
    worklist = [node for node, deg in indegree.items() if deg == 0]
    seen = 0
    while worklist:
        node = worklist.pop()
        seen += 1
        for succ in forward_succs[node]:
            indegree[succ] -= 1
            if indegree[succ] == 0:
                worklist.append(succ)
    irreducible = seen != len(reachable)

    return LoopAnalysis(
        loops=tuple(loops),
        irreducible=irreducible,
        unreachable_nodes=unreachable,
    )


def count_backward_target_edges(
    succs: Dict[int, Sequence[int]], order: Sequence[int]
) -> int:
    """按给定顺序统计"往回跳"边数（目标不在源之后）。仅用于 §3.1 统计口径。"""
    index = {node: i for i, node in enumerate(order)}
    count = 0
    for node, targets in succs.items():
        for target in targets:
            if node in index and target in index and index[target] <= index[node]:
                count += 1
    return count


# ---------------------------------------------------------------------------
# EVM 静态 CFG
# ---------------------------------------------------------------------------

_EVM_SKIP_OPS = frozenset({"TAG", "BLOCKEND"})
_EVM_TERMINAL_OPS = frozenset({"STOP", "RETURN", "REVERT", "SELFDESTRUCT", "INVALID"})
_EVM_CONTROL_OPS = _EVM_TERMINAL_OPS | frozenset({"JUMP", "JUMPI"})


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
        ops = [op for op in block.operations if op.kind.upper() not in _EVM_SKIP_OPS]
        ctrl = next((op for op in ops if op.kind.upper() in _EVM_CONTROL_OPS), None)

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


def analyze_evm_blocks(
    blocks: Sequence[EVMBlock],
) -> Tuple[LoopAnalysis, EvmJumpClassification]:
    """EVM 侧一站式：静态 CFG + natural loop 分析。"""
    succs, classification = build_evm_cfg(blocks)
    entry = blocks[0].pc
    return find_natural_loops(succs, entry), classification


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

_X86_TERMINAL_MNEMONICS = frozenset({"ud2", "int3", "hlt"})
_RIP_LEA_RE = re.compile(r"\[rip\s*([+-])\s*(0x[0-9a-fA-F]+|\d+)\]")


def _bridge_return_target(block: X86Block) -> Optional[int]:
    """从 go-bridge ret 块中提取静态返回地址。

    compileCallGoFunction 用 ``lea REG, [rip+disp]`` 把返回地址写入
    callEngine；取块内**最后一条** RIP 相对 lea。无该模式的 ret 是
    错误码终止出口（返回 None）。
    """
    target: Optional[int] = None
    for insn in block.instructions:
        if insn.mnemonic != "lea":
            continue
        match = _RIP_LEA_RE.search(insn.op_str)
        if not match:
            continue
        sign = -1 if match.group(1) == "-" else 1
        disp = int(match.group(2), 0)
        target = insn.addr + len(insn.bytes) + sign * disp
    return target


def build_x86_cfg(
    blocks: Sequence[X86Block],
) -> Tuple[Dict[int, List[int]], List[int]]:
    """从 x86 基本块构建静态块级 CFG。

    Returns:
        (succs, unresolved_sites)；unresolved_sites 是无法静态解析后继的
        跳转指令地址（间接跳转等），守卫据此 fail-closed。
    """
    ordered = sorted(blocks, key=lambda b: b.start_addr)
    blocks_by_addr = {block.start_addr: block for block in ordered}
    next_addr = {
        block.start_addr: (
            ordered[i + 1].start_addr if i + 1 < len(ordered) else None
        )
        for i, block in enumerate(ordered)
    }
    unresolved_sites: List[int] = []
    succs: Dict[int, List[int]] = {}

    for block in ordered:
        out: List[int] = []
        insns = block.instructions
        last = insns[-1] if insns else None
        if last is None:
            succs[block.start_addr] = out
            continue

        mnemonic = last.mnemonic
        fallthrough = next_addr[block.start_addr]

        if mnemonic == "jmp":
            operands = parse_operands(last)
            target = operands.get("jump_target")
            if target is None:
                unresolved_sites.append(last.addr)
            elif target in blocks_by_addr:
                out.append(target)
            # 越界 jmp（如截断 core）：无后继，守卫层不视为循环隐患
        elif mnemonic.startswith("j"):
            operands = parse_operands(last)
            target = operands.get("jump_target")
            if target is None:
                unresolved_sites.append(last.addr)
            elif target in blocks_by_addr:
                out.append(target)
            if fallthrough is not None:
                out.append(fallthrough)
        elif mnemonic == "ret":
            target = _bridge_return_target(block)
            if target is not None and target in blocks_by_addr:
                out.append(target)
            # 无 lea 模式：错误码终止出口，无后继
        elif mnemonic in _X86_TERMINAL_MNEMONICS:
            pass
        elif mnemonic == "call":
            # AOT 产物不经 call 做控制流；保守视为顺序执行
            if fallthrough is not None:
                out.append(fallthrough)
        else:
            if fallthrough is not None:
                out.append(fallthrough)
        succs[block.start_addr] = out

    return succs, unresolved_sites


def analyze_x86_blocks(
    blocks: Sequence[X86Block],
) -> Tuple[LoopAnalysis, List[int]]:
    """x86 侧一站式：静态 CFG + natural loop 分析。"""
    succs, unresolved_sites = build_x86_cfg(blocks)
    ordered = sorted(blocks, key=lambda b: b.start_addr)
    entry = ordered[0].start_addr
    return find_natural_loops(succs, entry), unresolved_sites


# ---------------------------------------------------------------------------
# Tier 1 配对与 §6 守卫报告
# ---------------------------------------------------------------------------

def is_evm_tag_header(block: X86Block) -> bool:
    """判别 x86 natural loop 头是否为 EVM 块边界（TAG 序言）。

    TAG 序言 = makeStaticUseGas 的 gas 检查开头：``mov rax,[r13+0x70]``
    → ``cmp rax, IMM`` → ``jb``（中间可能有 nop 对齐）。带该序言的循环头
    对应 EVM 级循环（Tier 1）；不带的是 codegen 内生循环（Tier 2 候选）。
    """
    meaningful = [i for i in block.instructions if i.mnemonic != "nop"][:3]
    if len(meaningful) < 3:
        return False
    first, second, third = meaningful
    return (
        first.mnemonic == "mov"
        and "[r13 + 0x70]" in first.op_str
        and second.mnemonic == "cmp"
        and third.mnemonic in ("jb", "jc")
    )


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

    def notes(self) -> List[str]:
        """信息性观察（不影响守卫结论）。"""
        out: List[str] = []
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
) -> LoopGuardReport:
    """对一对 (EVM IR, x86) 程序执行完整的 P1 检测：

    两侧支配分析 → natural loop 识别 → **Tier 1/Tier 2 分层**（TAG 序言
    判别：带 makeStaticUseGas 序言的 x86 循环头是 EVM 级循环，其余是
    codegen 内生循环）→ Tier 2 模板匹配 → Tier 1 配对 → 守卫报告。

    fail-closed 语义：
    - Tier 2 候选（无 TAG 序言）必须命中 ``tier2_matcher``（已证引理的
      模板），否则计入 unpaired_x86 → 守卫失败。
    - Tier 1 候选（带 TAG 序言）进入与 EVM 循环的顺序+结构配对。

    Args:
        tier2_matcher: 判断某条 x86 natural loop 是否命中**已证** Tier 2
            引理模板（P3 提供；默认 None ⇒ 无引理可用，Tier 2 候选全部
            落入 unpaired_x86，守卫如实失败）。
    """
    evm_analysis, evm_classification = analyze_evm_blocks(evm_blocks)
    x86_analysis, x86_unresolved = analyze_x86_blocks(x86_blocks)

    blocks_by_addr = {block.start_addr: block for block in x86_blocks}
    tier1_candidates: List[NaturalLoop] = []
    unmatched_tier2: List[NaturalLoop] = []
    for loop in x86_analysis.loops:
        header_block = blocks_by_addr.get(loop.header)
        if header_block is not None and is_evm_tag_header(header_block):
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
