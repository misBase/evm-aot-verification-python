"""x86 侧的 CFG 构建、支配分析与 natural loop 识别。

从 `verification/loop_pairing.py` 提取，**行为逐字不变**。提取的唯一理由是解开
import 环：`x86_64/summaries/` 下的 Tier 2 copy-loop 发现需要这些函数，而
`verification/__init__.py` 会拉起 `equivalence_checker`，后者又经
`x86_64/__init__.py` → `cfg_executor` → `summaries` 绕回起点。

设计依据 docs/循环处理增强方案.md §3.1/§6：

- natural loop 回边 = 边 u→h 且 h 支配 u。真实合约中多数"按序回跳"是 Solidity
  内部函数的调用/返回伪回边，**严禁**用朴素"目标地址在前"判定循环。
- x86 侧 go-bridge `ret` 站点带静态 RIP 相对返回地址（compileCallGoFunction 的
  `lea REG, [rip+disp]` 模式）；无该模式的 `ret` 是错误码终止出口。

Tier 1 配对与 EVM 侧分析仍在 `verification/loop_pairing.py`，它 re-export 本模块
的符号以保持既有调用点不变。
"""

import re
from dataclasses import dataclass
from typing import (
    Callable,
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
)

from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.disassembler import parse_operands
from x86_64.models import X86Block, X86Instruction


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
    # 被 ``back_edge_filter`` 判掉、因而没有参与 loop 构造的回边（按 latch 升序）。
    # 默认空元组 ⇒ 未传 filter 时与历史结果逐字相同。
    excluded_back_edges: Tuple[Tuple[int, int], ...] = ()

    @property
    def back_edge_count(self) -> int:
        return sum(len(loop.back_edges) for loop in self.loops)



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

def find_natural_loops(
    succs: Dict[int, Sequence[int]],
    entry: int,
    back_edge_filter: Optional[Callable[[int, int], bool]] = None,
) -> LoopAnalysis:
    """识别 natural loops，并检测不可归约残环。

    Args:
        back_edge_filter: 可选谓词 ``(latch, header) -> keep``。返回 False 的回边
            不参与 loop 构造，改记入 ``LoopAnalysis.excluded_back_edges``。它**只**
            作用于 loop-backedge 检测：``succs`` 一条边都不删，支配关系仍在完整
            CFG 上算，``irreducible`` 的口径也逐字不变（被判掉的边照旧算回边、
            照旧不进 ``forward_succs``）。默认 None ⇒ 行为与历史完全一致。
    """
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
    excluded: List[Tuple[int, int]] = []
    edges_by_header: Dict[int, List[Tuple[int, int]]] = {}
    for latch, header in back_edges:
        if back_edge_filter is not None and not back_edge_filter(latch, header):
            excluded.append((latch, header))
            continue
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
        excluded_back_edges=tuple(sorted(excluded)),
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
    exclude_call_return_shaped_edges: bool = False,
) -> Tuple[LoopAnalysis, List[int]]:
    """x86 侧一站式：静态 CFG + natural loop 分析。

    Args:
        exclude_call_return_shaped_edges: 打开后，按形态疑似 Solidity 内部函数
            调用/返回的回边不再计入 natural loop（见
            ``classify_x86_call_return_edge``）。默认 False ⇒ 行为不变。
    """
    succs, unresolved_sites = build_x86_cfg(blocks)
    ordered = sorted(blocks, key=lambda b: b.start_addr)
    entry = ordered[0].start_addr
    back_edge_filter = (
        x86_call_return_back_edge_filter(ordered)
        if exclude_call_return_shaped_edges
        else None
    )
    return (
        find_natural_loops(succs, entry, back_edge_filter=back_edge_filter),
        unresolved_sites,
    )


# ---------------------------------------------------------------------------
# Tier 1 配对与 §6 守卫报告
# ---------------------------------------------------------------------------

# callEngine 字段偏移按名字取，别在正则里写死：TAG 序言判据与下面的 call/return
# 判据都要用，改 profile 时只有一处需要跟。
_CALLENGINE_GAS_OFFSET = AOT_COMPILER_PROFILE.offsets["gas_remaining"]
# 栈帧字节偏移字段（stackBasePointerInBytes）。compileEVMTag 读它做栈深检查；
# codegen 又在 JUMP/JUMPI 处按 `StackDepth*stackBytesSize` 调整它，那正是
# "函数调用压栈帧"与"循环回跳同帧"的分水岭（见下面 call/return 小节）。
_CALLENGINE_STACK_BYTE_OFFSET = AOT_COMPILER_PROFILE.offsets["stack_byte_offset"]

# `mov REG, IMM` / `cmp REG, IMM` / `sub REG, IMM` 共用的 "寄存器, 立即数" 形状
_X86_REG_IMM_RE = re.compile(r"^(\w+),\s*(0x[0-9a-fA-F]+|\d+)$")
_TAG_GAS_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$" % _CALLENGINE_GAS_OFFSET
)
_TAG_GAS_STORE_RE = re.compile(
    r"^qword ptr \[r13 \+ 0x%x\],\s*(\w+)$" % _CALLENGINE_GAS_OFFSET
)
_TAG_DEPTH_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r13 \+ 0x%x\]$" % _CALLENGINE_STACK_BYTE_OFFSET
)
# Go 侧 JCS 在 Capstone 下可能印成 jb 或 jc，同一条指令的两个别名。
_X86_JB_MNEMONICS = frozenset({"jb", "jc"})


def _without_nops(block: X86Block) -> List[X86Instruction]:
    """滤掉 nop：compileEVMTag 头上那条 nop 只是 jumpTable 的 label 锚点。"""
    return [i for i in block.instructions if i.mnemonic != "nop"]


def _tag_static_gas_check(block: X86Block) -> Optional[Tuple[str, int]]:
    """块尾是否为 ``makeStaticUseGas`` 的 gas 检查；返回 ``(临时寄存器, staticGas)``。

    形如 ``mov TMP,[r13+gas]; cmp TMP, staticGas; jb <OOG>``。临时寄存器由
    ``allocateRegisters`` 分配、并非恒为 rax，所以只能从 mov 里读出来再要求后两条
    用同一个寄存器。

    锚在**块尾**而不是块首：入口块的这段序言前面还压着保留寄存器初始化
    （见 ``is_evm_tag_header`` 的说明）。
    """
    insns = _without_nops(block)
    if len(insns) < 3:
        return None
    load, cmp_insn, jcc = insns[-3:]
    if (
        load.mnemonic != "mov"
        or cmp_insn.mnemonic != "cmp"
        or jcc.mnemonic not in _X86_JB_MNEMONICS
    ):
        return None
    load_match = _TAG_GAS_LOAD_RE.match(load.op_str)
    if load_match is None:
        return None
    cmp_match = _X86_REG_IMM_RE.match(cmp_insn.op_str)
    if cmp_match is None or cmp_match.group(1) != load_match.group(1):
        return None
    return load_match.group(1), int(cmp_match.group(2), 0)


def _tag_stack_depth_check(
    block: Optional[X86Block], temp_reg: str, static_gas: int
) -> bool:
    """fallthrough 块是否为 compileEVMTag 的"扣 gas + 栈深检查"节。

    形如 ``sub TMP, staticGas; mov [r13+gas], TMP; mov TMP,[r13+stackBytes];
    cmp TMP, minDepth*32; jb <Underflow>``。

    这一节是与 ``makeStaticUseGas`` 公共前缀的**唯一**区分点：动态 gas 路径
    （checkMemoryAndCalcDynamicGas*）扣完 gas 就去算内存扩展，从不读
    stackBasePointerInBytes。staticGas 立即数在两块间必须一致——同一次
    ``makeStaticUseGas`` 调用的 CMPQ 与 SUBQ 用的是同一个常量。
    """
    if block is None:
        return False
    insns = _without_nops(block)
    if len(insns) < 5:
        return False
    sub_insn, gas_store, depth_load, cmp_insn, jcc = insns[:5]
    if (
        sub_insn.mnemonic != "sub"
        or gas_store.mnemonic != "mov"
        or depth_load.mnemonic != "mov"
        or cmp_insn.mnemonic != "cmp"
        or jcc.mnemonic not in _X86_JB_MNEMONICS
    ):
        return False
    sub_match = _X86_REG_IMM_RE.match(sub_insn.op_str)
    if (
        sub_match is None
        or sub_match.group(1) != temp_reg
        or int(sub_match.group(2), 0) != static_gas
    ):
        return False
    store_match = _TAG_GAS_STORE_RE.match(gas_store.op_str)
    if store_match is None or store_match.group(1) != temp_reg:
        return False
    depth_match = _TAG_DEPTH_LOAD_RE.match(depth_load.op_str)
    if depth_match is None or depth_match.group(1) != temp_reg:
        return False
    cmp_match = _X86_REG_IMM_RE.match(cmp_insn.op_str)
    return cmp_match is not None and cmp_match.group(1) == temp_reg


def is_evm_tag_header(
    block: X86Block, blocks_by_addr: Mapping[int, X86Block]
) -> bool:
    """判别 x86 natural loop 头是否为 EVM 块边界（compileEVMTag 序言）。

    带该序言的循环头对应 EVM 级循环（Tier 1）；不带的是 codegen 内生循环
    （Tier 2 候选）。

    判据是 compileEVMTag（``impl_amd64.go``）前两节共 8 条指令的指纹，**跨块**：
    ``identify_basic_blocks`` 会在 gas 检查的 ``jb`` 处切断，序言后半截落到
    fallthrough 块里，所以必须带块表上下文——``X86Block.end_addr`` 恰是下一块的
    起始地址，故 fallthrough 就是 ``blocks_by_addr[block.end_addr]``。

    **为什么不能只看 gas 检查那三条**：``mov TMP,[r13+gas]; cmp TMP,IMM; jb``
    是 ``makeStaticUseGas`` 的公共前缀，动态 gas 路径
    （``checkMemoryAndCalcDynamicGas*``）生成同样的三条。只看它会严重过匹配：
    CErc20 34445 个块里命中 1522、Safe 30869 个里命中 1264，而两者真实的 EVM
    块数只有 723 / 742。补上 fallthrough 的栈深检查后正好 723 / 742，与 IR
    ``control_frames`` 数逐块相等。

    **为什么 gas 检查锚"块尾"而不锚"块首"**：入口块（0x0）里，第一个 TAG 的序言
    前面还压着函数入口的保留寄存器初始化——
    ``mov r14,[r13+stackBase]; add r14,[r13+stackBytes]; mov r15,[r13+memBase]``
    （``compileReservedStackBasePointerInitialization`` /
    ``compileReservedMemoryPointerInitialization``）。锚块首会把它漏掉，命中数停在
    722 / 741，正好差 1；这个差 1 既不是 fallthrough 窗口不够（放宽到 20 块结果
    不变），也不是别的边界情况，就是入口块这一处前缀。锚块尾即可精确覆盖。

    过匹配一直没有造成分层错误（natural loop 头子集上松严结论一致：CErc20 9/9、
    Safe 4/4），收紧是把"碰巧没错"变成"结构上不会错"。误判方向本身也是安全的：
    漏判 ⇒ 落进 Tier 2，必须命中已证引理否则守卫失败（fail-closed）。
    """
    gas_check = _tag_static_gas_check(block)
    if gas_check is None:
        return False
    temp_reg, static_gas = gas_check
    return _tag_stack_depth_check(
        blocks_by_addr.get(block.end_addr), temp_reg, static_gas
    )


# ---------------------------------------------------------------------------
# 按形态疑似 internal-call/return 的回边识别（x86 侧）
#
# **定位：达成率优化，不是健全性机制**（docs/循环处理增强方案.md §6
# "调用/返回形态候选的处置"）。收益有两条：
#   - 避免对 Solidity 内部函数的调用/返回边徒劳跑 Tier 1 归纳（每条分钟级 Z3）；
#   - 避免 §6 守卫因这些边配不上而拒绝整个合约。
#
# **误排除方向是 fail-safe 的**：排除只作用于 loop-backedge 检测，
# **执行 CFG 不删除任何边**——被排除的边照常展开执行；若其中真藏着符号 bound
# 循环，执行期照旧撞 depth 剪枝，`path_coverage_certificate()` 会 fail-closed
# 抓住（`x86_64/cfg_executor.py`）。判据因此按"宁可漏排除、不可错排除真循环"
# 取向：任何认不出的形态一律保留。
#
# 长期正解不是"排除"而是 cutpoint 泛化（docs/cutpoint泛化方案.md）——这些候选
# 的本质就是函数调用。
# ---------------------------------------------------------------------------

# `add qword ptr [r13 + <stack_byte_offset>], REG` —— 栈帧 delta 落盘
_X86_FRAME_DELTA_ADD_RE = re.compile(
    r"^qword ptr \[r13 \+ 0x%x\],\s*(\w+)$" % _CALLENGINE_STACK_BYTE_OFFSET
)
# `mov REG, qword ptr [r14 ± disp]` —— 从 EVM 栈槽装载返回 pc
_X86_STACK_SLOT_LOAD_RE = re.compile(
    r"^(\w+),\s*qword ptr \[r14(?:\s*[+-]\s*(?:0x[0-9a-fA-F]+|\d+))?\]$"
)
_X86_JEQ_MNEMONICS = frozenset({"je", "jz"})


def classify_x86_call_return_edge(
    latch_block: X86Block,
    header: int,
    blocks_by_addr: Mapping[int, X86Block],
) -> Optional[str]:
    """判断回边 ``latch → header`` 在 x86 侧是否呈 internal-call/return 形态。

    Returns:
        ``"call"`` / ``"return"`` / None（认不出 ⇒ 保留为循环回边）。

    共同前提：``header`` 必须带 compileEVMTag 序言，即它是 EVM 块边界。函数调用
    与函数返回都只能落在 EVM 块边界上；Tier 2 的 codegen 内生循环头没有这段序言，
    因此本判据结构上碰不到它们。这里只把 ``is_evm_tag_header`` 当**必要条件**用，
    判据收紧只会让排除更少 ⇒ 更多边留作循环回边，是保守方向。

    两种形态：

    **call**：``mov REG, IMM; add [r13+stack_byte_offset], REG; jmp header``，
    且 ``IMM != 0``。这是 `compileEVMJUMP` 对静态单目标跳转的下降形态，前面那两条
    是按块 ``StackDepth`` 调整栈帧基址。**非零 delta 是判据的核心**：循环回边
    回到同一个栈帧（delta 恒为 0），而调用边要为被调函数压出新帧。

    **return**：``mov REG, qword ptr [r14±disp]; cmp REG, IMM; je header``，
    即 `resolved_multi` JUMP 下降出的 ``CMPQ 返回pc + JEQ`` 比较链，且**装载与
    比较在同一个块内完成** ⇒ 整条链只有这一节 ⇒ 对应 IR 侧
    ``len(immediate_set) == 1``，即这条返回边被 `resolveSymbolicJumps` 精确解析
    到了唯一目标。多节链（``immediate_set`` ≥ 2 个目标）是跨调用点的并集过近似，
    单条边不再对应确定的调用/返回配对，故保留不排除（保守方向）。
    """
    header_block = blocks_by_addr.get(header)
    if header_block is None or not is_evm_tag_header(header_block, blocks_by_addr):
        return None

    insns = [i for i in latch_block.instructions if i.mnemonic != "nop"]
    if len(insns) < 3:
        return None
    last = insns[-1]
    if parse_operands(last).get("jump_target") != header:
        return None

    if last.mnemonic == "jmp":
        add_insn, mov_insn = insns[-2], insns[-3]
        if add_insn.mnemonic != "add" or mov_insn.mnemonic != "mov":
            return None
        add_match = _X86_FRAME_DELTA_ADD_RE.match(add_insn.op_str)
        if add_match is None:
            return None
        mov_match = _X86_REG_IMM_RE.match(mov_insn.op_str)
        if mov_match is None or mov_match.group(1) != add_match.group(1):
            return None
        return "call" if int(mov_match.group(2), 0) != 0 else None

    if last.mnemonic in _X86_JEQ_MNEMONICS:
        cmp_insn = insns[-2]
        if cmp_insn.mnemonic != "cmp":
            return None
        cmp_match = _X86_REG_IMM_RE.match(cmp_insn.op_str)
        if cmp_match is None:
            return None
        compared = cmp_match.group(1)
        for insn in insns[:-2]:
            if insn.mnemonic != "mov":
                continue
            load = _X86_STACK_SLOT_LOAD_RE.match(insn.op_str)
            if load is not None and load.group(1) == compared:
                return "return"
    return None


def x86_call_return_back_edge_filter(
    blocks: Sequence[X86Block],
) -> Callable[[int, int], bool]:
    """构造 ``find_natural_loops`` 用的回边谓词：call/return 形态的边返回 False。"""
    blocks_by_addr = {block.start_addr: block for block in blocks}

    def keep(latch: int, header: int) -> bool:
        latch_block = blocks_by_addr.get(latch)
        if latch_block is None:
            return True  # 认不出就保留
        return (
            classify_x86_call_return_edge(latch_block, header, blocks_by_addr)
            is None
        )

    return keep
