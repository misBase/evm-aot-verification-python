"""返回地址影子栈 → 块入口绝对栈深度类（docs/块级lockstep等价验证方案.md §3.2）。

块级 lock-step 证明要按 `(block_pair_id, k, msize, fmp)` 专门化，其中 `k` 是块
入口的**绝对栈深度**。朴素的上下文不敏感 CFG 给不出可用的 `k`：Go 的
`resolveSymbolicJumps` 把每个函数返回点解析成 `JUMP immediate_set`（该函数**全部**
调用点的返回地址并集），于是返回边把每个 callee 连回**所有** caller，栈深度沿这些
假环无限增长——实测 ENS 3.87×、CErc20 ≥240× 发散、Safe ≥267× 发散。

本模块的机制是**返回地址影子栈**（精确 call-string）：

    state = (pc, absolute_depth, pad_stack)

* 任意块：把块内 PUSH 的、值落在返回 pad 集合里的立即数**按程序序全部**压入影子栈
  （跳转目标自身不算）。
* 返回点（活控制流是带 ``immediate_set`` 的 ``JUMP``）：栈顶 ∈ ``immediate_set``
  ⇒ 只走那一条返回边并弹栈。
* 其余块：按 ``build_evm_cfg`` 的朴素后继走。
* 深度传播：``depth[succ] = depth[b] + b.stack_depth``。

净栈效应**一律取 Go 导出的 ``EVMBlock.stack_depth``**，不自建 opcode delta 表：
它已与手算 delta 表逐块对账（CErc20 709/723 一致，分歧全在 ``LOG``/``SSTORE`` 这类
`param` 不等于操作数个数的 op 上，以 Go 为准）。另外**静态 JUMP 不 pop**——Go 已把
``PUSH target; JUMP`` 折成 ``JUMP immediate=target``，块里没有对应的 PUSH，按"pop 1"
算会让一致块数从 709/723 掉到 171/723。

两个必须留下记录的坑（方案 §3.2 已写明，代价高昂，不要重新踩）：

**坑 1：静态判据不足以建图。** ``docs/cutpoint泛化方案.md §1.5`` 记的做法（调用点
PUSH 的 pad ∩ 被调方返回点 ``immediate_set``，交集唯一才算恢复）**不能用来建图**。
CErc20 块 836 是 ``PUSH 855; PUSH 850; JUMP 13048``——855 是留给**后续**调用的
continuation，只压"本次调用的那个 pad"就会丢帧，之后返回 thunk 链连续弹三帧却只
压过一帧，影子栈见底 ⇒ 假环复活 ⇒ 深度跑到 -41001。**栈序比集合交集信息量大。**
本模块仍计算该静态判据，但**只写进 stats 供报告**（``static_recovered``），
不参与建图。

**坑 2：没有优雅降级，只有悬崖。** 把静态恢复失败的调用点强制保守回退（栈顶匹配也
不采信，该返回点连回全部 caller），CErc20 立刻 1080×、不收敛、可达块掉到 437/723；
Safe 388×、不收敛、540/742。一次保守回退让影子栈错位，之后每个返回点都错、级联全
崩。所以这笔成本的真实形态是「2.5×，或彻底不可用」：影子栈 100% 命中必须做成**被
检查并 fail-closed 的结构前提**，而不是一个可以退让的近似。任何一次未命中 ⇒
``ShadowStackMiss``，**绝不**退回"连所有 caller"。

实测（``tests/unit/test_call_provenance.py`` 锁死为回归）：

    动态 provenance 恢复率  ENS 46/46、CErc20 915/915、Safe 378/378 = 100%，零回退
    深度类倍增              1.27× / 2.55× / 2.22×，全收敛，块覆盖 100%
    最大深度类              4 / 37 / 31        单一深度块占比 81% / 67% / 69%
    静态 provenance 恢复率  ENS 30/30、CErc20 215/230 (93%)、Safe 148/154 (96%)
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from dataclasses import dataclass, replace
from typing import (
    Dict,
    FrozenSet,
    List,
    Mapping,
    Optional,
    Sequence,
    Set,
    Tuple,
)

from evm_ir.models import EVMBlock
from verification.loop_pairing import (  # 复用既有口径，勿重写
    EvmJumpClassification,
    _evm_control_op,
    build_evm_cfg,
    evm_resolved_return_sites,
)


# ---------------------------------------------------------------------------
# 失败模式（全部 fail-closed；本模块不产出"尽力而为"的近似结果）
# ---------------------------------------------------------------------------


class CallProvenanceError(RuntimeError):
    """返回地址 provenance 分析的结构前提不成立。"""


class UnsupportedJumpShape(CallProvenanceError):
    """IR 里出现影子栈模型不覆盖的跳转形态（动态未解析 JUMP、缺失目标等）。

    这类形态会让 CFG 静默缺边 ⇒ 深度类不完备，必须整体拒绝。
    """


class ShadowStackMiss(CallProvenanceError):
    """某个返回点上影子栈未命中（空栈或栈顶不在 ``immediate_set`` 里）。

    见模块文档"坑 2"：**不做保守回退**。回退会让影子栈错位并级联污染整张 CFG，
    产出的深度类看上去仍是数字、实则完全错误（-41001 这类不可能值即由此而来）。
    """

    def __init__(
        self,
        pc: int,
        targets: Tuple[int, ...],
        stack: Tuple[int, ...],
        depth: int,
        reason: str = "栈顶不在 immediate_set 内",
    ) -> None:
        top = stack[-1] if stack else None
        super().__init__(
            f"返回点 pc={pc} 影子栈未命中({reason}): 栈顶={top}, "
            f"immediate_set={list(targets)[:8]} (栈深={len(stack)}, "
            f"绝对栈深={depth})。provenance 恢复率必须是 100%"
            "——不做保守回退，见 §3.2 悬崖。"
        )
        self.pc = pc
        self.targets = targets
        self.stack = stack
        self.depth = depth
        self.reason = reason


class DepthClassNotClosed(CallProvenanceError):
    """深度类不动点在预设预算内不封闭（疑似递归或未识别的栈增长循环）。"""

    def __init__(self, reason: str, pc: Optional[int] = None) -> None:
        where = f" (pc={pc})" if pc is not None else ""
        super().__init__(f"深度类不封闭{where}: {reason}")
        self.reason = reason
        self.pc = pc


class DepthClassInvariantViolated(CallProvenanceError):
    """自校验失败：某个块的某个可达绝对栈深 < 该块的 ``min_depth``。

    朴素（上下文不敏感）分析会给出 -41001 这种不可能值；正确结果里最小深度恒为 0。
    这条自校验因此是区分"正确的 2.5×"与"错误的数字"的最便宜的判据，必须保留。
    """


# ---------------------------------------------------------------------------
# 选项
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProvenanceOptions:
    """传播预算与**仅供哨兵回归使用**的三个反面开关。

    ``fail_closed=False`` / ``reverse_pad_push_order=True`` /
    ``distrust_return_points`` 产出的 CFG **不健全**，它们存在的唯一理由是让回归
    测试能观测到"关掉结构前提会塌成什么样"（方案 §8 验收基准 5 与压栈顺序哨兵）。
    ``build_call_provenance`` 拒绝这三个开关的非默认值。
    """

    state_budget: int = 4_000_000
    """状态展开预算上限；耗尽 = 不动点未封闭。"""

    shadow_stack_cap: int = 128
    """影子栈帧数上限；超出 = 疑似递归（三合约实测溢出 0 次）。"""

    depth_class_cap: int = 4096
    """单块深度类数上限；超出 = 该块发散（三合约实测最大 37）。"""

    fail_closed: bool = True
    """False 时未命中退回"连回全部 caller"的朴素行为（**不健全**，仅哨兵用）。"""

    reverse_pad_push_order: bool = False
    """True 时把同块内 pad 的压栈顺序反转（**不健全**，仅哨兵用）。"""

    distrust_return_points: FrozenSet[int] = frozenset()
    """这些返回点的影子栈匹配不予采信，强制走"未命中"分支（**不健全**，仅哨兵用）。

    方案 §8 验收基准 5 的哨兵入口：强制一次保守回退，验证系统 fail-closed
    而不是静默产出错误深度类。
    """


DEFAULT_OPTIONS = ProvenanceOptions()


# ---------------------------------------------------------------------------
# 结果
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProvenanceStats:
    """分析统计——供报告与回归断言，不参与建图。"""

    total_blocks: int
    reached_blocks: int
    return_points: int
    return_pads: int
    call_sites: int
    static_recovered: int
    """静态交集判据（``cutpoint泛化方案 §1.5``）恢复成功的调用点数。

    **只用于报告**：它在 CErc20 上只有 93%，而建图要求 100%——见模块文档坑 1，
    栈序比集合交集信息量大。
    """

    return_edges: int
    return_edges_matched: int
    fallback_returns: int
    """保守回退次数。fail-closed 模式下恒为 0（否则早已抛 ``ShadowStackMiss``）。"""

    expanded_states: int
    distinct_states: int
    shadow_stack_overflows: int
    depth_class_total: int
    max_depth_class: int
    single_depth_blocks: int
    min_depth_seen: int
    max_depth_seen: int
    depth_class_histogram: Tuple[Tuple[int, int], ...]
    """(深度类数, 块数) 升序，供分布回归。"""

    jump_shapes: EvmJumpClassification

    @property
    def depth_class_multiplier(self) -> float:
        """Σ|depth_classes| / 可达块数——块级证明相对整程序展开的规模倍增。"""
        return self.depth_class_total / max(self.reached_blocks, 1)

    @property
    def dynamic_recovery_rate(self) -> float:
        return self.return_edges_matched / max(self.return_edges, 1)

    @property
    def static_recovery_rate(self) -> float:
        return self.static_recovered / max(self.call_sites, 1)

    @property
    def single_depth_ratio(self) -> float:
        return self.single_depth_blocks / max(self.reached_blocks, 1)

    @property
    def block_coverage(self) -> float:
        return self.reached_blocks / max(self.total_blocks, 1)


@dataclass(frozen=True)
class CallProvenance:
    """一个合约的深度类与 context-sensitive CFG。"""

    depth_classes: Mapping[int, FrozenSet[int]]
    """块 pc -> 该块入口的全部可达绝对栈深度。不可达块不出现在映射里。"""

    succs: Mapping[int, Tuple[int, ...]]
    """context-sensitive CFG：只保留影子栈实际走到的边（升序去重）。

    是 ``build_evm_cfg`` 朴素后继的子集。**注意三合约上它与朴素后继逐块相等**
    ——每条返回边都在某个上下文里被真实走到，剪枝发生在 ``depth_succs`` 那一层
    （(pc, k) 粒度）而不是 pc 粒度。它仍是必要的记账：出现真子集就说明某条静态边
    在任何上下文下都不可达。
    """

    depth_succs: Mapping[Tuple[int, int], Tuple[int, ...]]
    """真正的 context-sensitive 转移关系：``(pc, k) -> 后继块 pc``。

    后继块的入口深度恒为 ``k + blocks_by_pc[pc].stack_depth``（每个块的净栈效应
    与上下文无关），所以这里只列后继 pc。这就是方案 §2.3 (H1)(H2) 三维闭包检查
    在 ``k`` 这一维上要消费的数据。
    """

    converged: bool
    stats: ProvenanceStats

    def depths_of(self, pc: int) -> FrozenSet[int]:
        """块的深度类；不可达块给空集。"""
        return self.depth_classes.get(pc, frozenset())

    def is_reachable(self, pc: int) -> bool:
        return bool(self.depth_classes.get(pc))


# ---------------------------------------------------------------------------
# 静态事实收集
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _Facts:
    """建图与报告所需的静态事实（口径见模块文档）。"""

    blocks: Tuple[EVMBlock, ...]
    blocks_by_pc: Mapping[int, EVMBlock]
    entry: int
    succs: Mapping[int, List[int]]
    classification: EvmJumpClassification
    pads: FrozenSet[int]
    return_points: Mapping[int, Tuple[int, ...]]
    call_sites: Mapping[int, Tuple[int, Tuple[int, ...]]]
    pad_pushes: Mapping[int, Tuple[int, ...]]


def _pads_pushed(block: EVMBlock, pads: FrozenSet[int]) -> Tuple[int, ...]:
    """块内 PUSH 的返回 pad，**按程序序、不去重**；排除本块跳转目标自身。

    不去重是有意的：影子栈是栈不是集合，同一个 pad 压两次就该弹两次。
    排除跳转目标是因为 Go 已把 ``PUSH target; JUMP`` 折成 ``JUMP immediate``，
    若立即数仍等于目标，它是目标而不是返回地址。
    """
    ctrl = _evm_control_op(block)
    target = ctrl.immediate if (ctrl is not None and ctrl.is_static) else None
    return tuple(
        op.immediate
        for op in block.operations
        if op.kind.upper() == "PUSH"
        and op.immediate is not None
        and op.immediate in pads
        and op.immediate != target
    )


def _collect_facts(blocks: Sequence[EVMBlock], options: ProvenanceOptions) -> _Facts:
    if not blocks:
        raise CallProvenanceError("EVM IR 为空，无法建立 provenance")

    ordered = tuple(blocks)
    blocks_by_pc = {block.pc: block for block in ordered}
    succs, classification = build_evm_cfg(ordered)
    pads = evm_resolved_return_sites(ordered)

    return_points: Dict[int, Tuple[int, ...]] = {}
    call_sites: Dict[int, Tuple[int, Tuple[int, ...]]] = {}

    for block in ordered:
        ctrl = _evm_control_op(block)
        if ctrl is None:
            continue
        kind = ctrl.kind.upper()
        if kind == "JUMPI" and ctrl.immediate_set:
            # 返回形态出现在条件跳转上，影子栈模型不覆盖（该弹栈还是不弹？）。
            # 三合约实测 0 例；出现即拒绝，不猜。
            raise UnsupportedJumpShape(
                f"块 {block.pc} 的 JUMPI 带 immediate_set={list(ctrl.immediate_set)}，"
                "影子栈模型只覆盖无条件 JUMP 的返回形态"
            )
        if kind != "JUMP":
            continue
        if ctrl.immediate_set:
            return_points[block.pc] = tuple(dict.fromkeys(ctrl.immediate_set))
            continue
        if ctrl.is_static and ctrl.immediate is not None:
            target = ctrl.immediate
            pushed = tuple(
                dict.fromkeys(
                    op.immediate
                    for op in block.operations
                    if op.kind.upper() == "PUSH"
                    and op.immediate is not None
                    and op.immediate != target
                    and op.immediate in pads
                )
            )
            if pushed:
                call_sites[block.pc] = (target, pushed)

    if classification.dynamic_unresolved:
        raise UnsupportedJumpShape(
            f"{classification.dynamic_unresolved} 处动态未解析 JUMP/JUMPI "
            f"(pc {classification.dynamic_sites[:8]})，CFG 会静默缺边 ⇒ 深度类不完备"
        )
    if classification.missing_targets:
        raise UnsupportedJumpShape(
            f"跳转目标不落在任何块上: {classification.missing_targets[:8]}"
        )

    pad_pushes = {}
    for block in ordered:
        pushed = _pads_pushed(block, pads)
        if options.reverse_pad_push_order:
            pushed = pushed[::-1]  # 哨兵用的反面配置，见 ProvenanceOptions
        pad_pushes[block.pc] = pushed

    return _Facts(
        blocks=ordered,
        blocks_by_pc=blocks_by_pc,
        entry=ordered[0].pc,
        succs=succs,
        classification=classification,
        pads=pads,
        return_points=return_points,
        call_sites=call_sites,
        pad_pushes=pad_pushes,
    )


@dataclass(frozen=True)
class ReturnAwareCfg:
    """给其他前向分析复用的 CFG 事实（``tools/msize_absint.py`` 的影子栈 CFG）。

    字段与 ``_Facts`` 同源、同口径，只是公开出去；不含深度传播结果。
    """

    entry: int
    by_pc: Mapping[int, EVMBlock]
    #: 朴素后继（``build_evm_cfg``）；返回点的后继是其 ``immediate_set`` 全集
    succs: Mapping[int, List[int]]
    #: 全程序已解析返回站点（``evm_resolved_return_sites``）
    pads: FrozenSet[int]
    #: 返回点块 pc -> 活控制流 ``JUMP`` 的 ``immediate_set``（去重、保序）
    ret_points: Mapping[int, Tuple[int, ...]]


def build_return_aware_cfg(evm_blocks: Sequence[EVMBlock]) -> ReturnAwareCfg:
    """抽出返回点 / 返回 pad / 朴素后继，供影子栈式分析使用。

    与 :func:`build_call_provenance` 共用 ``_collect_facts``，因此同样 fail-closed：
    JUMPI 上的 ``immediate_set``、动态未解析跳转、跳转目标不落在块上一律抛
    :class:`UnsupportedJumpShape`——CFG 缺边会让下游前向分析静默漏状态。
    """
    facts = _collect_facts(evm_blocks, DEFAULT_OPTIONS)
    return ReturnAwareCfg(
        entry=facts.entry,
        by_pc=facts.blocks_by_pc,
        succs=facts.succs,
        pads=facts.pads,
        ret_points=facts.return_points,
    )


# ---------------------------------------------------------------------------
# 静态交集判据（**只进报告，不参与建图**——见模块文档坑 1）
# ---------------------------------------------------------------------------


def _static_recovered_call_sites(facts: _Facts) -> Dict[int, Optional[int]]:
    """``cutpoint泛化方案 §1.5`` 的静态判据：调用点 pad ∩ 被调方返回点目标集。

    交集恰为 1 个元素才算"静态恢复"。CErc20 上只有 215/230——正是这 15 个缺口
    说明它建不了图。保留它是为了在报告里量化"静态信息比栈序少多少"。
    """
    same_level_cache: Dict[int, Set[int]] = {}

    def same_level_succs(pc: int) -> List[int]:
        # 同层可达：不跨越调用边，调用点直接续到它压入的 pad
        if pc in facts.return_points:
            return []
        call_site = facts.call_sites.get(pc)
        if call_site is not None:
            return list(call_site[1])
        return list(facts.succs.get(pc, ()))

    def same_level_reach(start: int) -> Set[int]:
        cached = same_level_cache.get(start)
        if cached is not None:
            return cached
        seen: Set[int] = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in seen or node not in facts.blocks_by_pc:
                continue
            seen.add(node)
            stack.extend(same_level_succs(node))
        same_level_cache[start] = seen
        return seen

    recovered: Dict[int, Optional[int]] = {}
    for pc, (target, pushed) in facts.call_sites.items():
        callee_returns: Set[int] = set()
        for node in same_level_reach(target):
            callee_returns.update(facts.return_points.get(node, ()))
        intersection = [pad for pad in pushed if pad in callee_returns]
        recovered[pc] = intersection[0] if len(intersection) == 1 else None
    return recovered


# ---------------------------------------------------------------------------
# 不动点传播
# ---------------------------------------------------------------------------


def analyze_call_provenance(
    evm_blocks: Sequence[EVMBlock],
    options: ProvenanceOptions = DEFAULT_OPTIONS,
) -> CallProvenance:
    """按 ``options`` 跑影子栈传播。

    ``options`` 取默认值时行为与 ``build_call_provenance`` 一致（fail-closed）。
    非默认值只供哨兵回归，产出的 CFG 不健全，见 ``ProvenanceOptions``。
    """
    facts = _collect_facts(evm_blocks, options)

    depths: Dict[int, Set[int]] = defaultdict(set)
    taken_succs: Dict[int, Set[int]] = defaultdict(set)
    taken_depth_succs: Dict[Tuple[int, int], Set[int]] = defaultdict(set)
    depths[facts.entry].add(0)

    start = (facts.entry, 0, ())
    seen = {start}
    work: List[Tuple[int, int, Tuple[int, ...]]] = [start]

    expanded = 0
    matched = 0
    fallbacks = 0
    overflows = 0
    min_depth_seen = 0
    max_depth_seen = 0

    while work and expanded < options.state_budget:
        pc, depth, stack = work.pop()
        expanded += 1
        block = facts.blocks_by_pc.get(pc)
        if block is None:
            continue

        # 净栈效应取 Go 导出值；静态 JUMP 不额外 pop（见模块文档）
        out_depth = depth + block.stack_depth
        min_depth_seen = min(min_depth_seen, out_depth)
        max_depth_seen = max(max_depth_seen, out_depth)

        # 坑 1：压入**全部** pad，按程序序，而不是"本次调用的那一个"
        stack = stack + facts.pad_pushes[pc]
        if len(stack) > options.shadow_stack_cap:
            if options.fail_closed:
                raise DepthClassNotClosed(
                    f"影子栈超过 {options.shadow_stack_cap} 帧，疑似递归或未识别的"
                    "栈增长循环",
                    pc=pc,
                )
            overflows += 1
            stack = stack[-options.shadow_stack_cap :]

        transitions: List[Tuple[int, Tuple[int, ...]]] = []
        targets = facts.return_points.get(pc)
        if targets is not None:
            trusted = pc not in options.distrust_return_points  # 哨兵开关
            if trusted and stack and stack[-1] in targets:
                matched += 1
                transitions.append((stack[-1], stack[:-1]))
            elif options.fail_closed:
                # 坑 2：没有优雅降级，只有悬崖
                raise ShadowStackMiss(
                    pc,
                    targets,
                    stack,
                    depth,
                    reason=(
                        "栈顶不在 immediate_set 内"
                        if trusted
                        else "该返回点被哨兵开关标记为不采信"
                    ),
                )
            else:
                fallbacks += 1
                rest = stack[:-1] if stack else stack
                transitions.extend((target, rest) for target in targets)
        else:
            transitions.extend((succ, stack) for succ in facts.succs.get(pc, ()))

        for target, new_stack in transitions:
            if target not in facts.blocks_by_pc:
                continue
            taken_succs[pc].add(target)
            taken_depth_succs[(pc, depth)].add(target)
            reached = depths[target]
            if out_depth not in reached and len(reached) >= options.depth_class_cap:
                if options.fail_closed:
                    raise DepthClassNotClosed(
                        f"单块深度类超过 {options.depth_class_cap}", pc=target
                    )
                continue
            reached.add(out_depth)
            key = (target, out_depth, new_stack)
            if key not in seen:
                seen.add(key)
                work.append(key)

    converged = not work
    if not converged and options.fail_closed:
        raise DepthClassNotClosed(
            f"状态展开预算 {options.state_budget} 耗尽，队列残留 {len(work)}"
        )

    depth_classes = {
        pc: frozenset(values) for pc, values in depths.items() if values
    }
    if options.fail_closed:
        _assert_min_depth_invariant(facts, depth_classes)

    static_recovered = _static_recovered_call_sites(facts)
    sizes = [len(values) for values in depth_classes.values()]
    histogram = Counter(sizes)
    stats = ProvenanceStats(
        total_blocks=len(facts.blocks),
        reached_blocks=len(depth_classes),
        return_points=len(facts.return_points),
        return_pads=len(facts.pads),
        call_sites=len(facts.call_sites),
        static_recovered=sum(1 for v in static_recovered.values() if v is not None),
        return_edges=matched + fallbacks,
        return_edges_matched=matched,
        fallback_returns=fallbacks,
        expanded_states=expanded,
        distinct_states=len(seen),
        shadow_stack_overflows=overflows,
        depth_class_total=sum(sizes),
        max_depth_class=max(sizes, default=0),
        single_depth_blocks=histogram.get(1, 0),
        min_depth_seen=min_depth_seen,
        max_depth_seen=max_depth_seen,
        depth_class_histogram=tuple(sorted(histogram.items())),
        jump_shapes=facts.classification,
    )

    return CallProvenance(
        depth_classes=depth_classes,
        succs={pc: tuple(sorted(v)) for pc, v in taken_succs.items()},
        depth_succs={
            key: tuple(sorted(v)) for key, v in sorted(taken_depth_succs.items())
        },
        converged=converged,
        stats=stats,
    )


def _assert_min_depth_invariant(
    facts: _Facts, depth_classes: Mapping[int, FrozenSet[int]]
) -> None:
    """自校验：每个块的每个可达绝对栈深都 ≥ 该块的 ``min_depth``。

    ``min_depth`` 是 Go 导出的"本块所需的最小入口栈深"。朴素分析沿假环把深度
    压到 -41001，这条判据能当场抓住；正确结果里最小深度恒为 0。
    """
    for pc, values in depth_classes.items():
        block = facts.blocks_by_pc.get(pc)
        if block is None:
            continue
        worst = min(values, default=None)
        if worst is not None and worst < block.min_depth:
            raise DepthClassInvariantViolated(
                f"块 {pc} 的可达绝对栈深 {worst} < min_depth {block.min_depth}"
                "（深度类被假返回边污染）"
            )


def build_call_provenance(
    evm_blocks: Sequence[EVMBlock],
    options: Optional[ProvenanceOptions] = None,
) -> CallProvenance:
    """建立 fail-closed 的返回地址 provenance；任何结构前提不成立即抛异常。

    Args:
        evm_blocks: 合约的 EVM IR 块，``evm_blocks[0]`` 是 entry。
        options: 只允许调整预算/上限；两个反面开关必须保持默认，否则 ``ValueError``。

    Raises:
        UnsupportedJumpShape: 出现影子栈模型不覆盖的跳转形态。
        ShadowStackMiss: 任一返回点未命中（**不做保守回退**，见模块文档坑 2）。
        DepthClassNotClosed: 不动点在预算内不封闭（疑似递归/栈增长循环）。
        DepthClassInvariantViolated: 自校验 ``depth >= min_depth`` 失败。
    """
    options = options or DEFAULT_OPTIONS
    if (
        not options.fail_closed
        or options.reverse_pad_push_order
        or options.distrust_return_points
    ):
        raise ValueError(
            "build_call_provenance 只接受 fail-closed 且程序序的配置；"
            "反面开关仅供 analyze_call_provenance 的哨兵回归使用"
        )
    provenance = analyze_call_provenance(evm_blocks, options)
    if not provenance.converged:  # 防御：正常路径已在传播里抛出
        raise DepthClassNotClosed("深度类不动点未收敛")
    return provenance


# ---------------------------------------------------------------------------
# 报告
# ---------------------------------------------------------------------------


def format_report(provenance: CallProvenance, name: str = "") -> str:
    """人读报告（方案 §6 阶段 0 的验收数字就按这张表核对）。"""
    s = provenance.stats
    head = f"===== {name} — call provenance =====" if name else "===== call provenance ====="
    lines = [
        head,
        f"返回点 / 返回 pad      : {s.return_points} / {s.return_pads}",
        f"调用点 / 静态唯一恢复  : {s.call_sites} / {s.static_recovered}"
        f"  ({s.static_recovery_rate * 100:.0f}%，仅报告，不参与建图)",
        f"动态 provenance 恢复率 : {s.return_edges_matched}/{s.return_edges}"
        f" = {s.dynamic_recovery_rate * 100:.1f}%  (回退 {s.fallback_returns})",
        f"可达块                 : {s.reached_blocks}/{s.total_blocks}"
        f" = {s.block_coverage * 100:.1f}%",
        f"状态展开 / 去重状态    : {s.expanded_states} / {s.distinct_states}",
        f"收敛                   : {provenance.converged}"
        f"  (深度范围 [{s.min_depth_seen},{s.max_depth_seen}],"
        f" 影子栈溢出 {s.shadow_stack_overflows})",
        f"深度类分布(类数->块数) : {dict(s.depth_class_histogram[:14])}",
        f"最大深度类             : {s.max_depth_class}",
        f"单一深度块占比         : {s.single_depth_blocks}/{s.reached_blocks}"
        f" = {s.single_depth_ratio * 100:.1f}%",
        f"Σ(深度类) / 倍增       : {s.depth_class_total} /"
        f" {s.depth_class_multiplier:.2f}×",
    ]
    return "\n".join(lines)


def provenance_fingerprint(provenance: CallProvenance) -> str:
    """深度类的稳定指纹，供 theorem key（方案 §2.3）引用。

    只覆盖 ``depth_classes`` 与 ``depth_succs``：这两项变了，块级定理的专门化参数
    就变了，证书必须失效。
    """
    import hashlib

    payload = json.dumps(
        {
            "depth_classes": {
                str(pc): sorted(values)
                for pc, values in sorted(provenance.depth_classes.items())
            },
            "depth_succs": {
                f"{pc}:{depth}": list(targets)
                for (pc, depth), targets in sorted(provenance.depth_succs.items())
            },
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(payload.encode()).hexdigest()[:16]


def load_evm_blocks(ir_json_path: str) -> List[EVMBlock]:
    """从 IR JSON 读出块序列（``blocks[0]`` 是 entry）。"""
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram

    return list(EVMProgram(load_ir_from_json(ir_json_path)).blocks)


def main(argv: Optional[Sequence[str]] = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("ir_json", nargs="+", help="EVM IR JSON 路径")
    parser.add_argument(
        "--budget", type=int, default=DEFAULT_OPTIONS.state_budget, help="状态展开预算"
    )
    args = parser.parse_args(argv)

    options = replace(DEFAULT_OPTIONS, state_budget=args.budget)
    status = 0
    for path in args.ir_json:
        try:
            provenance = build_call_provenance(load_evm_blocks(path), options)
        except CallProvenanceError as exc:  # fail-closed：报告并以非零码退出
            print(f"===== {path} — REJECTED =====\n{type(exc).__name__}: {exc}\n")
            status = 1
            continue
        print(format_report(provenance, name=path))
        print(f"指纹                   : {provenance_fingerprint(provenance)}\n")
    return status


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
