"""Generic x86 slice summary framework."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, Protocol, Sequence, Tuple

from state.smt_state import SMTState
from x86_64.models import Register, X86Block


SummaryStart = Tuple[int, int]
SUMMARY_PLUGIN_MODES = frozenset({"off", "fallback", "strict"})


_BLOCK_TERMINATOR_MNEMONICS = {
    "jmp",
    "jb",
    "jae",
    "ja",
    "jbe",
    "je",
    "jne",
    "jl",
    "jle",
    "jg",
    "jge",
    "ret",
}


class SummaryMatchError(ValueError):
    """Raised when summary discovery finds an invalid or overlapping slice."""


class SummaryPreconditionError(ValueError):
    """summary 的适用前提是 SAT/unknown 而非被蕴含证明（prove-or-reject）。

    可信 summary 只在自己的前提域内成立。前提必须由**当前 path condition +
    调用方全局先验**证明；查询为 SAT 或 unknown 时必须拒绝应用，绝不能自行往
    ``SMTState.assumptions`` 里补一条未证前提——那会静默缩小证明域（假绿）。

    抛出后由 executor 决定：``fallback`` 策略下回退到逐指令执行原循环（语义与
    不启用 summary 完全一致），否则整体失败。
    """

    def __init__(
        self,
        *,
        kind: str,
        label: str,
        premise,
        result,
        location: "SummaryStart | None" = None,
    ) -> None:
        self.kind = kind
        self.label = label
        self.premise = premise
        self.result = result
        self.location = location
        where = (
            f" at 0x{location[0]:x}:{location[1]}" if location is not None else ""
        )
        rendered_premise = str(premise)
        if len(rendered_premise) > 1000:
            rendered_premise = (
                rendered_premise[:1000]
                + f"... <truncated {len(rendered_premise) - 1000} chars>"
            )
        super().__init__(
            f"{kind} summary precondition{where} not proved "
            f"({label}, solver={result}): {rendered_premise}"
        )


class SummarySingleEntryError(SummaryMatchError):
    """covered 区里有块能被外部边绕过 summary 入口直接进入（§5.4 单入口检查）。

    summary 只在符号执行**命中 ``start_key``** 时才折叠。若存在一条从 covered
    区之外指向 covered 区中**非入口块**的边，走那条边进来的路径会把这些块原样
    逐指令执行掉——**结论仍然健全**（逐指令执行的语义与不启用 summary 完全
    一致），塌掉的是「折叠一定生效」这条**完备性**保证。而后者是 Tier 1 证书
    折叠的硬前置：证书要断言「这段循环已整体被闭式引理替换」，只要有一条绕过
    边，该断言就只对部分路径成立，证书随之失去意义。

    为什么必须显式抛，而不是把这条 summary 悄悄从发现结果里删掉：删掉之后上层
    观察到的现象是「这里根本没有可折叠的循环」，与「有一条但被拒了」无法区分，
    证书阶段既报不出原因也定位不到是哪个块被绕过。抛出后由调用方按策略处置
    （例如关掉 copy_loop 重建 runtime，整体退回逐指令执行），这与
    :class:`SummaryPreconditionError` 的 prove-or-reject 纪律是同一条：
    **拒绝要留痕，降级由调用方决定。**
    """

    def __init__(
        self,
        *,
        kind: str,
        entry_addr: int,
        reason: str,
        bypass_edges: Sequence[Tuple[int, int]] = (),
    ) -> None:
        self.kind = kind
        self.entry_addr = entry_addr
        self.reason = reason
        self.bypass_edges = tuple(bypass_edges)
        rendered = ""
        if self.bypass_edges:
            shown = [
                f"0x{src:x}->0x{dst:x}" for src, dst in self.bypass_edges[:8]
            ]
            if len(self.bypass_edges) > 8:
                shown.append(f"... and {len(self.bypass_edges) - 8} more")
            rendered = ": " + ", ".join(shown)
        super().__init__(
            f"{kind} summary at 0x{entry_addr:x} is not single entry "
            f"({reason}){rendered}"
        )


@dataclass(frozen=True)
class SummaryContinuation:
    """Where execution resumes after a summary has been applied."""

    block_addr: int
    instruction_index: int = 0


@dataclass(frozen=True)
class X86Summary:
    """A trusted replacement for an x86 instruction slice.

    ``start_block_addr`` and ``start_instruction_index`` are the exact point at
    which the executor should apply the summary.  For cross-block summaries,
    ``covered_block_addrs`` must include every skipped block except the
    continuation block.  For same-block summaries, ``continuation`` names the
    first instruction after the summarized slice.

    ``entry_addr`` is a human-readable identifier used only for hit statistics
    and debug logging; the executor always locates a summary by ``start_key``.
    A spec may set ``entry_addr == start_block_addr`` when the two coincide.
    """

    kind: str
    entry_addr: int
    start_block_addr: int
    start_instruction_index: int
    continuation: SummaryContinuation
    covered_block_addrs: Tuple[int, ...]
    clobber_registers: Tuple[Register, ...]
    clobber_flags: Tuple[str, ...] = ("CF", "ZF", "SF", "OF")
    payload: Any = None

    @property
    def start_key(self) -> SummaryStart:
        return (self.start_block_addr, self.start_instruction_index)

    @property
    def is_cross_block(self) -> bool:
        return self.continuation.block_addr != self.start_block_addr


def find_summary_bypass_edges(
    summary: X86Summary,
    succs: Mapping[int, Sequence[int]],
) -> Tuple[Tuple[int, int], ...]:
    """列出所有「从 covered 区外指向 covered 区中非入口块」的静态边。

    判据只有三条，全部按静态 CFG 判定，不看可达性：

    1. 边的**源**不在 ``covered_block_addrs`` 里（区内边是折叠的一部分，合法）；
    2. 边的**目标**在 ``covered_block_addrs`` 里；
    3. 目标 **不是** ``start_block_addr``（入口块是唯一允许的进入点）。

    入口块允许被任意外部边指向——那正是 summary 期望被命中的方式；即使
    ``start_instruction_index > 0``，从块首进来也会先逐条执行前缀再在命中点
    折叠，语义不受影响。反过来，continuation 块若被列进 ``covered``（部分覆盖
    形态），它就是一个不折不扣的非入口覆盖块，外部边指向它同样算绕过。

    **为什么单个 natural loop 几乎总是自动通过**：``find_natural_loops`` 的
    body 是从 latch 起沿前驱做反向闭包、只在 header 处停止，所以非 header 的
    body 节点的全部（入口可达）前驱都已经在 body 里。真正会被这条检查抓住的是
    **复合 cluster**（mcopy 的 preamble/align + word 循环 + glue + shr + tail
    拼出来的 covered 区）——它内部那几个循环头的前驱并不天然都落在 covered 内，
    以及那些不参与 ``preds`` 计算的**入口不可达块**发出的边。所以这条检查不是
    形式主义，它守的正是发现期唯一靠拼接得到的那类 covered 区。
    """

    covered = set(summary.covered_block_addrs)
    entry = summary.start_block_addr
    edges: set[Tuple[int, int]] = set()
    for src, targets in succs.items():
        if src in covered:
            continue
        for dst in targets:
            if dst in covered and dst != entry:
                edges.add((src, dst))
    return tuple(sorted(edges))


def require_single_entry(
    summary: X86Summary,
    succs: Mapping[int, Sequence[int]],
    unresolved_sites: Sequence[int] = (),
) -> None:
    """发现/注册期的单入口检查，不满足即 fail-closed 抛异常。

    ``unresolved_sites`` 是 :func:`x86_64.loop_analysis.build_x86_cfg` 报出的
    **静态解析不出目标的跳转**（间接 jmp 等）。它们同样必须拒绝：目标未知就无法
    排除它落在 covered 区的非入口块上，放行等于拿「没看见」冒充「不存在」。只有
    当 covered 区**除入口外没有别的块**时才可以豁免——此时压根不存在可被绕过的
    块，检查平凡成立（同 block summary 走的就是这条）。
    """

    non_entry_covered = set(summary.covered_block_addrs) - {
        summary.start_block_addr
    }
    if not non_entry_covered:
        return
    if unresolved_sites:
        raise SummarySingleEntryError(
            kind=summary.kind,
            entry_addr=summary.entry_addr,
            reason=(
                f"{len(unresolved_sites)} jump site(s) have no statically "
                "resolvable target, so no covered block can be proved "
                "unreachable from outside; first at "
                f"0x{min(unresolved_sites):x}"
            ),
        )
    bypass_edges = find_summary_bypass_edges(summary, succs)
    if bypass_edges:
        raise SummarySingleEntryError(
            kind=summary.kind,
            entry_addr=summary.entry_addr,
            reason=(
                f"{len(bypass_edges)} external edge(s) enter covered blocks "
                f"other than the entry block 0x{summary.start_block_addr:x}"
            ),
            bypass_edges=bypass_edges,
        )


@dataclass(frozen=True)
class SummaryDiscoveryContext:
    blocks: Sequence[X86Block]
    blocks_by_addr: Dict[int, X86Block]
    block_index: Dict[int, int]


class X86SummarySpec(Protocol):
    kind: str

    def discover(
        self,
        ctx: SummaryDiscoveryContext,
        *,
        strict: bool = False,
    ) -> Iterable[X86Summary]:
        ...

    def apply(
        self,
        summary: X86Summary,
        state: SMTState,
        *,
        fresh_prefix: str,
    ) -> SMTState:
        ...


def validate_summary_plugin_mode(mode: str) -> str:
    if mode not in SUMMARY_PLUGIN_MODES:
        modes = ", ".join(sorted(SUMMARY_PLUGIN_MODES))
        raise ValueError(f"summary plugin mode must be one of: {modes}")
    return mode


@dataclass(frozen=True)
class X86SummaryPlugin:
    """One summary spec registered with a runtime-level discovery mode."""

    spec: X86SummarySpec
    mode: str = "fallback"

    def __post_init__(self) -> None:
        object.__setattr__(self, "mode", validate_summary_plugin_mode(self.mode))


class X86SummaryManager:
    """Index, apply, and count already-discovered x86 summaries.

    Discovery is the runtime's job; the manager is a passive container that
    validates the supplied summaries, indexes them by start position, dispatches
    ``apply`` to the owning spec, and tracks per-kind hit statistics.
    """

    def __init__(
        self,
        blocks: Sequence[X86Block],
        specs: Sequence[X86SummarySpec],
        summaries: Sequence[X86Summary],
    ):
        self.blocks = list(blocks)
        self.blocks_by_addr = {block.start_addr: block for block in blocks}
        self.specs = {spec.kind: spec for spec in specs}
        self.summaries: List[X86Summary] = []
        self.summaries_by_start: Dict[SummaryStart, X86Summary] = {}
        self.hit_counts: Dict[str, int] = {}
        self.hit_entries: Dict[str, set[int]] = {}

        self._validate_and_index(summaries)

    def _validate_and_index(self, summaries: Sequence[X86Summary]) -> None:
        covered_keys: Dict[SummaryStart, X86Summary] = {}
        for summary in summaries:
            self._validate_summary(summary)
            if summary.start_key in self.summaries_by_start:
                prior = self.summaries_by_start[summary.start_key]
                raise SummaryMatchError(
                    f"summary start overlap at {summary.start_key}: "
                    f"{prior.kind} and {summary.kind}"
                )
            for key in self._covered_instruction_keys(summary):
                prior = covered_keys.get(key)
                if prior is not None:
                    raise SummaryMatchError(
                        f"summary coverage overlap at {key}: "
                        f"{prior.kind} and {summary.kind}"
                    )
                covered_keys[key] = summary

            self.summaries.append(summary)
            self.summaries_by_start[summary.start_key] = summary

    def _validate_summary(self, summary: X86Summary) -> None:
        if summary.kind not in self.specs:
            raise SummaryMatchError(f"unknown summary kind: {summary.kind}")
        if summary.start_block_addr not in self.blocks_by_addr:
            raise SummaryMatchError(
                f"summary start block is not local: 0x{summary.start_block_addr:x}"
            )
        if summary.start_block_addr not in summary.covered_block_addrs:
            raise SummaryMatchError(
                "summary coverage must include its start block: "
                f"0x{summary.start_block_addr:x}"
            )
        if summary.continuation.block_addr not in self.blocks_by_addr:
            raise SummaryMatchError(
                "summary continuation block is not local: "
                f"0x{summary.continuation.block_addr:x}"
            )
        start_block = self.blocks_by_addr[summary.start_block_addr]
        if not 0 <= summary.start_instruction_index < len(start_block.instructions):
            raise SummaryMatchError(
                f"summary start instruction index out of range: {summary.start_key}"
            )
        cont_block = self.blocks_by_addr[summary.continuation.block_addr]
        if not 0 <= summary.continuation.instruction_index <= len(cont_block.instructions):
            raise SummaryMatchError(
                "summary continuation instruction index out of range: "
                f"{summary.continuation}"
            )
        if not summary.is_cross_block:
            if summary.continuation.instruction_index <= summary.start_instruction_index:
                raise SummaryMatchError(
                    "same-block summary continuation must advance instruction index"
                )
            if (
                start_block.instructions
                and summary.continuation.instruction_index == len(start_block.instructions)
                and start_block.instructions[-1].mnemonic.lower()
                in _BLOCK_TERMINATOR_MNEMONICS
            ):
                raise SummaryMatchError(
                    "same-block summary must not cover final control-transfer instruction"
                )

    def _covered_instruction_keys(self, summary: X86Summary) -> Iterable[SummaryStart]:
        for block_addr in summary.covered_block_addrs:
            block = self.blocks_by_addr.get(block_addr)
            if block is None:
                raise SummaryMatchError(
                    f"summary covered block is not local: 0x{block_addr:x}"
                )

            start = 0
            end = len(block.instructions)
            if block_addr == summary.start_block_addr:
                start = summary.start_instruction_index
            if block_addr == summary.continuation.block_addr:
                end = summary.continuation.instruction_index
            for index in range(start, end):
                yield (block_addr, index)

    def get(self, block_addr: int, instruction_index: int) -> X86Summary | None:
        return self.summaries_by_start.get((block_addr, instruction_index))

    def apply(
        self,
        summary: X86Summary,
        state: SMTState,
        *,
        fresh_prefix: str,
        path_condition=None,
        precondition_timeout_ms: int = 5000,
    ) -> SMTState:
        """把 summary 应用到状态上。

        ``path_condition`` / ``precondition_timeout_ms`` 只传给**声明了这两个
        形参**的 spec —— prove-or-reject 的 summary（copy-loop）需要它们来证明
        自己的适用前提，而不需要前提的 spec（calldataload / mul）保持原签名。
        按 `inspect.signature` 按需注入，避免为了两个参数改动所有 spec。
        """
        import inspect

        spec = self.specs[summary.kind]
        kwargs = {"fresh_prefix": fresh_prefix}
        try:
            parameters = inspect.signature(spec.apply).parameters
        except (TypeError, ValueError):      # 内建/C 实现取不到签名
            parameters = {}
        if "path_condition" in parameters:
            kwargs["path_condition"] = path_condition
        if "precondition_timeout_ms" in parameters:
            kwargs["precondition_timeout_ms"] = precondition_timeout_ms
        return spec.apply(summary, state, **kwargs)

    def record_hit(self, summary: X86Summary) -> None:
        self.hit_counts[summary.kind] = self.hit_counts.get(summary.kind, 0) + 1
        self.hit_entries.setdefault(summary.kind, set()).add(summary.entry_addr)

    def hit_count(self, kind: str) -> int:
        return self.hit_counts.get(kind, 0)

    def hit_entry_set(self, kind: str) -> set[int]:
        return set(self.hit_entries.get(kind, set()))

    def summaries_for_kind(self, kind: str) -> List[X86Summary]:
        return [summary for summary in self.summaries if summary.kind == kind]


class X86SummaryRuntime:
    """Per-plugin discovery plus shared summary execution services."""

    def __init__(
        self,
        blocks: Sequence[X86Block],
        plugins: Sequence[X86SummaryPlugin],
    ):
        self.blocks = list(blocks)
        self.plugins = tuple(plugins)
        self._instance_counter = 0
        self.plugin_modes: Dict[str, str] = {}
        # prove-or-reject：前提未被证明时的处置策略与记录
        self.precondition_policy = "plugin"      # "plugin" | "strict"
        self.precondition_timeout_ms = 5000
        self.precondition_failures: List["SummaryPreconditionError"] = []
        # 应用 summary 时被**假设**（而非证明）的前提。可信 summary 必须让它
        # 保持为空——往 `SMTState` 里补一条未证前提会静默缩小证明域（假绿），
        # 断言 `assumed_premises == []` 就是这条纪律的机器守卫。
        self.assumed_premises: List[str] = []
        self.assumed_premises_by_kind: Dict[str, List[str]] = {}

        ctx = SummaryDiscoveryContext(
            blocks=self.blocks,
            blocks_by_addr={block.start_addr: block for block in self.blocks},
            block_index={block.start_addr: i for i, block in enumerate(self.blocks)},
        )

        enabled_specs: List[X86SummarySpec] = []
        discovered: List[X86Summary] = []
        # Runtime 统一做插件 discovery；Manager 只校验、索引已发现的 summary。
        for plugin in self.plugins:
            if plugin.spec.kind in self.plugin_modes:
                raise SummaryMatchError(
                    f"duplicate summary plugin kind: {plugin.spec.kind}"
                )
            self.plugin_modes[plugin.spec.kind] = plugin.mode

            if plugin.mode == "off":
                continue
            enabled_specs.append(plugin.spec)
            discovered.extend(
                plugin.spec.discover(ctx, strict=plugin.mode == "strict")
            )

        self.manager = X86SummaryManager(self.blocks, enabled_specs, discovered)

    @property
    def summaries(self) -> List[X86Summary]:
        return self.manager.summaries

    def get(self, block_addr: int, instruction_index: int) -> X86Summary | None:
        return self.manager.get(block_addr, instruction_index)

    def exit_guard(self, summary: X86Summary, state: SMTState):
        """Condition under which the raw slice leaves through an exit the
        summary does not model, or None. The executor splits on it: raw
        execution under the guard, the summary under its negation."""
        guard = getattr(self.manager.specs[summary.kind], "exit_guard", None)
        return None if guard is None else guard(summary, state)

    def apply(self, summary: X86Summary, state: SMTState,
              path_condition=None) -> SMTState:
        """应用 summary。前提未被证明时抛 :class:`SummaryPreconditionError`。

        ``path_condition`` 是当前路径的累积约束——prove-or-reject 的 summary
        用它来**证明**自己的适用前提；不传则前提只能靠全局先验证明，通常会
        被拒绝（fail-closed 方向）。
        """
        self._instance_counter += 1
        fresh_prefix = f"{summary.kind}_summary_{self._instance_counter}"
        before_notes = list(
            getattr(state, "summary_assumed_premises", None) or []
        )
        new_state = self.manager.apply(
            summary,
            state,
            fresh_prefix=fresh_prefix,
            path_condition=path_condition,
            precondition_timeout_ms=self.precondition_timeout_ms,
        )
        self._record_assumed_premises(summary, before_notes, new_state)
        self.manager.record_hit(summary)
        return new_state

    def _record_assumed_premises(
        self, summary: X86Summary, before_notes: List[str], new_state: SMTState
    ) -> None:
        """记录本次应用新增的**被假设**前提（正常应为空）。

        可信 summary 走 prove-or-reject：前提要么被当前 path condition 证明、
        要么拒绝应用。任何新增条目都意味着有 summary 在往状态里补未证前提，
        证明域被静默缩小——测试断言 `assumed_premises == []` 守的就是这个。
        """
        after_notes = list(
            getattr(new_state, "summary_assumed_premises", None) or []
        )
        added = after_notes[len(before_notes):]
        if not added:
            return
        kind_notes = self.assumed_premises_by_kind.setdefault(summary.kind, [])
        for note in added:
            if note not in kind_notes:
                kind_notes.append(note)
            if note not in self.assumed_premises:
                self.assumed_premises.append(note)

    def should_fallback_on_precondition(self, kind: str) -> bool:
        """前提被拒后是否回退到逐指令执行原循环。

        ``strict`` 策略下一律不回退（证书模式要求折叠必须成功）；``plugin``
        策略下由该 kind 的插件模式决定——`fallback` 模式的插件允许回退，
        回退语义与不启用 summary 完全一致，因此是健全的。
        """
        return (
            self.precondition_policy == "plugin"
            and self.plugin_modes.get(kind) == "fallback"
        )

    def record_precondition_failure(
        self, error: "SummaryPreconditionError"
    ) -> None:
        """记录一次前提拒绝，供报告与诊断（不改变证明结论）。"""
        self.precondition_failures.append(error)

    def hit_count(self, kind: str) -> int:
        return self.manager.hit_count(kind)

    def hit_entry_set(self, kind: str) -> set[int]:
        return self.manager.hit_entry_set(kind)

    def summaries_for_kind(self, kind: str) -> List[X86Summary]:
        return self.manager.summaries_for_kind(kind)

    def mode_for_kind(self, kind: str) -> str | None:
        return self.plugin_modes.get(kind)
