"""Generic x86 slice summary framework."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Protocol, Sequence, Tuple

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
    ) -> SMTState:
        return self.specs[summary.kind].apply(
            summary,
            state,
            fresh_prefix=fresh_prefix,
        )

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

    def apply(self, summary: X86Summary, state: SMTState) -> SMTState:
        self._instance_counter += 1
        fresh_prefix = f"{summary.kind}_summary_{self._instance_counter}"
        new_state = self.manager.apply(
            summary,
            state,
            fresh_prefix=fresh_prefix,
        )
        self.manager.record_hit(summary)
        return new_state

    def hit_count(self, kind: str) -> int:
        return self.manager.hit_count(kind)

    def hit_entry_set(self, kind: str) -> set[int]:
        return self.manager.hit_entry_set(kind)

    def summaries_for_kind(self, kind: str) -> List[X86Summary]:
        return self.manager.summaries_for_kind(kind)

    def mode_for_kind(self, kind: str) -> str | None:
        return self.plugin_modes.get(kind)
