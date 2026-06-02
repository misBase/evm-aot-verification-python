"""x86 summary plugin registry."""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Callable, Mapping, Sequence

from x86_64.models import X86Block

from .base import X86SummaryPlugin, X86SummaryRuntime, X86SummarySpec
from .calldataload import CALLDATALOAD_SUMMARY_KIND, CallDataLoadSummarySpec


# 内置 summary 注册表：key 是配置里使用的 kind，value 是 spec 类。
# mode 是注册期策略，统一在组装 plugin 时附加，不由 spec 自己关心。
BUILTIN_SUMMARY_SPECS: Mapping[str, Callable[[], X86SummarySpec]] = {
    CALLDATALOAD_SUMMARY_KIND: CallDataLoadSummarySpec,
}


@dataclass(frozen=True)
class X86SummaryConfig:
    """Configuration for optional x86 summary plugin registration.

    ``builtin_modes`` maps a builtin summary ``kind`` to its discovery mode
    (off/fallback/strict); only the named kinds are enabled.
    """

    builtin_modes: Mapping[str, str] = field(default_factory=dict)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "builtin_modes",
            MappingProxyType(dict(self.builtin_modes)),
        )

    @classmethod
    def disabled(cls) -> "X86SummaryConfig":
        return cls()

    @classmethod
    def enabled(cls, **builtin_modes: str) -> "X86SummaryConfig":
        return cls(builtin_modes=builtin_modes)


# 显式信任的 summary 配置：启用 trusted CALLDATALOAD 加速。
# 集中在一处，便于全局调档（含一键关闭做对照验证），同时仍显式可审计——
# 调用方传 TRUSTED_SUMMARY_CONFIG 即可看出本次验证信任了哪些切片。
TRUSTED_SUMMARY_CONFIG = X86SummaryConfig.enabled(
    calldataload="fallback",
)


def build_x86_summary_runtime(
    blocks: Sequence[X86Block],
    *,
    summary_config: X86SummaryConfig | None = None,
) -> X86SummaryRuntime:
    """Build an x86 summary runtime from an explicit summary config.

    No summary plugin is enabled by default. Builtin plugins are registered
    only when named in ``summary_config.builtin_modes``.
    """
    config = (
        summary_config
        if summary_config is not None
        else X86SummaryConfig.disabled()
    )
    plugins = []
    for kind, mode in config.builtin_modes.items():
        spec_factory = BUILTIN_SUMMARY_SPECS.get(kind)
        if spec_factory is None:
            known = ", ".join(sorted(BUILTIN_SUMMARY_SPECS)) or "<none>"
            raise ValueError(
                f"unknown builtin x86 summary plugin: {kind} "
                f"(known: {known})"
            )
        plugins.append(X86SummaryPlugin(spec_factory(), mode=mode))
    return X86SummaryRuntime(blocks, plugins)
