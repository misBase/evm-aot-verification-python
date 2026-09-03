"""x86 summary plugin registry."""

from __future__ import annotations

from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Callable, Mapping, Sequence

from x86_64.models import X86Block

from .base import X86SummaryPlugin, X86SummaryRuntime, X86SummarySpec
from .calldataload import CALLDATALOAD_SUMMARY_KIND, CallDataLoadSummarySpec
from .copy_loop import COPY_LOOP_SUMMARY_KIND, CopyLoopSummarySpec
from .mul import MUL_SUMMARY_KIND, MulSummarySpec


# 内置 summary 注册表：key 是配置里使用的 kind，value 是 spec 类。
# mode 是注册期策略，统一在组装 plugin 时附加，不由 spec 自己关心。
BUILTIN_SUMMARY_SPECS: Mapping[str, Callable[[], X86SummarySpec]] = {
    CALLDATALOAD_SUMMARY_KIND: CallDataLoadSummarySpec,
    COPY_LOOP_SUMMARY_KIND: CopyLoopSummarySpec,
    MUL_SUMMARY_KIND: MulSummarySpec,
}


@dataclass(frozen=True)
class X86SummaryConfig:
    """Configuration for optional x86 summary plugin registration.

    ``builtin_modes`` maps a builtin summary ``kind`` to its discovery mode
    (off/fallback/strict); only the named kinds are enabled.

    ``prove_mul_hits`` 控制 MUL summary 的 per-hit glue 证明（fail-closed，
    证明失败时 fallback 模式同样报错）；默认开启，单次实测 10-40ms。
    """

    builtin_modes: Mapping[str, str] = field(default_factory=dict)
    prove_mul_hits: bool = True
    mul_proof_timeout_ms: int = 10_000

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
    def enabled(
        cls,
        *,
        prove_mul_hits: bool = True,
        mul_proof_timeout_ms: int = 10_000,
        **builtin_modes: str,
    ) -> "X86SummaryConfig":
        # keyword-only 分离：除显式具名参数外，其余 kwargs 都是 summary kind。
        return cls(
            builtin_modes=builtin_modes,
            prove_mul_hits=prove_mul_hits,
            mul_proof_timeout_ms=mul_proof_timeout_ms,
        )


# 显式信任的 summary 配置：启用 trusted CALLDATALOAD/MUL 加速。
# 集中在一处，便于全局调档（含一键关闭做对照验证），同时仍显式可审计——
# 调用方传 TRUSTED_SUMMARY_CONFIG 即可看出本次验证信任了哪些切片。
TRUSTED_SUMMARY_CONFIG = X86SummaryConfig.enabled(
    calldataload="fallback",
    mul="fallback",
)

# 追加 Tier 2 copy-loop 折叠的配置。**默认配置刻意不含它**：copy-loop 会把整个
# 拷贝循环换成闭式语义，是比 CALLDATALOAD/MUL 大得多的一步，先让调用方显式选择，
# 也让既有全量回归保持在原基线上。
#
# 折叠是否安全的依据在 docs/循环处理增强方案.md §5：这四条 opcode
# （CALLDATACOPY/CODECOPY/RETURNDATACOPY/MCOPY）的 gas 全部在**循环之外**由
# `checkMemoryAndCalcDynamicGas*` 前言扣完，循环体内一条 gas 指令都没有，因此
# 跳过循环体不会让两侧 gas 分叉。
TRUSTED_SUMMARY_CONFIG_WITH_TIER2 = X86SummaryConfig.enabled(
    calldataload="fallback",
    mul="fallback",
    copy_loop="fallback",
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
        if kind == MUL_SUMMARY_KIND:
            spec = MulSummarySpec(
                prove_hits=config.prove_mul_hits,
                proof_timeout_ms=config.mul_proof_timeout_ms,
            )
        else:
            spec = spec_factory()
        plugins.append(X86SummaryPlugin(spec, mode=mode))
    return X86SummaryRuntime(blocks, plugins)
