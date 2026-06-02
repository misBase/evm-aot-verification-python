"""x86 summary framework.

Summaries are trusted replacements for compiler-generated instruction slices.
They must not cover GO bridge / call-site machinery unless the summary itself
models the bridge and preserves call-site mapping semantics.
"""

from .base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    SummaryMatchError,
    X86Summary,
    X86SummaryManager,
    X86SummaryPlugin,
    X86SummaryRuntime,
    X86SummarySpec,
)
from .registry import (
    TRUSTED_SUMMARY_CONFIG,
    X86SummaryConfig,
    build_x86_summary_runtime,
)

__all__ = [
    "SummaryContinuation",
    "SummaryDiscoveryContext",
    "SummaryMatchError",
    "X86Summary",
    "X86SummaryManager",
    "X86SummaryPlugin",
    "X86SummaryRuntime",
    "X86SummarySpec",
    "X86SummaryConfig",
    "TRUSTED_SUMMARY_CONFIG",
    "build_x86_summary_runtime",
]
