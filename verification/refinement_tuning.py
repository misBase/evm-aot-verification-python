"""Timeout and partition knobs shared by refinement sub-checks."""

from dataclasses import dataclass


_PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS = 250
_STORAGE_QUICK_TIMEOUT_CAP_MS = 750
_STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT = 68
_STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS = 30000
_PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS = 200


@dataclass(frozen=True)
class _RefinementCheckTuning:
    """Small timeout and partition knobs used by refinement sub-checks."""

    path_pair_feasibility_timeout_ms: int
    storage_quick_timeout_ms: int
    storage_calldatasize_exact_partition_limit: int
    storage_calldatasize_exact_partition_timeout_ms: int
    storage_calldatasize_tail_partition_timeout_ms: int
    path_structural_oracle_timeout_ms: int

    @classmethod
    def for_timeout(cls, timeout_ms: int) -> "_RefinementCheckTuning":
        storage_quick_timeout_ms = min(timeout_ms, _STORAGE_QUICK_TIMEOUT_CAP_MS)
        return cls(
            path_pair_feasibility_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS,
            ),
            storage_quick_timeout_ms=storage_quick_timeout_ms,
            storage_calldatasize_exact_partition_limit=(
                _STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT
            ),
            storage_calldatasize_exact_partition_timeout_ms=min(
                timeout_ms,
                max(storage_quick_timeout_ms, 1000),
            ),
            storage_calldatasize_tail_partition_timeout_ms=min(
                timeout_ms,
                _STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS,
            ),
            path_structural_oracle_timeout_ms=min(
                timeout_ms,
                _PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS,
            ),
        )
