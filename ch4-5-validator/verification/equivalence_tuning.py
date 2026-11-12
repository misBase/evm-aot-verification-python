"""Timeout and partition knobs shared by equivalence sub-checks."""

from dataclasses import dataclass


_PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS = 250
_PATH_PAIR_FEASIBILITY_RESCUE_TIMEOUT_CAP_MS = 5000
_PATH_PAIR_CALLDATASIZE_EXACT_PARTITION_LIMIT = 100
_PATH_PAIR_CALLDATASIZE_EXACT_PARTITION_TIMEOUT_CAP_MS = 10000
_PATH_PAIR_CALLDATASIZE_TAIL_PARTITION_TIMEOUT_CAP_MS = 5000
_STORAGE_QUICK_TIMEOUT_CAP_MS = 750
_STORAGE_PATH_FEASIBILITY_RESCUE_TIMEOUT_CAP_MS = 5000
_STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT = 68
_STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS = 30000
_STORAGE_STORE_NOOP_TIMEOUT_CAP_MS = 20000
_PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS = 200
_MEMORY_UNROLL_BYTE_LIMIT = 256
_MEMORY_UNROLL_BYTE_TIMEOUT_CAP_MS = 10000
_MEMORY_CHUNK_TIMEOUT_CAP_MS = 2500
_MEMORY_CHUNK_FALLBACK_STREAK_LIMIT = 2


@dataclass(frozen=True)
class _EquivalenceCheckTuning:
    """Small timeout and partition knobs used by equivalence sub-checks."""

    path_pair_feasibility_timeout_ms: int
    path_pair_feasibility_rescue_timeout_ms: int
    path_pair_calldatasize_exact_partition_limit: int
    path_pair_calldatasize_exact_partition_timeout_ms: int
    path_pair_calldatasize_tail_partition_timeout_ms: int
    storage_quick_timeout_ms: int
    storage_path_feasibility_rescue_timeout_ms: int
    storage_calldatasize_exact_partition_limit: int
    storage_calldatasize_exact_partition_timeout_ms: int
    storage_calldatasize_tail_partition_timeout_ms: int
    storage_store_noop_timeout_ms: int
    path_structural_oracle_timeout_ms: int
    memory_unroll_byte_limit: int
    memory_unroll_byte_timeout_ms: int
    memory_chunk_timeout_ms: int
    memory_chunk_fallback_streak_limit: int

    @classmethod
    def for_timeout(cls, timeout_ms: int) -> "_EquivalenceCheckTuning":
        storage_quick_timeout_ms = min(timeout_ms, _STORAGE_QUICK_TIMEOUT_CAP_MS)
        return cls(
            path_pair_feasibility_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_FEASIBILITY_TIMEOUT_CAP_MS,
            ),
            path_pair_feasibility_rescue_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_FEASIBILITY_RESCUE_TIMEOUT_CAP_MS,
            ),
            path_pair_calldatasize_exact_partition_limit=(
                _PATH_PAIR_CALLDATASIZE_EXACT_PARTITION_LIMIT
            ),
            path_pair_calldatasize_exact_partition_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_CALLDATASIZE_EXACT_PARTITION_TIMEOUT_CAP_MS,
            ),
            path_pair_calldatasize_tail_partition_timeout_ms=min(
                timeout_ms,
                _PATH_PAIR_CALLDATASIZE_TAIL_PARTITION_TIMEOUT_CAP_MS,
            ),
            storage_quick_timeout_ms=storage_quick_timeout_ms,
            storage_path_feasibility_rescue_timeout_ms=min(
                timeout_ms,
                _STORAGE_PATH_FEASIBILITY_RESCUE_TIMEOUT_CAP_MS,
            ),
            storage_calldatasize_exact_partition_limit=(
                _STORAGE_CALLDATASIZE_EXACT_PARTITION_LIMIT
            ),
            storage_calldatasize_exact_partition_timeout_ms=min(
                timeout_ms,
                max(storage_quick_timeout_ms, 60000),
            ),
            storage_calldatasize_tail_partition_timeout_ms=min(
                timeout_ms,
                _STORAGE_CALLDATASIZE_TAIL_TIMEOUT_CAP_MS,
            ),
            storage_store_noop_timeout_ms=min(
                timeout_ms,
                _STORAGE_STORE_NOOP_TIMEOUT_CAP_MS,
            ),
            path_structural_oracle_timeout_ms=min(
                timeout_ms,
                _PATH_STRUCTURAL_ORACLE_TIMEOUT_CAP_MS,
            ),
            memory_unroll_byte_limit=_MEMORY_UNROLL_BYTE_LIMIT,
            memory_unroll_byte_timeout_ms=min(
                timeout_ms,
                _MEMORY_UNROLL_BYTE_TIMEOUT_CAP_MS,
            ),
            memory_chunk_timeout_ms=min(
                timeout_ms,
                _MEMORY_CHUNK_TIMEOUT_CAP_MS,
            ),
            memory_chunk_fallback_streak_limit=_MEMORY_CHUNK_FALLBACK_STREAK_LIMIT,
        )
