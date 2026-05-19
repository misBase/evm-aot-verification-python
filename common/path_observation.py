"""Neutral path-observation containers for program-level semantics."""

from dataclasses import dataclass
from typing import Any

OBSERVATION_KEYS = frozenset({
    "condition",
    "offset",
    "length",
    "memory",
    "base_addr",
    "has_return_data",
    "storage",
    "transient_storage",
})


@dataclass(frozen=True)
class PathObservation:
    """Observable result of one terminal execution path."""

    condition: Any
    offset: Any
    length: Any
    memory: Any
    base_addr: Any
    has_return_data: Any
    storage: Any
    transient_storage: Any

    def __getitem__(self, key: str) -> Any:
        if key not in OBSERVATION_KEYS:
            raise KeyError(key)
        return getattr(self, key)

    def get(self, key: str, default: Any = None) -> Any:
        """Dictionary-compatible accessor for existing checkers."""
        if key not in OBSERVATION_KEYS:
            return default
        return getattr(self, key)

    def as_dict(self) -> dict[str, Any]:
        """Return the legacy dict shape consumed by ``RefinementChecker``."""
        return {
            "condition": self.condition,
            "offset": self.offset,
            "length": self.length,
            "memory": self.memory,
            "base_addr": self.base_addr,
            "has_return_data": self.has_return_data,
            "storage": self.storage,
            "transient_storage": self.transient_storage,
        }


@dataclass(frozen=True)
class PathSemantics:
    """Result of a path-sensitive program execution."""

    global_states: list[Any]
    observations: list[PathObservation]
    merged_state: Any = None

    def as_result_dicts(self) -> list[dict[str, Any]]:
        """Return observations in the legacy result-dict shape."""
        return [observation.as_dict() for observation in self.observations]
