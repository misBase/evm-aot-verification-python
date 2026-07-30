"""程序级语义使用的中立 path-observation 容器。"""

from dataclasses import dataclass, field
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
    "status_code",
    "gas",
})


@dataclass(frozen=True)
class PathObservation:
    """一条终止执行路径的可观察结果。"""

    condition: Any
    offset: Any
    length: Any
    memory: Any
    base_addr: Any
    has_return_data: Any
    storage: Any
    transient_storage: Any
    # 必填：给默认值会让漏传的 producer 一路静默到 refinement 检查里变成假绿。
    status_code: Any
    # 该终止路径的剩余 gas（EVM 侧 evm_gas.Gas / x86 侧 callengine_gas_remaining）。
    # 同样必填、同样的理由。值可以是 None，但那必须是「本次运行没建模 gas」的显式
    # 表态（由 gas_modeling_enabled 决定），不能是 producer 忘了传——所以不给默认值，
    # 让漏传在构造处就 TypeError，而不是漂到 gas 检查里变成静默 skip。
    gas: Any

    def __getitem__(self, key: str) -> Any:
        if key not in OBSERVATION_KEYS:
            raise KeyError(key)
        return getattr(self, key)

    def get(self, key: str, default: Any = None) -> Any:
        """兼容现有 checker 的 dict 风格访问器。"""
        if key not in OBSERVATION_KEYS:
            return default
        return getattr(self, key)

    def as_dict(self) -> dict[str, Any]:
        """返回 ``RefinementChecker`` 仍在使用的旧 dict 形状。"""
        return {
            "condition": self.condition,
            "offset": self.offset,
            "length": self.length,
            "memory": self.memory,
            "base_addr": self.base_addr,
            "has_return_data": self.has_return_data,
            "storage": self.storage,
            "transient_storage": self.transient_storage,
            "status_code": self.status_code,
            "gas": self.gas,
        }


@dataclass(frozen=True)
class PathCoverageCertificate:
    """path-observation 集合覆盖其建模输入的证据。"""

    complete: bool
    reason: str
    source: str = ""
    details: tuple[tuple[str, Any], ...] = ()

    @classmethod
    def unknown(cls, reason: str = "no coverage certificate") -> "PathCoverageCertificate":
        return cls(complete=False, reason=reason)

    @classmethod
    def by_construction(
        cls,
        reason: str,
        *,
        source: str = "",
        details: tuple[tuple[str, Any], ...] = (),
    ) -> "PathCoverageCertificate":
        return cls(
            complete=True,
            reason=reason,
            source=source,
            details=details,
        )


@dataclass(frozen=True)
class PathSemantics:
    """路径敏感程序执行的结果。"""

    global_states: list[Any]
    observations: list[PathObservation]
    merged_state: Any = None
    coverage: PathCoverageCertificate = field(
        default_factory=PathCoverageCertificate.unknown
    )

    def as_result_dicts(self) -> list[dict[str, Any]]:
        """以旧 result-dict 形状返回 observation。"""
        return [observation.as_dict() for observation in self.observations]
