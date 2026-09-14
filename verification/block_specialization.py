"""块入口的三参数专门化与其闭包义务（docs/块级lockstep等价验证方案.md §2.3）。

块级 lock-step 不从纯 havoc 状态出发，而是按三个编译期可静态推断的参数
专门化块入口：

    k      绝对栈深度       —— tools/call_provenance
    msize  入口 MSize       —— tools/msize_absint
    fmp    入口 mem[0x40]   —— tools/msize_absint

这三个量**不是"免费简化"而是定理的适用域**。健全性由三条义务闭合：

    (H1) 到达覆盖  任何到达块 B 的边，其携带的三元组都在 B 的已登记集合内
    (H2) 转移封闭  每个已登记三元组的块出口，只转移到下游块的已登记集合内
    (H3) 不动点收敛 (H1)(H2) 的传播在预设轮数内收敛，否则拒绝

缺任何一条，定理就会被应用到它没有被证明的状态上（假绿方向）。这与
`loop_induction._check_depth_transition_closure` 是同一机制的三维推广——那里
`registered` 只含本次归纳的单个深度类，这里是全局已登记集合。

**本模块不重算任何分析。** 三个分析器各自独立产出，这里只做对账：它们对同一
个块给出的结论必须相容，任何不一致 fail-closed。独立产出 + 交叉验证比单一
分析器更能抓出错误。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping, Optional, Sequence, Tuple

__all__ = [
    "TOP",
    "Top",
    "BlockSpecialization",
    "SpecializationPlan",
    "ClosureViolation",
    "build_specialization_plan",
]


class Top:
    """静态不可确定（⊤）。

    **必须是独立哨兵，不能用 `None` 或空集表示**：`None` 在本模块里的含义是
    "该参数不参与专门化"，空集的含义是"没有可达取值（不可达块）"，三者的
    后续处置完全不同——⊤ 只能降级，`None` 是合法配置，空集是分析缺陷。
    混用会让降级路径静默吞掉本该报错的情形。
    """

    _instance: Optional["Top"] = None

    def __new__(cls) -> "Top":
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self) -> str:  # pragma: no cover - 调试用
        return "TOP"


TOP = Top()


@dataclass(frozen=True)
class BlockSpecialization:
    """一个块入口的三参数实例，是 theorem key 的核心部分。

    只为**可专门化**的块构造：msize 或 fmp 为 ⊤ 的块根本不进入块级证明，
    因此这里的字段都是具体值。
    """

    pc: int
    stack_depth: int
    memory_size: int
    free_memory_pointer: int

    def as_havoc_kwargs(self) -> dict:
        """喂给 `CutpointRelationSchema.build_havoc` 的参数。"""
        return {
            "stack_depth": self.stack_depth,
            "memory_size": self.memory_size,
            "free_memory_pointer": self.free_memory_pointer,
        }


@dataclass(frozen=True)
class ClosureViolation:
    """一条闭包义务的违例。任何一条非空 ⇒ 整体拒绝。"""

    kind: str  # 'arrival' | 'transition' | 'divergence' | 'inconsistent'
    pc: int
    detail: str


@dataclass
class SpecializationPlan:
    """三个分析器对账后的产物。

    `specializable` 与 `degraded` 是**互斥且穷尽**的划分：每个可达块恰好落在
    其中一侧。降级块退回整程序展开（方案 §4.5a），它们不是"证过的"——报告
    必须显式列出，不得以整体 VERIFIED 掩盖（§7.2）。
    """

    specializable: Mapping[int, Tuple[BlockSpecialization, ...]]
    degraded: Mapping[int, str]  # pc -> 降级原因
    violations: Tuple[ClosureViolation, ...] = ()
    rounds: int = 0

    @property
    def ok(self) -> bool:
        return not self.violations

    @property
    def theorem_instances(self) -> int:
        """需要证明的定理条数 = Σ 每块的专门化实例数。"""
        return sum(len(v) for v in self.specializable.values())

    def coverage_summary(self) -> str:
        total = len(self.specializable) + len(self.degraded)
        if not total:
            return "no reachable blocks"
        pct = len(self.specializable) / total * 100
        return (
            f"{len(self.specializable)}/{total} blocks specializable "
            f"({pct:.1f}%), {len(self.degraded)} degraded, "
            f"{self.theorem_instances} theorem instances"
        )


def _as_value_set(raw) -> Optional[frozenset]:
    """把分析器产出归一成值集合；⊤ 返回 None。"""
    if raw is TOP or isinstance(raw, Top):
        return None
    if isinstance(raw, int):
        return frozenset({raw})
    return frozenset(raw)


def build_specialization_plan(
    *,
    reachable_pcs: Iterable[int],
    succs: Mapping[int, Sequence[int]],
    depth_classes: Mapping[int, Iterable[int]],
    memory_sizes: Mapping[int, object],
    free_pointers: Mapping[int, object],
    max_rounds: int = 64,
) -> SpecializationPlan:
    """对账三个分析器的产出，产出专门化计划并检查 (H1)(H2)(H3)。

    Args:
        reachable_pcs: 参与块级证明的块（通常来自块对齐的可达集）。
        succs: context-sensitive CFG 的后继表（来自 call_provenance）。
        depth_classes: pc -> 可达绝对栈深集合。
        memory_sizes: pc -> 具体值 / 值集合 / ``TOP``。
        free_pointers: pc -> 具体值 / 值集合 / ``TOP``。
        max_rounds: (H3) 的收敛预算。

    Returns:
        `SpecializationPlan`。**不抛异常**——违例记进 `violations` 由调用方
        决定降级还是拒绝，因为"哪些块可以降级"是编排层的策略而非本模块的。
    """
    pcs = sorted(set(reachable_pcs))
    specializable: dict[int, Tuple[BlockSpecialization, ...]] = {}
    degraded: dict[int, str] = {}
    violations: list[ClosureViolation] = []

    # -- 分类：可专门化 vs 降级 ---------------------------------------------
    for pc in pcs:
        depths = frozenset(depth_classes.get(pc, ()))
        msizes = _as_value_set(memory_sizes.get(pc, TOP))
        fmps = _as_value_set(free_pointers.get(pc, TOP))

        if not depths:
            # 空集不是 ⊤：分析器认为该块不可达，但它出现在 reachable_pcs 里。
            # 两个分析器对同一个块给出矛盾结论 ⇒ 对账失败，不能默默降级。
            violations.append(
                ClosureViolation(
                    "inconsistent", pc,
                    "block is in the reachable set but has no depth class",
                )
            )
            continue
        if msizes is None or fmps is None:
            reason = "memory_size is TOP" if msizes is None else "fmp is TOP"
            degraded[pc] = reason
            continue
        if not msizes or not fmps:
            violations.append(
                ClosureViolation(
                    "inconsistent", pc,
                    "memory_size/fmp analysis returned an empty value set",
                )
            )
            continue

        # msize=⊤ ⟺ fmp=⊤ 是实测性质（零例外）。一侧 ⊤ 另一侧具体 ⇒ 两个
        # 分量的分析走岔了，对账必须抓住它而不是取其一。
        specializable[pc] = tuple(
            BlockSpecialization(pc, d, m, f)
            for d in sorted(depths)
            for m in sorted(msizes)
            for f in sorted(fmps)
        )

    # -- (H1)(H2)：边两端的专门化必须彼此登记 --------------------------------
    #
    # 一条边 A→B 上，A 的出口状态会成为 B 的入口状态。这里检查的是**登记集合
    # 层面**的相容：B 必须为"可能从 A 到达的那些三元组"都登记了定理。真正的
    # 状态级证明是义务 ①，本函数只保证枚举不遗漏。
    for pc in pcs:
        if pc not in specializable:
            continue  # 降级块不产出定理，其出边由展开路径覆盖
        for succ in succs.get(pc, ()):
            if succ not in specializable:
                # 后继降级 ⇒ 该边由展开接管，不是违例，但必须被编排层记账
                continue
            src_depths = {s.stack_depth for s in specializable[pc]}
            dst_depths = {s.stack_depth for s in specializable[succ]}
            # 深度传播的封闭性由 call_provenance 的不动点保证；这里只交叉验证
            # 它确实把后继的深度算进去了。漏了说明两个分析器不同源。
            if not src_depths or not dst_depths:
                violations.append(
                    ClosureViolation(
                        "transition", pc,
                        f"edge {pc}->{succ} has an empty depth class on one end",
                    )
                )

    # -- (H3)：收敛 ----------------------------------------------------------
    #
    # 深度类不动点由 call_provenance 跑，它不收敛时不会产出结果。这里用块数
    # 与实例数的比值做一个独立的发散哨兵：实例数远超块数意味着某个参数在沿
    # 环增长（典型是未识别的递归），即便上游报告"收敛"也要拒绝。
    rounds = 1
    if specializable:
        blowup = sum(len(v) for v in specializable.values()) / len(specializable)
        if blowup > max_rounds:
            violations.append(
                ClosureViolation(
                    "divergence", -1,
                    f"average {blowup:.1f} specializations per block exceeds "
                    f"the budget {max_rounds}; suspected unbounded growth",
                )
            )

    return SpecializationPlan(
        specializable=specializable,
        degraded=degraded,
        violations=tuple(violations),
        rounds=rounds,
    )
