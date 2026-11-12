"""Tier 1 循环证书：可被主证明**消费**的证明产物（docs/循环处理增强方案.md §4.5）。

归纳的产物不该只是一个 `proved: bool`。主验证器要在 cutpoint 上引用它，就必须
能核对：这条定理是在哪个 R 版本、哪个深度类、哪些调用方前提下证的，以及**终止
性证据是否齐备**。

两层拆分：

- :class:`Tier1LoopTheorem` —— caller-independent 的 `R ⇒ 一轮决策对齐 / 回边
  保持 / 出口保持 / gas 递减`；
- :class:`Tier1LoopCertificate` —— 把定理绑定到具体的 caller assumptions、
  arrival path condition 与 Base 证明上。

与 develop-cycle 版的两处关键差异：

1. **没有 envelope 字段**。那边把 gas 排除在 R 之外、用 no-OOG envelope 压死
   OOG 分支，于是证书要额外记录 envelope 是否被实例化。develop 的 gas 已进 R
   （`CutpointRelationSchema` 的 `gas` 分量），envelope 取消，这套记录随之消失。
2. **`proved` 强制要求终止与深度类证据**。§4.5 要求六项终止前提作为证据进证书
   ——只写在文档里的前提不是主证明可消费的证据。因此证书的 `proved` 比
   `LoopInductionResult.proved`（只表示锁步同步）更严格。
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from z3 import simplify

from common.identity import callable_identity  # noqa: F401  (re-export)
from evm_ir.models import EVMBlock
from verification.cutpoint_relation import CUTPOINT_STRUCTURAL_SITES
from verification.loop_induction import LoopInductionResult
from x86_64.models import X86Block


def _digest(value) -> str:
    return hashlib.sha256(repr(value).encode("utf-8")).hexdigest()


def fingerprint_evm_blocks(blocks: Sequence[EVMBlock]) -> str:
    payload = []
    for block in blocks:
        operations = []
        for op in block.operations:
            operations.append(
                (
                    op.kind,
                    op.pc,
                    op.immediate,
                    tuple(op.immediate_set or ()),
                    bool(op.is_static),
                    op.param,
                )
            )
        payload.append(
            (
                block.pc,
                getattr(block, "min_depth", None),
                getattr(block, "max_depth", None),
                # **必须含 static_gas**：gas 现在是 R 的分量、②(e) 还用它做
                # ranking function。指令序列相同而 static_gas 不同的两个程序
                # 若指纹相同，第二次就会复用定理，跳过唯一能发现循环体 gas
                # 差异的 ② —— 假绿。
                getattr(block, "static_gas", None),
                # 合法跳转目标集合影响控制流，同样进指纹
                bool(getattr(block, "is_jump_target", False)),
                bool(getattr(block, "is_stop", False)),
                tuple(operations),
            )
        )
    return _digest(tuple(payload))


def fingerprint_x86_blocks(blocks: Sequence[X86Block]) -> str:
    payload = tuple(
        (
            block.start_addr,
            tuple(
                (insn.addr, bytes(insn.bytes).hex(), insn.mnemonic, insn.op_str)
                for insn in block.instructions
            ),
        )
        for block in blocks
    )
    return _digest(payload)


def fingerprint_assumptions(assumptions: Iterable[object]) -> str:
    normalized = sorted(simplify(assumption).sexpr() for assumption in assumptions)
    return _digest(tuple(normalized))


def fingerprint_aot_profile(profile) -> str:
    """AOT profile 的完整指纹。

    **只取 `offsets` 不够**：`status_codes` / `resumable_statuses` /
    builtin & host 函数映射 / stack bias 都直接改变 x86 段执行与 host 分发语义，
    两个 offsets 相同而这些不同的 profile 若共用键，第二次验证就会采用在**另一套
    ABI 语义**下证出的定理。
    """
    if profile is None:
        return _digest(None)

    def _sorted_map(name):
        value = getattr(profile, name, None)
        if value is None:
            return None
        try:
            return tuple(sorted(dict(value).items()))
        except (TypeError, ValueError):
            return repr(value)

    return _digest(
        (
            _sorted_map("offsets"),
            _sorted_map("status_codes"),
            tuple(sorted(getattr(profile, "resumable_statuses", ()) or ())),
            _sorted_map("builtin_functions"),
            _sorted_map("host_functions"),
            getattr(profile, "stack_sp_bias_limbs", None),
        )
    )


def fingerprint_summary_config(summary_config) -> str:
    if summary_config is None:
        return _digest(None)
    modes = tuple(sorted(dict(summary_config.builtin_modes).items()))
    return _digest(
        (
            modes,
            getattr(summary_config, "prove_mul_hits", None),
            getattr(summary_config, "mul_proof_timeout_ms", None),
            getattr(summary_config, "prove_div_hits", None),
            getattr(summary_config, "div_proof_timeout_ms", None),
        )
    )


@dataclass(frozen=True)
class Tier1LoopTheoremKey:
    evm_program: str
    x86_program: str
    evm_header: int
    x86_header: int
    evm_exits: Tuple[int, ...]
    x86_exits: Tuple[int, ...]
    depth_class: int
    relation: str
    summary_config: str
    aot_profile: str
    # The inferred lowering map is navigation evidence rather than a semantic
    # axiom, but a theorem proved for one validated region partition must not be
    # reused after that partition changes.
    lowering_map: str = ""


@dataclass(frozen=True)
class Tier1LoopApplicationKey:
    theorem: Tier1LoopTheoremKey
    caller_assumptions: str
    entry_condition: str


@dataclass(frozen=True)
class Tier1LoopTheorem:
    """Caller-independent R-preservation theorem for one depth class."""

    key: Tier1LoopTheoremKey
    induction: LoopInductionResult
    query_count: int

    @property
    def proved(self) -> bool:
        return self.induction.proved


@dataclass(frozen=True)
class Tier1LoopCertificate:
    """One theorem applied under a concrete caller precondition/Base proof."""

    key: Tier1LoopApplicationKey
    theorem: Tier1LoopTheorem
    base: LoopInductionResult
    # ③ 出口查询：从「出口处 R 成立」继续到下一 cutpoint 或终止。
    # **不是可选项**——循环完全可以保持 R、gas 递减并正常退出，而退出**之后**
    # 的后缀产生不同的 status / 返回值 / storage。缺了它，证书只覆盖「循环本身」
    # 却被当成「这条路径已验」，那是假绿。
    exit_query: Optional[LoopInductionResult] = None
    notes: Tuple[str, ...] = ()
    # 已核对的 cutpoint 结构前提覆盖点（§4.5.6）。由编排层汇总 ①②③ 各自负责
    # 的那几处；五处不齐 ⇒ 证书不成立。
    structural_premise_sites: Tuple[str, ...] = ()
    # 是否要求终止性证据。留 True 时 `proved` 会强制检查 ②(e) 与深度类完备性；
    # 只关心「锁步同步」的调用方可显式关掉，但结论就**不含终止性**。
    require_termination: bool = True

    @property
    def proved(self) -> bool:
        """证书成立 ⟺ 定理 + Base + ③出口 + （按需的）终止与深度类证据。

        **这里刻意比 `LoopInductionResult.proved` 更严**：那个字段只表示锁步
        同步（②a–d）成立，而证书是给主证明消费的，必须把 §4.2 的 ③ 出口义务
        与 §4.5 要求的终止证据、深度类完备性一并纳入——否则「同步已证」会冒充
        「整条路径已验」。
        """
        if not (self.theorem.proved and self.base.proved):
            return False
        if self.exit_query is None or not self.exit_query.proved:
            return False
        # **深度类闭合与终止性无关**，不能被 `require_termination=False` 跳过：
        # 它是「重复应用同一条归纳定理」的必要条件——latch 逃逸到未登记的深度类
        # 时，下一轮就在一个定理从未覆盖的 class 上复用它。放弃终止性只该放弃
        # 终止性。
        if not self.depth_classes_complete:
            return False
        # **结构前提与终止性无关**，同样不能被 `require_termination=False` 跳过：
        # 「两侧均 running」是"这些状态确实是 cutpoint 到达状态"的前提，缺了它，
        # 一个已终止的状态就能冒充到达状态把 R 的义务变成空真的。
        if not self.structural_premises_complete:
            return False
        if not self.require_termination:
            return True
        return self.termination_complete

    @property
    def structural_premises_complete(self) -> bool:
        """§4.5.6 的五处覆盖点是否齐备。

        只写「Base 和 application」两处不够：status 不进 R 的等式分量之后，
        latch 再应用 / 正常 exit 边 / ③ 进入下一 cutpoint 这三处仍可能靠
        `create_initial_state` 的初值偷换掉「两侧均 running」。
        """
        return set(CUTPOINT_STRUCTURAL_SITES) <= set(
            self.structural_premise_sites
        )

    @property
    def termination_complete(self) -> bool:
        """②(e) 的六项前提全部到位才算数。

        本处直接证的只有两项（每条可行 latch arm 的 gas 严格递减、无位向量
        回绕的依据）；其余四项由别处兑现，记在
        `TerminationEvidence.external_premises` 上并带 `discharged` 标志。

        **必须检查 `pending_premises`**：若只看前两项，「内层循环已处理」
        「所有 SCC 已切断」「无 stuttering」这些前提没落实时，局部的 gas
        递减结论会被直接升格成终止证书——那是假绿。
        """
        evidence = self.theorem.induction.termination
        if evidence is None:
            return False
        return (
            evidence.all_arms_decrease
            and evidence.no_wraparound_basis is not None
            and not evidence.pending_premises
        )

    @property
    def depth_classes_complete(self) -> bool:
        """§4.1 的两条义务：Base 的首次到达覆盖 + 归纳步的转移封闭。

        两者分别由 Base 查询与归纳步产出，必须**都**在场——只有其一时深度类
        集合还不是该循环头的归纳不变式。
        """
        base_evidence = self.base.depth_evidence
        step_evidence = self.theorem.induction.depth_evidence
        if base_evidence is None or step_evidence is None:
            return False
        return (
            base_evidence.arrival_coverage_basis is not None
            and step_evidence.transition_closed
        )

    @property
    def unmet_obligations(self) -> Tuple[str, ...]:
        """列出未满足的义务，供报告直接引用（而不是只给一个 False）。"""
        missing = []
        if not self.theorem.proved:
            missing.append("theorem (R preservation) not proved")
        if not self.base.proved:
            missing.append("base (R holds on arrival) not proved")
        if self.exit_query is None:
            missing.append("exit query (3) never ran")
        elif not self.exit_query.proved:
            missing.append("exit query (3) not proved")
        if not self.depth_classes_complete:
            missing.append(
                "depth-class completeness incomplete "
                "(arrival coverage / transition closure)"
            )
        if not self.structural_premises_complete:
            missing.append(
                "cutpoint structural premises not covered at: "
                + ", ".join(
                    sorted(
                        set(CUTPOINT_STRUCTURAL_SITES)
                        - set(self.structural_premise_sites)
                    )
                )
            )
        if self.require_termination:
            if not self.termination_complete:
                evidence = self.theorem.induction.termination
                pending = evidence.pending_premises if evidence else ()
                if pending:
                    missing.append(
                        "termination premises not discharged: "
                        + ", ".join(pending)
                    )
                else:
                    missing.append("termination evidence incomplete (2e)")
        return tuple(missing)

    @property
    def depth_class(self) -> int:
        return self.theorem.key.depth_class

    @property
    def evm_header(self) -> int:
        return self.theorem.key.evm_header

    @property
    def x86_header(self) -> int:
        return self.theorem.key.x86_header


@dataclass
class LoopCertificateCache:
    """Per-run cache; intentionally has no persistence API."""

    theorems: Dict[Tier1LoopTheoremKey, Tier1LoopTheorem] = field(
        default_factory=dict
    )
    applications: Dict[
        Tier1LoopApplicationKey, Tier1LoopCertificate
    ] = field(default_factory=dict)
    # Some application keys deliberately use exact per-run Python/Z3 object
    # identities instead of serialising enormous symbolic states.  Z3 AST ids
    # (and Python ``id`` values used for opaque metadata) may be recycled after
    # their owners are collected, so retain the source object graph for every
    # such cached application.  This makes those identities unique for the
    # lifetime of the per-run cache without putting unhashable symbolic states
    # directly in the dictionary key.
    application_identity_anchors: Dict[
        Tier1LoopApplicationKey, object
    ] = field(default_factory=dict, repr=False)

    # `callable_identity` 对 lambda / 闭包 / 绑定方法回退到含地址的 `repr()`。
    # 地址在对象被 GC 后会被复用，届时一个语义不同的新闭包会生成相同的 key
    # 并复用旧定理（假绿）。因此凡是进过缓存键的可调用对象，都必须在本缓存的
    # 生命周期内被**持有**——这个列表就是那个锚。
    callable_anchors: List[object] = field(default_factory=list, repr=False)

    def anchor_callable(self, fn) -> None:
        """把进过缓存键的可调用对象钉住，防止地址复用造成键碰撞。"""
        if fn is None:
            return
        if not any(anchored is fn for anchored in self.callable_anchors):
            self.callable_anchors.append(fn)

    def theorem(self, key: Tier1LoopTheoremKey) -> Optional[Tier1LoopTheorem]:
        return self.theorems.get(key)

    def put_theorem(self, theorem: Tier1LoopTheorem) -> None:
        self.theorems[theorem.key] = theorem

    def application(
        self, key: Tier1LoopApplicationKey
    ) -> Optional[Tier1LoopCertificate]:
        return self.applications.get(key)

    def put_application(
        self,
        certificate: Tier1LoopCertificate,
        *,
        identity_anchor: object = None,
    ) -> None:
        self.applications[certificate.key] = certificate
        if identity_anchor is not None:
            self.application_identity_anchors[certificate.key] = identity_anchor


__all__ = [
    "LoopCertificateCache",
    "callable_identity",
    "fingerprint_aot_profile",
    "Tier1LoopApplicationKey",
    "Tier1LoopCertificate",
    "Tier1LoopTheorem",
    "Tier1LoopTheoremKey",
    "fingerprint_assumptions",
    "fingerprint_evm_blocks",
    "fingerprint_summary_config",
    "fingerprint_x86_blocks",
]
