"""把 ①②③ 三条查询串成一张可被主证明消费的证书（§4.2 + §4.5）。

这是「证明原语层」与「主证明折叠」之间的那一层：`Tier1LoopInduction` 提供三条
查询，:mod:`verification.loop_certificates` 定义证书的形状，本模块负责按 §4.2
的顺序把它们跑出来并组装。

## 顺序不是随意的

```text
① Base    → 产出 depth_classes（到达循环头时的绝对栈深）
② 归纳步  → 对**每个** depth class 各证一次（R 按类实例化）
③ 出口    → 从「出口处 R 成立」继续到下一 cutpoint 或终止
```

②必须在①之后，因为 R 的 `live_stack_prefix` 与 `stack_geometry` 两个分量都按
绝对栈深实例化——深度类未知时无法构造 havoc 状态。

## 每个深度类都要独立成书

一个循环头可能被不同调用点以不同绝对栈深到达。**每个深度类是一条独立的定理**，
不能用其中一条覆盖其余；`Tier1LoopTheoremKey.depth_class` 进缓存键正是为此。
任一深度类失败 ⇒ 整体 inconclusive（不是「其它类还好」）。
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

from z3 import And, Not, SolverFor, unsat

from evm_ir.models import EVMBlock
from state.smt_state import SMTState
from verification.cutpoint_relation import (
    CutpointModelRangeError,
    CutpointRelationSchema,
)
from verification.loop_certificates import (
    LoopCertificateCache,
    Tier1LoopApplicationKey,
    Tier1LoopCertificate,
    Tier1LoopTheorem,
    Tier1LoopTheoremKey,
    callable_identity,
    fingerprint_aot_profile,
    fingerprint_assumptions,
    fingerprint_evm_blocks,
    fingerprint_summary_config,
    fingerprint_x86_blocks,
)
from verification.loop_induction import (
    APPLICATION_STRUCTURAL_SITE,
    ExternalPremiseDischarges,
    LoopInductionResult,
    Tier1LoopInduction,
)
from x86_64.models import X86Block


@dataclass
class LoopProofOutcome:
    """一个循环头在所有深度类上的证明结果。"""

    certificates: Tuple[Tier1LoopCertificate, ...] = ()
    reasons: Tuple[str, ...] = ()
    queries: Tuple[Tuple[str, str], ...] = ()
    depth_classes: Tuple[int, ...] = ()

    @property
    def proved(self) -> bool:
        """所有深度类都拿到成立的证书，且没有任何失败原因。

        **空证书集合不算成功**：那意味着 Base 没找到任何到达路径，此时说"证明
        通过"等于把一个没验过的循环报成已验——vacuous 方向。
        """
        return (
            bool(self.certificates)
            and not self.reasons
            and all(cert.proved for cert in self.certificates)
        )

    @property
    def unmet_obligations(self) -> Tuple[str, ...]:
        out: List[str] = list(self.reasons)
        for cert in self.certificates:
            out.extend(
                f"depth={cert.depth_class}: {reason}"
                for reason in cert.unmet_obligations
            )
        return tuple(out)


def _check_application_premise(
    schema: CutpointRelationSchema,
    initial_state: SMTState,
    timeout_ms: int,
    queries: List[Tuple[str, str]],
) -> Optional[str]:
    """§4.5.6 覆盖点②：**每次 certificate application** 的结构前提。

    定理是在"两侧均 running"的 havoc 前提下证出的，把它绑到一个具体调用方
    （`initial_state` + caller assumptions）时必须重新确认该前提在这个调用
    上下文里成立。少了这一步，一个已经带着终止状态码的调用方状态也能领到证书
    ——那正是 §4.5.6 说的"靠 `create_initial_state` 的初值偷换"。

    Returns:
        None 表示前提成立；否则返回拒绝理由。SAT/unknown 一律 fail-closed
        转 inconclusive，**不当反例报告**。
    """
    report = schema.structural_premises(
        initial_state, initial_state, site=APPLICATION_STRUCTURAL_SITE
    )
    if not report.ok:
        return (
            "certificate application: cutpoint structural premise violated "
            + "; ".join(report.defects)
        )
    solver = SolverFor("QF_AUFBV")
    solver.set("timeout", timeout_ms)
    for assumption in getattr(initial_state, "assumptions", None) or []:
        solver.add(assumption)
    solver.add(Not(And(*report.conditions)))
    verdict = solver.check()
    queries.append(("② application structural premise", str(verdict)))
    if verdict != unsat:
        return (
            "certificate application: both sides must be running at the "
            f"cutpoint, but that could not be established ({verdict}; "
            "SAT/unknown ⇒ inconclusive, NOT a counterexample)"
        )
    return None


def _prove_all_exits(
    checker: Tier1LoopInduction,
    depth: int,
    *,
    evm_exits: Sequence[int],
    x86_exits: Sequence[int],
    summary_config,
    queries: List[Tuple[str, str]],
) -> LoopInductionResult:
    """对**每个**配对出口跑 ③，合取结果。

    `check_exit_query()` 不指定出口时只取排序后的第一个。② 虽然证明了每个出口
    处 R 保持，但出口**之后**的 suffix 彼此不同——只验第一个出口，其余出口后的
    status / storage / 返回值差异会被整条漏掉。

    任一出口失败 ⇒ 整体 inconclusive（不是"其它出口还好"）。
    """
    evm_sorted = sorted(evm_exits)
    x86_sorted = sorted(checker.x86_exits)
    if not evm_sorted or not x86_sorted:
        return LoopInductionResult.inconclusive(
            "exit query: no pairable exit (all x86 exits are terminal error "
            "stubs, or one side has none)",
            [],
        )
    if len(evm_sorted) != len(x86_sorted):
        # **不能 zip 截断**：`zip` 会静默丢掉多出来的那些出口，于是它们之后的
        # suffix 一条都没验，却仍然签发证书（假绿）。注意 `checker.x86_exits`
        # 已被 `__init__` 过滤掉 TAG 错误 stub，所以数量不等是真实的配对失败。
        return LoopInductionResult.inconclusive(
            f"exit query: exit count mismatch after filtering error stubs — "
            f"EVM {evm_sorted} vs x86 {[hex(a) for a in x86_sorted]}; "
            "refusing to zip-truncate",
            [],
        )
    paired = list(zip(evm_sorted, x86_sorted))

    reasons: List[str] = []
    exit_queries: List[Tuple[str, str]] = []
    # ③ 负责的结构前提覆盖点：**每个**出口都核对过才算这一处成立，所以逐出口
    # 取**交集**。取并集会让"某个出口漏核对"被其它出口的记录掩盖——那正是
    # `UnknownStructuralSiteError` 想防的那类静默缺席。
    exit_sites: Optional[set] = None
    for evm_exit, x86_exit in paired:
        result = checker.check_exit_query(
            stack_depth=depth,
            evm_exit_pc=evm_exit,
            x86_exit_addr=x86_exit,
            summary_config=summary_config,
        )
        queries.extend(result.queries)
        exit_queries.extend(result.queries)
        sites = set(result.structural_premise_sites)
        exit_sites = sites if exit_sites is None else (exit_sites & sites)
        if not result.proved:
            reasons.extend(
                f"exit {evm_exit}<->0x{x86_exit:x}: {reason}"
                for reason in result.reasons
            )

    if reasons:
        return LoopInductionResult(
            status="inconclusive", reasons=reasons, queries=exit_queries
        )
    return LoopInductionResult(
        status="proved",
        queries=exit_queries,
        structural_premise_sites=tuple(sorted(exit_sites or ())),
    )


def _collect_structural_sites(
    base: LoopInductionResult,
    induction: LoopInductionResult,
    exit_query: Optional[LoopInductionResult],
) -> Tuple[str, ...]:
    """汇总 ①②③ 各自核对的结构前提覆盖点，并补上本层认领的那一处。

    `certificate_application` 由编排层认领，依据是：application key 绑定了
    entry condition 与规范化的 caller assumptions，而 ① Base 已对**该入口下的
    全部到达路径**核对过结构前提（`base_arrival`）；证书只在指纹一致时被取用，
    因此被应用到的状态就是 Base 枚举过的那一批。

    这**不解除**消费端的义务：主验证器在 paired cutpoint 引用证书时，仍要对
    当时的实际状态重新核对（§4.7 消费四步的第 3 步）。这里认领的只是"生成侧
    已把适用域钉死在 Base 枚举过的状态集合上"这一条。

    五处不齐时**不在这里补**——`Tier1LoopCertificate.proved` 会因缺项而为假，
    `unmet_obligations` 逐条列出缺哪几处。在这里补齐等于把义务改成注释。
    """
    sites = set(base.structural_premise_sites)
    sites |= set(induction.structural_premise_sites)
    if exit_query is not None:
        sites |= set(exit_query.structural_premise_sites)
    sites.add(APPLICATION_STRUCTURAL_SITE)
    return tuple(sorted(sites))


def prove_loop_certificate(
    *,
    evm_blocks: Sequence[EVMBlock],
    x86_blocks: Sequence[X86Block],
    evm_header: int,
    x86_header: int,
    evm_exits: Sequence[int],
    x86_exits: Sequence[int],
    initial_state: SMTState,
    evm_entry_pc: int,
    x86_entry_addr: int,
    relation_schema: Optional[CutpointRelationSchema] = None,
    cache: Optional[LoopCertificateCache] = None,
    summary_config=None,
    aot_profile=None,
    timeout_ms: int = 30000,
    max_depth: int = 400,
    extra_invariant=None,
    evm_body=None,
    require_termination: bool = True,
    compare_terminal_gas: bool = False,
    host_gas_uf_enabled: bool = False,
    premise_discharges: Optional[ExternalPremiseDischarges] = None,
) -> LoopProofOutcome:
    """跑 ①②③ 并按深度类组装证书。

    Args:
        require_termination: 证书是否要求终止证据与深度类完备性（§4.5）。
            关掉它，结论就**不含**终止性——只是「两侧锁步同步」。
        premise_discharges: 调用方兑现的两条外部终止前提（§6 结构守卫 /
            外层证明图）。默认 None ⇒ 两条都算未兑现，于是
            `require_termination=True` 时证书的 `proved` 恒为 False——这是
            **正确行为**：未兑现的前提不能算数。真正跑过守卫与证明图的那一层
            （`program_verifier`）拿到肯定结论后才可以置位。它进定理缓存键，
            避免"以 True 证过一次、之后以 False 请求"取回宽松定理。
        compare_terminal_gas / host_gas_uf_enabled: 必须与调用方的 `GasCheck`
            档位一致。**这两个必须原样传给每一段查询**——只在接口上收下却不
            往下传，②的 havoc 与 ②(d)/③ 就会退回默认 `False`，含 host 调用
            或 terminal gas 差异的循环会在错误语义下拿到证书（假绿）。它们
            同样进 theorem cache key，避免不同 gas 模式复用同一条定理。

    Returns:
        :class:`LoopProofOutcome`。失败一律是 ``reasons`` 非空或某条证书
        ``proved`` 为假，**绝不把 SAT 当反例报告**（§6：归纳步 SAT ≠ bug）。
    """
    schema = relation_schema or CutpointRelationSchema()
    # calldata 语义开关取自**调用方的初始状态**——Base 本来就用它，②/③ 的 havoc
    # 必须跟上，否则定理会在另一套 calldata 语义下证出（假绿）。
    abstract_calldataload_words = bool(
        getattr(initial_state, "abstract_calldataload_words", False)
    )
    assume_calldata_offset_no_overflow = bool(
        getattr(initial_state, "assume_calldata_offset_no_overflow", True)
    )
    cache = cache if cache is not None else LoopCertificateCache()
    # 进过缓存键的可调用对象必须被缓存持有：`callable_identity` 对匿名可调用
    # 回退到含地址的 repr，对象被 GC 后地址复用会让语义不同的新闭包撞上旧键。
    cache.anchor_callable(extra_invariant)
    for invariant in getattr(schema, "persistent_invariants", ()) or ():
        cache.anchor_callable(invariant)
    queries: List[Tuple[str, str]] = []

    def _checker(stack_depth: int) -> Tier1LoopInduction:
        return Tier1LoopInduction(
            evm_blocks=evm_blocks,
            x86_blocks=x86_blocks,
            evm_header=evm_header,
            x86_header=x86_header,
            evm_exits=evm_exits,
            x86_exits=x86_exits,
            stack_depth=stack_depth,
            timeout_ms=timeout_ms,
            max_depth=max_depth,
            extra_invariant=extra_invariant,
            evm_body=evm_body,
            aot_profile=aot_profile,
            relation_schema=schema,
            compare_terminal_gas=compare_terminal_gas,
            host_gas_uf_enabled=host_gas_uf_enabled,
            abstract_calldataload_words=abstract_calldataload_words,
            assume_calldata_offset_no_overflow=(
                assume_calldata_offset_no_overflow
            ),
        )

    # ① Base：深度类未知时 stack_depth 只用于构造 checker，Base 自己从
    # 实际到达路径提取深度类，不依赖这个占位值。
    base = _checker(stack_depth=0).check_base_query(
        initial_state, evm_entry_pc=evm_entry_pc, x86_entry_addr=x86_entry_addr,
        summary_config=summary_config,
    )
    queries.extend(base.queries)
    if not base.proved:
        return LoopProofOutcome(
            reasons=tuple(base.reasons) or ("base query inconclusive",),
            queries=tuple(queries),
        )

    depth_classes = tuple(base.depth_classes)
    if not depth_classes:
        return LoopProofOutcome(
            reasons=(
                "base query proved but produced no depth class; the loop header "
                "is unreachable from this entry — reporting success here would "
                "be vacuous",
            ),
            queries=tuple(queries),
        )

    theorem_key_base = dict(
        evm_program=fingerprint_evm_blocks(evm_blocks),
        x86_program=fingerprint_x86_blocks(x86_blocks),
        evm_header=evm_header,
        x86_header=x86_header,
        evm_exits=tuple(sorted(evm_exits)),
        x86_exits=tuple(sorted(x86_exits)),
        # gas 档位与强化不变式都改变定理的**命题内容**，必须进 key：
        # 不同 GasCheck 档下 ②/②(d)/③ 证的不是同一件事；不同 `extra_invariant`
        # 下定理成立的子域也不同。
        relation="|".join(
            (
                schema.fingerprint,
                f"gas_terminal={int(compare_terminal_gas)}",
                f"host_gas_uf={int(host_gas_uf_enabled)}",
                f"abstract_cdl={int(abstract_calldataload_words)}",
                f"cdl_no_overflow={int(assume_calldata_offset_no_overflow)}",
                f"invariant={callable_identity(extra_invariant)}",
            )
        ),
        summary_config=fingerprint_summary_config(summary_config),
        aot_profile=fingerprint_aot_profile(aot_profile),
    )
    caller_assumptions = fingerprint_assumptions(
        getattr(initial_state, "assumptions", None) or []
    )

    certificates: List[Tier1LoopCertificate] = []
    reasons: List[str] = []

    for depth in depth_classes:
        key = Tier1LoopTheoremKey(depth_class=depth, **theorem_key_base)
        theorem = cache.theorem(key)
        if theorem is None:
            # 深度类可能合法但超出 schema 的建模范围（如 byte offset > 0x4000）。
            # `build_havoc` 对此抛 ValueError；在这里转成 inconclusive，让流程
            # 降级而不是异常退出。
            # ② 归纳步：按该深度类实例化 R
            try:
                induction = _checker(stack_depth=depth).check_inductive_step(
                    summary_config=summary_config,
                )
            except CutpointModelRangeError as exc:
                # **只**捕获建模范围错误。裸 `except ValueError` 会吞掉别处真正
                # 该 fail-hard 的编程错误，把 bug 伪装成"这个循环证不了"。
                reasons.append(
                    f"depth={depth}: outside the schema's modelled range "
                    f"({exc}); degrading instead of failing hard"
                )
                continue
            queries.extend(induction.queries)
            theorem = Tier1LoopTheorem(
                key=key, induction=induction, query_count=len(induction.queries)
            )
            # **只缓存成立的定理**。timeout/max_depth 不在 key 里，把
            # inconclusive 也缓存起来，调用方换更大预算重试时会直接取回旧的
            # 失败结果而不重新求解（降级被固化成永久失败）。
            if theorem.proved:
                cache.put_theorem(theorem)
        if not theorem.proved:
            reasons.extend(
                f"depth={depth}: {reason}" for reason in theorem.induction.reasons
            )
            continue

        application_key = Tier1LoopApplicationKey(
            theorem=key,
            caller_assumptions=caller_assumptions,
            # `require_termination` 必须进 key：同一个 cache 先以 False 调用、
            # 再以 True 调用时，若 key 相同就会取回那张宽松证书，从而绕过未
            # 兑现的终止前提（假绿）。
            entry_condition=(
                f"{evm_entry_pc}:{x86_entry_addr}"
                f":term={int(require_termination)}"
            ),
        )
        certificate = cache.application(application_key)
        if certificate is None:
            # ③ 出口：循环可以保持 R、gas 递减并正常退出，而退出**之后**的
            # 后缀产生不同的 status / 返回值 / storage。少了这一步，证书只覆盖
            # 「循环本身」却被当成「这条路径已验」。
            # ③ 必须**逐出口**跑。`check_exit_query()` 不传出口时只取排序后的
            # 第一个；②虽然证了每个出口处 R 保持，但出口**之后**的 suffix 各不
            # 相同——只验第一个出口，其余出口后的 status/storage/返回值差异会
            # 被整条漏掉（假绿）。
            exit_query = _prove_all_exits(
                _checker(stack_depth=depth), depth,
                evm_exits=evm_exits, x86_exits=x86_exits,
                summary_config=summary_config, queries=queries,
            )
            certificate = Tier1LoopCertificate(
                key=application_key,
                theorem=theorem,
                base=base,
                exit_query=exit_query,
                require_termination=require_termination,
                structural_premise_sites=_collect_structural_sites(
                    base, theorem.induction, exit_query
                ),
            )
            if certificate.proved:
                cache.put_application(certificate)
        certificates.append(certificate)

    return LoopProofOutcome(
        certificates=tuple(certificates),
        reasons=tuple(reasons),
        queries=tuple(queries),
        depth_classes=depth_classes,
    )


__all__ = ["LoopProofOutcome", "prove_loop_certificate"]
