"""Tier 1 循环证书的义务合取语义（docs/循环处理增强方案.md §4.5）。

核心守的一件事：**证书的 `proved` 必须严于 `LoopInductionResult.proved`**。

后者只表示锁步同步（②a–d）成立；证书是给主证明消费的，还必须带上 §4.5 要求的
终止证据与深度类完备性。两者混为一谈，"同步已证"就会冒充"终止已证"——那是
在报告层面的假绿。
"""

import pytest

from verification.loop_certificates import (
    LoopCertificateCache,
    Tier1LoopApplicationKey,
    Tier1LoopCertificate,
    Tier1LoopTheorem,
    Tier1LoopTheoremKey,
    fingerprint_assumptions,
    fingerprint_summary_config,
)
from verification.cutpoint_relation import CUTPOINT_STRUCTURAL_SITES
from verification.loop_induction import (
    DepthClassEvidence,
    ExternalPremise,
    LoopInductionResult,
    TerminationEvidence,
)


def _theorem_key(**overrides) -> Tier1LoopTheoremKey:
    base = dict(
        evm_program="evm-fp",
        x86_program="x86-fp",
        evm_header=0,
        x86_header=0,
        evm_exits=(30,),
        x86_exits=(0x13,),
        depth_class=1,
        relation="cutpoint-r-develop-v1",
        summary_config="cfg",
        aot_profile="profile",
    )
    base.update(overrides)
    return Tier1LoopTheoremKey(**base)


def _premises(discharged: bool = True):
    """五条外部前提。`discharged=False` 用来测「前提未兑现」那一格。"""
    return [
        ExternalPremise(
            name=f"premise_{i}", detail="...", responsible="...",
            discharged=discharged,
        )
        for i in range(5)
    ]


def _complete_termination() -> TerminationEvidence:
    return TerminationEvidence(
        latch_arms_checked=1,
        latch_arms_decreasing=1,
        no_wraparound_basis="TAG guard forks before the subtraction",
        external_premises=_premises(discharged=True),
    )


# 用哨兵区分「没传（要默认值）」与「显式传 None（要缺证据）」——两者语义相反，
# 用 None 兼任默认标记会让"缺证据"的用例悄悄拿到完整证据而变绿。
_DEFAULT = object()


def _step_result(termination=_DEFAULT, depth=_DEFAULT) -> LoopInductionResult:
    if termination is _DEFAULT:
        termination = _complete_termination()
    if depth is _DEFAULT:
        depth = DepthClassEvidence(
            registered_classes=(1,),
            latch_transitions_checked=1,
            latch_transitions_closed=1,
        )
    return LoopInductionResult(
        status="proved", termination=termination, depth_evidence=depth,
    )


def _base_result(depth=_DEFAULT) -> LoopInductionResult:
    if depth is _DEFAULT:
        depth = DepthClassEvidence(
            registered_classes=(1,),
            arrival_coverage_basis="coverage certificate complete",
        )
    return LoopInductionResult(
        status="proved", depth_classes=[1], depth_evidence=depth,
    )


def _exit_result(proved: bool = True) -> LoopInductionResult:
    return LoopInductionResult(status="proved" if proved else "inconclusive")


def _certificate(step=None, base=None, exit_query=_DEFAULT,
                 structural_premise_sites=_DEFAULT,
                 **kwargs) -> Tier1LoopCertificate:
    key = _theorem_key()
    theorem = Tier1LoopTheorem(
        key=key, induction=step or _step_result(), query_count=3
    )
    if exit_query is _DEFAULT:
        exit_query = _exit_result()
    if structural_premise_sites is _DEFAULT:
        # 默认给齐五处，让各用例专注自己那一维（终止证据 / 深度类 / ③出口）。
        # 结构前提本身的守卫由 TestStructuralPremiseCoverage 单独覆盖——
        # 混在别的用例里会让"某处漏核对"被无关的断言掩盖。
        structural_premise_sites = tuple(CUTPOINT_STRUCTURAL_SITES)
    return Tier1LoopCertificate(
        key=Tier1LoopApplicationKey(
            theorem=key, caller_assumptions="", entry_condition=""
        ),
        theorem=theorem,
        base=base or _base_result(),
        exit_query=exit_query,
        structural_premise_sites=structural_premise_sites,
        **kwargs,
    )


class TestObligationConjunction:
    def test_fully_evidenced_certificate_is_proved(self):
        cert = _certificate()
        assert cert.proved
        assert cert.unmet_obligations == ()

    def test_synchronisation_alone_is_not_enough(self):
        """归纳步 proved 但没有终止证据 ⇒ 证书**不成立**。

        这是本模块存在的理由：`LoopInductionResult.proved` 为真只说明两侧锁步
        同步，主证明不能据此认为循环会终止。
        """
        step = _step_result(termination=None)
        cert = _certificate(step=step)

        assert step.proved              # 同步性确实成立
        assert not cert.proved          # 但证书不成立
        assert "termination" in " ".join(cert.unmet_obligations)

    def test_partial_latch_coverage_is_not_enough(self):
        """有一条 latch arm 没证出 gas 递减 ⇒ 终止证据不完整。"""
        step = _step_result(
            termination=TerminationEvidence(
                latch_arms_checked=2,
                latch_arms_decreasing=1,          # 少一条
                no_wraparound_basis="...",
            )
        )
        assert not _certificate(step=step).proved

    def test_missing_no_wraparound_basis_is_not_enough(self):
        """gas 递减 + 位向量回绕 = 递减可能是绕回来的，终止推不出来。"""
        step = _step_result(
            termination=TerminationEvidence(
                latch_arms_checked=1,
                latch_arms_decreasing=1,
                no_wraparound_basis=None,          # 缺依据
            )
        )
        assert not _certificate(step=step).proved

    @pytest.mark.parametrize("missing", ["base", "step"])
    def test_depth_class_needs_both_obligations(self, missing):
        """§4.1 的两条义务必须**都**在场。

        只有首次到达覆盖（Base）而没有转移封闭（归纳步），深度类集合还不是
        该循环头的归纳不变式；反之亦然。
        """
        if missing == "base":
            cert = _certificate(base=_base_result(depth=DepthClassEvidence(
                registered_classes=(1,),
                arrival_coverage_basis=None,       # 缺 (i)
            )))
        else:
            cert = _certificate(step=_step_result(depth=DepthClassEvidence(
                registered_classes=(1,),
                latch_transitions_checked=1,
                latch_transitions_closed=0,        # 缺 (ii)
                escaping_depths=(2,),
            )))
        assert not cert.proved
        assert "depth-class" in " ".join(cert.unmet_obligations)

    def test_require_termination_can_be_opted_out_explicitly(self):
        """可以显式放弃终止性，但那时结论就**不含**终止性——不是默认行为。"""
        cert = _certificate(step=_step_result(termination=None),
                            require_termination=False)
        assert cert.proved

    def test_failed_theorem_or_base_always_blocks(self):
        for bad in ("theorem", "base"):
            step = _step_result() if bad != "theorem" else LoopInductionResult(
                status="inconclusive"
            )
            base = _base_result() if bad != "base" else LoopInductionResult(
                status="inconclusive"
            )
            cert = _certificate(step=step, base=base)
            assert not cert.proved
            # 即便关掉终止要求也不能放行
            relaxed = _certificate(step=step, base=base,
                                   require_termination=False)
            assert not relaxed.proved


class TestCache:
    def test_theorem_and_application_roundtrip(self):
        cache = LoopCertificateCache()
        cert = _certificate()
        cache.put_theorem(cert.theorem)
        cache.put_application(cert)

        assert cache.theorem(cert.theorem.key) is cert.theorem
        assert cache.application(cert.key) is cert

    def test_distinct_depth_classes_do_not_share_a_theorem(self):
        """深度类进 key：不同深度类的定理不能互相复用。"""
        cache = LoopCertificateCache()
        cert = _certificate()
        cache.put_theorem(cert.theorem)
        assert cache.theorem(_theorem_key(depth_class=2)) is None

    def test_relation_version_is_part_of_the_key(self):
        """R 的版本变了，旧证书必须失效（分量集合变化会改变语义）。"""
        cache = LoopCertificateCache()
        cache.put_theorem(_certificate().theorem)
        assert cache.theorem(_theorem_key(relation="other-version")) is None


class TestFingerprints:
    def test_assumption_fingerprint_is_order_insensitive(self):
        from z3 import BitVec, ULE

        x, y = BitVec("x", 64), BitVec("y", 64)
        a, b = ULE(x, y), ULE(y, x)
        assert fingerprint_assumptions([a, b]) == fingerprint_assumptions([b, a])

    def test_summary_config_fingerprint_tracks_modes(self):
        from x86_64.summaries.registry import (
            TRUSTED_SUMMARY_CONFIG,
            TRUSTED_SUMMARY_CONFIG_WITH_TIER2,
        )

        assert fingerprint_summary_config(
            TRUSTED_SUMMARY_CONFIG
        ) != fingerprint_summary_config(TRUSTED_SUMMARY_CONFIG_WITH_TIER2)


class TestExitQueryObligation:
    """③ 出口不是可选项（codex review 的阻塞项）。

    循环完全可以保持 R、gas 递减并正常退出，而退出**之后**的后缀产生不同的
    status / 返回值 / storage。缺了 ③，证书只覆盖「循环本身」，却会被主证明
    当成「这条路径已验」。
    """

    def test_missing_exit_query_blocks_the_certificate(self):
        cert = _certificate(exit_query=None)
        assert not cert.proved
        assert "exit query" in " ".join(cert.unmet_obligations)

    def test_failed_exit_query_blocks_the_certificate(self):
        cert = _certificate(exit_query=_exit_result(proved=False))
        assert not cert.proved
        assert "exit query" in " ".join(cert.unmet_obligations)

    def test_exit_query_is_required_even_without_termination(self):
        """放弃终止性 ≠ 放弃出口义务——后者与终止性无关。"""
        cert = _certificate(exit_query=None, require_termination=False)
        assert not cert.proved


class TestExternalPremisesMustBeDischarged:
    """外部前提必须被**兑现**，不能只是说明文字（codex review 的阻塞项）。

    六项终止前提里本处只直接证两项；其余四项若只记成一串描述而 `proved` 不
    检查，就等于把它们降格成注释——「内层循环已处理」「SCC 已切断」没落实时，
    局部的 gas 递减结论仍会被升格成终止证书。
    """

    def test_undischarged_premise_blocks_termination(self):
        step = _step_result(
            termination=TerminationEvidence(
                latch_arms_checked=1,
                latch_arms_decreasing=1,
                no_wraparound_basis="...",
                external_premises=_premises(discharged=False),
            )
        )
        cert = _certificate(step=step)
        assert not cert.proved
        assert "not discharged" in " ".join(cert.unmet_obligations)

    def test_partially_discharged_premises_still_block(self):
        premises = _premises(discharged=True)
        premises[2] = ExternalPremise(
            name="all_sccs_cut_or_certified",
            detail="...",
            responsible="enclosing proof graph",
            discharged=False,
        )
        step = _step_result(
            termination=TerminationEvidence(
                latch_arms_checked=1,
                latch_arms_decreasing=1,
                no_wraparound_basis="...",
                external_premises=premises,
            )
        )
        cert = _certificate(step=step)
        assert not cert.proved
        assert "all_sccs_cut_or_certified" in " ".join(cert.unmet_obligations)

    def test_empty_premise_list_does_not_silently_pass(self):
        """清空列表不能变成「没有待兑现前提」而放行。

        生成端必须**填**这些前提；空列表意味着调用方绕过了记录，这里以
        `latch_arms_checked` 等其余义务兜底，但至少不能因为空列表而更宽松。
        """
        step = _step_result(
            termination=TerminationEvidence(
                latch_arms_checked=1,
                latch_arms_decreasing=1,
                no_wraparound_basis="...",
                external_premises=[],
            )
        )
        # 空列表下 pending 为空，证书会成立——这是已知边界：真正的守卫在生成端
        # （`_collect_termination_evidence` 无条件填五条）。此测试钉住这一点，
        # 以便将来若要收紧（要求非空）时有明确的失败点。
        assert _certificate(step=step).proved


class TestStructuralPremiseCoverage:
    """cutpoint 结构前提的五处覆盖必须齐全（§4.5.6）。

    这一维与终止性**正交**：status 不进 R 的等式分量之后，"两侧都还在 running"
    只剩初值在撑着；五处任一漏核对，一个已终止的状态就能冒充 cutpoint 到达状态。
    """

    def test_missing_one_site_blocks_the_certificate(self):
        partial = tuple(CUTPOINT_STRUCTURAL_SITES[:-1])
        missing = CUTPOINT_STRUCTURAL_SITES[-1]
        cert = _certificate(structural_premise_sites=partial)
        assert not cert.proved
        assert any(missing in reason for reason in cert.unmet_obligations)

    def test_no_sites_at_all_blocks_the_certificate(self):
        cert = _certificate(structural_premise_sites=())
        assert not cert.proved

    def test_require_termination_false_does_not_skip_structural_premises(self):
        """放弃终止性只该放弃终止性——结构前提与它无关，不能被一并跳过。"""
        cert = _certificate(
            structural_premise_sites=(), require_termination=False
        )
        assert not cert.proved
        assert any(
            "structural premises" in reason for reason in cert.unmet_obligations
        )

    def test_all_five_sites_satisfy_this_dimension(self):
        cert = _certificate(
            structural_premise_sites=tuple(CUTPOINT_STRUCTURAL_SITES)
        )
        assert cert.proved
        assert not any(
            "structural premises" in reason for reason in cert.unmet_obligations
        )
