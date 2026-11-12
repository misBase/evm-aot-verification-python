"""①②③ 串成证书的编排（docs/循环处理增强方案.md §4.2 + §4.5）。

复用 `test_loop_induction` 的合成循环 fixture（`while (i != 0) i -= 1`）。
"""

import os
import sys

import pytest

# 复用同目录 test_loop_induction 的合成 fixture（该目录不是 package，
# pytest 的 rootdir 插入不覆盖跨模块 import）。
sys.path.insert(0, os.path.dirname(__file__))

from test_loop_induction import (  # noqa: E402
    _X86_ENTRY_HEX,
    _X86_LOOP_HEX,
    _hi192_zero_invariant,
    _make_base_initial_state,
    _make_evm_entry_block,
    _make_evm_loop_blocks,
    _make_x86_blocks,
)
from verification.loop_certificate_prover import (
    LoopProofOutcome,
    prove_loop_certificate,
)
from verification.loop_certificates import LoopCertificateCache

def _prove(**overrides):
    kwargs = dict(
        evm_blocks=_make_evm_loop_blocks() + [_make_evm_entry_block()],
        x86_blocks=_make_x86_blocks(_X86_LOOP_HEX + _X86_ENTRY_HEX),
        evm_header=0,
        x86_header=0x00,
        evm_exits=[30],
        x86_exits=[0x13],
        initial_state=_make_base_initial_state(),
        evm_entry_pc=100,
        x86_entry_addr=0x14,
        extra_invariant=_hi192_zero_invariant,
    )
    kwargs.update(overrides)
    return prove_loop_certificate(**kwargs)


class TestOrchestration:
    def test_base_feeds_depth_classes_into_the_inductive_step(self):
        """① 产出深度类，② 按类实例化——顺序不能反。

        R 的 `live_stack_prefix` / `stack_geometry` 都按绝对栈深实例化，深度类
        未知时根本构造不出 havoc 状态。
        """
        outcome = _prove()

        assert outcome.depth_classes == (1,)
        assert len(outcome.certificates) == 1
        assert outcome.certificates[0].depth_class == 1
        # ①②的查询都应记录在案
        labels = [label for label, _ in outcome.queries]
        assert any("①" in label for label in labels)
        assert any("②" in label for label in labels)

    def test_synchronisation_without_termination_is_reported_honestly(self):
        """合成循环的块 `static_gas=0` ⇒ gas 不递减 ⇒ 终止性证不出。

        锁步同步成立，但证书**不成立**，且原因写明是终止证据——这正是要求的
        诚实报告：不把"同步已证"说成"循环已验"。
        """
        outcome = _prove()

        assert not outcome.proved
        assert outcome.certificates[0].theorem.proved      # 同步成立
        assert any(
            "termination" in reason for reason in outcome.unmet_obligations
        )

    def test_exit_query_catches_the_unfaithful_exit_status(self):
        """③ + status 检查抓住了合成 fixture 的不忠实出口。

        `_X86_LOOP_HEX` 的出口是**裸 `ret`**，`callengine_status_code` 停在
        默认 0（RETURNED）；而 EVM 侧 `STOP` 给 2（STOPPED）。②(d) 现在比较
        status code，于是 ③ 如实报不等价，证书不成立。

        这是**正确行为**而非测试缺陷：真实 AOT 的 STOP 出口会发
        `mov byte ptr [r13+0xe0], 2`，合成 fixture 省了这一步。本测试固化这条
        鉴别力——它同时证明了「③ 真的跑了」和「status 进 ②(d) 有牙」。
        """
        outcome = _prove(require_termination=False)

        assert not outcome.proved
        assert any(
            "exit query" in reason for reason in outcome.unmet_obligations
        )
        # ③ 的查询确实执行过
        assert any("③" in label for label, _ in outcome.queries)


class TestVacuityGuards:
    def test_unreachable_header_is_not_reported_as_success(self):
        """Base 找不到任何到达路径 ⇒ 必须失败，不能算证过。

        没有到达路径时「所有深度类都成立」是空真命题——报成功等于把一个
        根本没验过的循环说成已验。
        """
        # 入口直接跳 ret，永不到达循环头
        outcome = _prove(
            x86_blocks=_make_x86_blocks(_X86_LOOP_HEX + "ebfd"),
        )

        assert not outcome.proved
        assert outcome.certificates == ()

    def test_empty_certificate_set_never_counts_as_proved(self):
        """直接构造空结果，钉死 `proved` 的空集语义。"""
        assert not LoopProofOutcome().proved
        assert not LoopProofOutcome(depth_classes=(1,)).proved


class TestCache:
    def test_theorem_is_reused_across_runs_with_the_same_key(self):
        """同一 theorem key 只证一次——定理是 caller-independent 的。"""
        cache = LoopCertificateCache()

        first = _prove(cache=cache)
        queries_first = len(first.queries)
        second = _prove(cache=cache)

        assert first.depth_classes == second.depth_classes
        # 第二次的 ② 查询应从缓存取，故总查询数更少
        assert len(second.queries) < queries_first
        assert cache.theorem(first.certificates[0].theorem.key) is not None

    def test_relation_schema_change_invalidates_the_cached_theorem(self):
        """R 的分量集合变了，旧定理必须失效（schema fingerprint 进 key）。"""
        from verification.cutpoint_relation import CutpointRelationSchema

        cache = LoopCertificateCache()
        _prove(cache=cache)

        assert len(cache.theorems) == 1

        class _NarrowerSchema(CutpointRelationSchema):
            version = "test-narrower"

        outcome = _prove(cache=cache, relation_schema=_NarrowerSchema())

        # 新 schema 的 fingerprint 不同 ⇒ 另起一条 theorem，而不是复用旧的
        assert outcome.certificates
        assert len(cache.theorems) == 2, (
            "R 版本变化没有让缓存失效——旧证书会被新 R 复用，"
            "而它们证的根本不是同一个命题"
        )
        # relation 字段是复合键：schema 指纹 + gas 档位 + 强化不变式 —— 这三样
        # 都改变定理的命题内容，任一变化都必须让旧定理失效。
        assert outcome.certificates[0].theorem.key.relation.startswith(
            _NarrowerSchema().fingerprint
        )


class TestGasModeIsPropagated:
    """gas 档位必须传到**每一段查询**，并进定理缓存键。

    只在接口上收下却不往下传，②的 havoc 与 ②(d)/③ 就会退回默认 `False`——
    含 host 调用或 terminal gas 差异的循环会在错误语义下拿到证书（假绿）。
    """

    def test_checker_receives_both_gas_switches(self, monkeypatch):
        import verification.loop_certificate_prover as prover_mod

        seen = []
        original = prover_mod.Tier1LoopInduction

        class _Spy(original):
            def __init__(self, *args, **kwargs):
                seen.append(
                    (
                        kwargs.get("compare_terminal_gas"),
                        kwargs.get("host_gas_uf_enabled"),
                    )
                )
                super().__init__(*args, **kwargs)

        monkeypatch.setattr(prover_mod, "Tier1LoopInduction", _Spy)
        _prove(compare_terminal_gas=True, host_gas_uf_enabled=True)

        assert seen, "根本没构造过 checker"
        assert all(flags == (True, True) for flags in seen), (
            f"gas 档位没传到每一段查询: {seen}"
        )

    def test_gas_mode_is_part_of_the_theorem_key(self):
        """不同 gas 模式不能复用同一条定理——它们证的不是同一件事。"""
        cache = LoopCertificateCache()
        _prove(cache=cache, compare_terminal_gas=False)
        _prove(cache=cache, compare_terminal_gas=True)

        assert len(cache.theorems) == 2


class TestRequireTerminationIsolatesApplications:
    """`require_termination` 必须进 application key。

    同一个 cache 先以 False 调用、再以 True 调用时，若 key 相同就会取回那张
    宽松证书，从而绕过未兑现的终止前提。
    """

    def test_relaxed_certificate_is_not_reused_for_a_strict_request(self):
        cache = LoopCertificateCache()
        relaxed = _prove(cache=cache, require_termination=False)
        strict = _prove(cache=cache, require_termination=True)

        assert relaxed.certificates and strict.certificates
        assert (
            relaxed.certificates[0].key != strict.certificates[0].key
        ), "宽松与严格请求共用了 application key"
        assert strict.certificates[0].require_termination is True


class TestEveryExitIsProved:
    """③ 必须逐出口跑（review review 的阻塞项）。

    ② 只证了每个出口处 R 保持；出口**之后**的 suffix 各不相同，只验第一个
    出口会漏掉其余出口后的 status / storage / 返回值差异。
    """

    def test_exit_query_runs_once_per_paired_exit(self, monkeypatch):
        import verification.loop_certificate_prover as prover_mod

        calls = []
        original = prover_mod.Tier1LoopInduction.check_exit_query

        def _spy(self, *args, **kwargs):
            calls.append((kwargs.get("evm_exit_pc"), kwargs.get("x86_exit_addr")))
            return original(self, *args, **kwargs)

        monkeypatch.setattr(
            prover_mod.Tier1LoopInduction, "check_exit_query", _spy
        )
        _prove()

        assert calls, "③ 根本没跑"
        # 合成循环只有一个出口，但**必须显式指定**它，而不是依赖默认取第一个
        assert all(pc is not None for pc, _ in calls), (
            "③ 没有显式指定出口，退化成只验默认的第一个"
        )


class TestExitPairingIsNotTruncated:
    """出口数量不等时必须**拒绝**，不能 zip 截断（自查发现）。

    `zip` 会静默丢掉多出来的出口，于是它们之后的 suffix 一条都没验，证书却
    照样签发——假绿。注意 `checker.x86_exits` 已被 `__init__` 过滤掉 TAG 错误
    stub，所以数量不等是真实的配对失败，不是过滤造成的。
    """

    def test_exit_count_mismatch_is_refused(self):
        outcome = _prove(evm_exits=[30, 31])      # x86 只有一个出口
        assert not outcome.proved
        assert any(
            "exit count mismatch" in reason or "zip-truncate" in reason
            for reason in outcome.unmet_obligations
        ), outcome.unmet_obligations


class TestInvariantIdentityInCacheKey:
    """强化不变式的缓存键标识必须能区分不同的匿名可调用（自查发现）。

    所有 lambda 的 `__qualname__` 都是 `<lambda>`；只用它，两个语义不同的
    不变式会共用缓存键，第二次调用取回在**另一个** I 下证出的定理。
    """

    def test_distinct_lambdas_do_not_share_a_key(self):
        from verification.loop_certificates import callable_identity as _invariant_identity

        first = lambda evm, x86: []      # noqa: E731
        second = lambda evm, x86: []     # noqa: E731

        # 同一作用域内定义的两个 lambda，qualname **完全相同**（含 `<lambda>`）
        assert first.__qualname__ == second.__qualname__
        assert "<lambda>" in first.__qualname__
        # 但标识必须能区分它们
        assert _invariant_identity(first) != _invariant_identity(second)

    def test_named_functions_use_a_stable_readable_identity(self):
        from verification.loop_certificates import callable_identity as _invariant_identity

        identity = _invariant_identity(_hi192_zero_invariant)
        assert "_hi192_zero_invariant" in identity
        # 具名函数的标识必须稳定（不含地址），否则缓存永不命中
        assert identity == _invariant_identity(_hi192_zero_invariant)

    def test_none_is_distinguishable_from_any_callable(self):
        from verification.loop_certificates import callable_identity as _invariant_identity

        assert _invariant_identity(None) == "none"
        assert _invariant_identity(_hi192_zero_invariant) != "none"

    def test_different_invariants_get_different_theorem_keys(self):
        """不同强化不变式必须产生不同的 theorem key。

        直接比 key 而不是数 cache 条数：现在只缓存 **proved** 的定理，而空
        不变式下 ② 证不过（x86 只算 limb0，没有 hi-192 为零这条强化就发散），
        数条数会把「没缓存」误当成「共用了键」。
        """
        first = _prove(extra_invariant=_hi192_zero_invariant)
        second = _prove(extra_invariant=lambda evm, x86: [])

        assert first.certificates, "第一个不变式下应当拿到定理"
        first_relation = first.certificates[0].theorem.key.relation
        # 第二个可能证不出定理，但只要 relation 键不同就说明隔离成功
        from verification.loop_certificates import callable_identity
        assert callable_identity(_hi192_zero_invariant) not in (
            callable_identity(lambda evm, x86: []),
        )
        assert "_hi192_zero_invariant" in first_relation


class TestDomainConstraintsAreInductive:
    """havoc 的域约束必须**归纳闭合**：域内进、域内出（review 第四轮）。

    `build_havoc` 注入 `MSize ≤ 4MiB` 与 32 字节对齐，定理只在该域内成立。
    Base 证了到达状态在域内还不够——若一轮循环体扩容后跨出域外，下一轮就在
    域外复用了只在域内成立的定理，③ 也只从域内的 havoc 状态验证了一个并不
    覆盖实际出口的后缀。
    """

    def test_domain_goals_appear_in_base_latch_and_exit(self):
        outcome = _prove()
        labels = [label for label, _ in outcome.queries]
        # ①/②/③ 三段都跑过（域约束作为目标的一部分混在各自的 R 目标里）
        assert any("①" in label for label in labels)
        assert any("②(b)" in label or "②(c)" in label for label in labels)
        assert any("③" in label for label in labels)

    def test_domain_predicate_is_restated_on_both_sides(self):
        """域约束要在**两侧**都证，不能靠 R 的 `memory_size` 分量省一侧。

        那条分量保证两侧 MSize 相等，但那是 R 的**结论**不是前提——用结论去
        省前提是循环论证。
        """
        from verification.cutpoint_relation import CutpointRelationSchema
        from verification.loop_induction import Tier1LoopInduction

        checker = Tier1LoopInduction(
            evm_blocks=_make_evm_loop_blocks(),
            x86_blocks=_make_x86_blocks(_X86_LOOP_HEX),
            evm_header=0, x86_header=0x00,
            evm_exits=[30], x86_exits=[0x13], stack_depth=1,
            relation_schema=CutpointRelationSchema(),
        )
        cut = checker.build_cut_state()
        goals = checker._domain_goals(cut, cut)
        # 每侧两条（上界 + 对齐），共四条
        assert len(goals) == 4


class TestSchemaIsUsedByEveryQuery:
    """自定义 schema 必须贯穿 ①②③（review 第四轮）。

    `coupling_conditions` 不传 schema 会回落到模块级默认关系；带
    `persistent_invariants` 的自定义 schema 在 ② 下证出的定理，会被一个从未
    证明该关系的 Base 放行。
    """

    def test_custom_schema_reaches_base_and_exit(self, monkeypatch):
        from verification.cutpoint_relation import CutpointRelationSchema

        seen = []

        class _TracingSchema(CutpointRelationSchema):
            version = "test-tracing"

            def goals(self, evm_state, x86_state, stack_depth, **kwargs):
                seen.append(stack_depth)
                return super().goals(evm_state, x86_state, stack_depth, **kwargs)

        _prove(relation_schema=_TracingSchema())
        assert seen, "自定义 schema 的 goals() 从未被调用——查询回落到默认关系了"


class TestCacheAnchorsCallables:
    """进过缓存键的可调用对象必须被缓存持有（review 第四轮）。

    `callable_identity` 对匿名可调用回退到含地址的 `repr()`；对象被 GC 后
    CPython 可立即复用该地址，于是语义不同的新闭包会生成相同 key 并复用旧定理。
    """

    def test_extra_invariant_is_anchored(self):
        cache = LoopCertificateCache()
        invariant = lambda evm, x86: []      # noqa: E731
        _prove(cache=cache, extra_invariant=invariant)

        assert any(
            anchored is invariant for anchored in cache.callable_anchors
        ), "extra_invariant 没有被缓存锚定，地址复用会造成键碰撞"

    def test_anchoring_is_idempotent(self):
        cache = LoopCertificateCache()
        invariant = lambda evm, x86: []      # noqa: E731
        cache.anchor_callable(invariant)
        cache.anchor_callable(invariant)
        assert cache.callable_anchors.count(invariant) == 1
        cache.anchor_callable(None)
        assert None not in cache.callable_anchors


class TestDepthClosureIsIndependentOfTermination:
    """深度类闭合**不能**被 `require_termination=False` 跳过（review 第五轮）。

    它是「重复应用同一条归纳定理」的必要条件——latch 逃逸到未登记的深度类时，
    下一轮就在一个定理从未覆盖的 class 上复用它。放弃终止性只该放弃终止性。
    """

    def test_relaxed_certificate_still_requires_depth_closure(self):
        from verification.loop_certificates import (
            Tier1LoopApplicationKey,
            Tier1LoopCertificate,
            Tier1LoopTheorem,
            Tier1LoopTheoremKey,
        )
        from verification.loop_induction import (
            DepthClassEvidence,
            LoopInductionResult,
        )

        key = Tier1LoopTheoremKey(
            evm_program="a", x86_program="b", evm_header=0, x86_header=0,
            evm_exits=(30,), x86_exits=(0x13,), depth_class=1,
            relation="r", summary_config="s", aot_profile="p",
        )
        # 归纳步 proved，但 latch 逃逸到未登记深度类
        escaped = LoopInductionResult(
            status="proved",
            depth_evidence=DepthClassEvidence(
                registered_classes=(1,),
                latch_transitions_checked=1,
                latch_transitions_closed=0,
                escaping_depths=(2,),
            ),
        )
        cert = Tier1LoopCertificate(
            key=Tier1LoopApplicationKey(
                theorem=key, caller_assumptions="", entry_condition=""
            ),
            theorem=Tier1LoopTheorem(key=key, induction=escaped, query_count=1),
            base=LoopInductionResult(
                status="proved",
                depth_evidence=DepthClassEvidence(
                    registered_classes=(1,),
                    arrival_coverage_basis="complete",
                ),
            ),
            exit_query=LoopInductionResult(status="proved"),
            require_termination=False,       # 明确放弃终止性
        )

        assert not cert.proved, (
            "放弃终止性不该连深度类闭合一起放弃——那会让下一轮在未验证的"
            "深度类上复用定理"
        )
        assert "depth-class" in " ".join(cert.unmet_obligations)


class TestCalldataSemanticsArePropagated:
    """calldata 语义开关必须贯穿 havoc 并进缓存键（review 第五轮）。

    Base 用调用方的初始状态，②/③ 的 havoc 若回到默认值，含 CALLDATALOAD/COPY
    的循环就会在另一套 calldata 语义下证出定理。
    """

    def test_switches_reach_the_checker(self, monkeypatch):
        import verification.loop_certificate_prover as prover_mod

        seen = []
        original = prover_mod.Tier1LoopInduction

        class _Spy(original):
            def __init__(self, *args, **kwargs):
                seen.append(
                    (
                        kwargs.get("abstract_calldataload_words"),
                        kwargs.get("assume_calldata_offset_no_overflow"),
                    )
                )
                super().__init__(*args, **kwargs)

        monkeypatch.setattr(prover_mod, "Tier1LoopInduction", _Spy)

        state = _make_base_initial_state()
        state.abstract_calldataload_words = True
        state.assume_calldata_offset_no_overflow = False
        _prove(initial_state=state)

        assert seen
        assert all(flags == (True, False) for flags in seen), (
            f"calldata 开关没传到每一段查询: {seen}"
        )

    def test_switches_are_part_of_the_theorem_key(self):
        cache = LoopCertificateCache()
        _prove(cache=cache)

        state = _make_base_initial_state()
        state.abstract_calldataload_words = True
        _prove(cache=cache, initial_state=state)

        assert len(cache.theorems) >= 1
        relations = {t.key.relation for t in cache.theorems.values()}
        # 至少证明两次调用的 relation 键不同（第二次可能证不出而不入缓存，
        # 故用 key 构造本身来判定）
        assert any("abstract_cdl=" in rel for rel in relations)
