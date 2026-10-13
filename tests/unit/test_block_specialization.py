"""三参数专门化计划与闭包义务（docs/块级lockstep等价验证方案.md §2.3）。

重点守两件事：

1. **⊤ 与 None 与空集三者不得混淆** —— 它们的处置分别是"符号节点"、"合法配置"、
   "分析缺陷"，混用会让降级路径静默吞掉本该报错的情形；
2. **对账能抓出分析器之间的不一致**，而不是取其一。
"""

import pytest

from verification.block_specialization import (
    TOP,
    BlockSpecialization,
    build_specialization_plan,
)


def _plan(**overrides):
    """两块直线 CFG：10 -> 20，两块都可专门化。"""
    base = dict(
        reachable_pcs=[10, 20],
        succs={10: (20,), 20: ()},
        depth_classes={10: {0}, 20: {2}},
        memory_sizes={10: 0x60, 20: 0x60},
        free_pointers={10: 0x80, 20: 0x80},
    )
    base.update(overrides)
    return build_specialization_plan(**base)


# -- 基本分类 ---------------------------------------------------------------


def test_all_concrete_blocks_are_specializable():
    plan = _plan()
    assert plan.ok
    assert set(plan.specializable) == {10, 20}
    assert plan.degraded == {}
    assert plan.theorem_instances == 2


def test_specialization_feeds_build_havoc():
    plan = _plan()
    spec = plan.specializable[10][0]
    assert spec.as_havoc_kwargs() == {
        "stack_depth": 0,
        "memory_size": 0x60,
        "free_memory_pointer": 0x80,
    }


def test_multiple_depth_classes_produce_one_instance_each():
    plan = _plan(depth_classes={10: {0, 2, 4}, 20: {2}})
    assert len(plan.specializable[10]) == 3
    assert plan.theorem_instances == 4


# -- ⊤ ⇒ 降级，且不是违例 ---------------------------------------------------


def test_top_memory_size_becomes_symbolic_relation():
    plan = _plan(memory_sizes={10: 0x60, 20: TOP})
    assert plan.ok, "⊤ 是合法的降级路径，不该记成违例"
    assert set(plan.specializable) == {10, 20}
    assert plan.specializable[20][0].memory_size is None


def test_top_fmp_becomes_symbolic_relation():
    plan = _plan(free_pointers={10: 0x80, 20: TOP})
    assert plan.ok
    assert plan.specializable[20][0].free_memory_pointer is None


def test_degraded_and_specializable_partition_the_reachable_set():
    plan = _plan(memory_sizes={10: 0x60, 20: TOP})
    assert set(plan.specializable) | set(plan.degraded) == {10, 20}
    assert not set(plan.specializable) & set(plan.degraded)


# -- 对账：分析器不一致必须被抓住，而不是取其一 -----------------------------


def test_empty_depth_class_on_a_reachable_block_is_a_violation():
    """空集不是 ⊤：一个分析器说可达、另一个说没有深度类 ⇒ 矛盾，不能默默降级。"""
    plan = _plan(depth_classes={10: {0}, 20: set()})
    assert not plan.ok
    assert any(v.kind == "inconsistent" and v.pc == 20 for v in plan.violations)


def test_empty_value_set_is_a_violation_not_a_degrade():
    plan = _plan(memory_sizes={10: 0x60, 20: frozenset()})
    assert not plan.ok
    assert any(v.kind == "inconsistent" for v in plan.violations)


def test_missing_analysis_defaults_to_symbolic_parameter():
    """分析器完全没给某块的结论 ⇒ 按 ⊤ 处理（保守方向），不是崩溃。"""
    plan = _plan(memory_sizes={10: 0x60})
    assert plan.ok
    assert plan.specializable[20][0].memory_size is None


# -- (H3) 发散哨兵 ----------------------------------------------------------


def test_many_finite_candidates_do_not_prove_or_disprove_convergence():
    plan = _plan(depth_classes={10: set(range(200)), 20: {2}}, )
    assert plan.ok
    assert plan.rounds == 0


def test_candidate_resource_budget_is_explicit():
    plan = build_specialization_plan(
        reachable_pcs=[10],
        succs={10: ()},
        depth_classes={10: set(range(10))},
        memory_sizes={10: 0x60},
        free_pointers={10: 0x80},
        max_instances=5,
    )
    assert not plan.ok


def test_missing_successor_is_not_silently_degraded():
    plan = _plan(succs={10: (999,), 20: ()})
    assert not plan.ok
    assert "unregistered" in plan.violations[0].detail


# -- 报告 -------------------------------------------------------------------


def test_coverage_summary_mentions_both_sides():
    plan = _plan(memory_sizes={10: 0x60, 20: TOP})
    summary = plan.coverage_summary()
    assert "2/2" in summary and "degraded" in summary


def test_specialization_is_hashable_for_use_as_a_theorem_key():
    spec = BlockSpecialization(10, 0, 0x60, 0x80)
    assert len({spec, BlockSpecialization(10, 0, 0x60, 0x80)}) == 1


def test_actual_abstract_interpreter_top_is_a_symbolic_candidate():
    from tools.msize_absint import TOP as ANALYSIS_TOP
    plan = _plan(memory_sizes={10: 96, 20: ANALYSIS_TOP},
                 free_pointers={10: 128, 20: ANALYSIS_TOP})
    assert plan.ok and not plan.degraded
    assert plan.specializable[20] == (BlockSpecialization(20, 2, None, None),)
