"""块级 lock-step 的三参数专门化（docs/块级lockstep等价验证方案.md §2.3/§4.1）。

`build_havoc` 除 `stack_depth` 外新增 `memory_size` / `free_memory_pointer`
两个专门化参数。本文件守两件事：

1. **专门化真的生效**，且两侧一致——`fmp` 写在 memory 快照上，x86 视图是
   `Lambda(a, Select(snapshot, a - r15))`，必须捕获**写后**的数组；
2. **未专门化时行为不变**（向后兼容，`free_memory_pointer` 义务恒真）。

独立文件而非并入 `test_cutpoint_relation.py`：同名 pytest 类会静默互相覆盖，
项目踩过这个坑。
"""

import pytest
from z3 import BitVecVal, Solver, is_false, is_true, sat, simplify, unsat

from verification.cutpoint_relation import (
    FREE_MEMORY_POINTER_OFFSET,
    CutpointModelRangeError,
    CutpointRelationSchema,
    read_evm_memory_word,
    read_x86_memory_word,
)

MSIZE = 0x60
FMP = 0x80
DEPTH = 3


@pytest.fixture
def schema():
    return CutpointRelationSchema()


def _specialized(schema, **kwargs):
    return schema.build_havoc(
        stack_depth=DEPTH, memory_size=MSIZE, free_memory_pointer=FMP, **kwargs
    )


# -- 分量登记 ---------------------------------------------------------------


def test_free_memory_pointer_is_a_declared_component(schema):
    assert "free_memory_pointer" in schema.component_names


def test_havoc_binds_the_new_component(schema):
    ctx = _specialized(schema)
    assert "free_memory_pointer" in ctx.bound_components


def test_context_carries_the_specialization_parameters(schema):
    ctx = _specialized(schema)
    assert (ctx.stack_depth, ctx.memory_size, ctx.free_memory_pointer) == (
        DEPTH,
        MSIZE,
        FMP,
    )


def test_goals_cover_every_component_including_the_new_one(schema):
    ctx = _specialized(schema)
    goals = schema.component_goals(ctx.state, ctx.state, DEPTH, context=ctx)
    assert tuple(g.name for g in goals) == schema.component_names


# -- 专门化生效，且两侧一致（核心假绿防护）---------------------------------


def test_free_pointer_is_concrete_on_both_sides(schema):
    """x86 视图必须捕获**写入 fmp 之后**的数组。

    先建视图再改 EVM 侧内存，会让两侧指向不同数组，而 `memory` 分量的等式
    仍然形式上成立 —— 那是假绿。本用例直接读两侧的 `mem[0x40]`。
    """
    state = _specialized(schema).state
    expected = BitVecVal(FMP, 256)
    for read in (read_evm_memory_word, read_x86_memory_word):
        word = simplify(read(state, FREE_MEMORY_POINTER_OFFSET) == expected)
        assert is_true(word), f"{read.__name__} 未读到专门化的 free pointer"


def test_memory_size_is_concrete_on_both_sides(schema):
    state = _specialized(schema).state
    assert simplify(state.evm_memory.MSize == BitVecVal(MSIZE, 64)).__bool__()
    assert simplify(
        state.callengine_memory_size_bytes == BitVecVal(MSIZE, 64)
    ).__bool__()


def test_specialized_goals_pin_the_values_not_merely_equality(schema):
    """义务必须钉住具体值，而不只是"两侧相等"。

    只证相等的话，定理在任意 MSize 上都成立，却会被应用到按具体值证出的
    结论上 —— (H1) 到达覆盖形同虚设。
    """
    ctx = _specialized(schema)
    by_name = {
        g.name: g.condition
        for g in schema.component_goals(
            ctx.state, ctx.state, DEPTH, context=ctx
        )
    }
    solver = Solver()
    # 目标在一个 MSize 被钉成别的值的状态上必须不可满足
    solver.add(by_name["memory_size"])
    solver.add(ctx.state.evm_memory.MSize != BitVecVal(MSIZE, 64))
    assert solver.check() == unsat


# -- 未专门化：向后兼容 -----------------------------------------------------


def test_unspecialized_free_pointer_goal_is_vacuously_true(schema):
    ctx = schema.build_havoc(stack_depth=DEPTH)
    by_name = {
        g.name: g.condition
        for g in schema.component_goals(
            ctx.state, ctx.state, DEPTH, context=ctx
        )
    }
    assert is_true(simplify(by_name["free_memory_pointer"]))


def test_unspecialized_memory_size_stays_symbolic(schema):
    ctx = schema.build_havoc(stack_depth=DEPTH)
    solver = Solver()
    solver.add(ctx.state.evm_memory.MSize == BitVecVal(0xA0, 64))
    assert solver.check() == sat, "未专门化时 MSize 应当仍是自由符号"


# -- fail-closed ------------------------------------------------------------


def test_out_of_range_memory_size_is_rejected(schema):
    """越界值若被接受，域约束会让整个 havoc 状态 unsat —— 最危险的 vacuous
    假绿。必须当场拒绝，让调用方降级而不是放宽边界。"""
    with pytest.raises(CutpointModelRangeError):
        schema.build_havoc(
            stack_depth=DEPTH,
            memory_size=schema.max_memory_size_bytes + 0x20,
            free_memory_pointer=FMP,
        )


def test_misaligned_memory_size_is_rejected(schema):
    with pytest.raises(CutpointModelRangeError):
        schema.build_havoc(
            stack_depth=DEPTH, memory_size=0x61, free_memory_pointer=FMP
        )


def test_context_and_explicit_parameters_conflict(schema):
    """两处给出不同的值 = 定理证在 A 上、应用到 B 上。当场拒绝而非取其一。"""
    ctx = _specialized(schema)
    with pytest.raises(ValueError, match="不得再显式传"):
        schema.component_goals(
            ctx.state, ctx.state, DEPTH, context=ctx, memory_size=0xA0
        )


# -- entry / exit site（方案 §2.4 ②(b)）------------------------------------


def _stack_geometry(schema, state, *, site):
    goals = schema.component_goals(state, state, DEPTH, site=site)
    return next(g.condition for g in goals if g.name == "stack_geometry")


def test_exit_site_drops_the_r14_reconstruction_term(schema):
    """x86 块内不维护 R14 与 [R13+0x30] 的同步：出口时 R14 仍是入口值，由
    后继块的 TAG 序言无条件重建。不做这个区分，每个有净栈效应的块都会假失败。
    """
    state = _specialized(schema).state
    entry = _stack_geometry(schema, state, site="entry")
    exit_ = _stack_geometry(schema, state, site="exit")
    assert len(entry.children()) == len(exit_.children()) + 1


def test_exit_site_still_asserts_the_byte_offset(schema):
    """省掉的只有 R14 那一项 —— byte_offset 仍然是义务，否则后继块 TAG 序言
    重建 R14 时用的就是一个没被证明的值。

    喂一个 byte_offset 被改错的 x86 状态，exit 义务必须当场变假。
    """
    ctx = _specialized(schema)
    evm_state = ctx.state
    x86_state = ctx.state.copy()
    x86_state.callengine_stack_byte_offset = BitVecVal(0xDEAD0, 64)
    goals = schema.component_goals(evm_state, x86_state, DEPTH, site="exit")
    cond = next(g.condition for g in goals if g.name == "stack_geometry")
    assert is_false(simplify(cond)), "exit site 必须仍然约束 byte_offset"


def test_unknown_site_is_rejected(schema):
    state = _specialized(schema).state
    with pytest.raises(ValueError, match="unknown relation site"):
        schema.component_goals(state, state, DEPTH, site="latch")


def test_entry_is_the_default_site(schema):
    """默认必须是完整义务：漏传 site 时应当更严格而不是更松。"""
    state = _specialized(schema).state
    goals = schema.component_goals(state, state, DEPTH)
    default = next(g.condition for g in goals if g.name == "stack_geometry")
    assert len(default.children()) == len(
        _stack_geometry(schema, state, site="entry").children()
    )
