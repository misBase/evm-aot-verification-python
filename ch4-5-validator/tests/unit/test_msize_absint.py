"""tools/msize_absint.py 的回归：方案 §3.3 的实测数字必须逐位复现。

docs/块级lockstep等价验证方案.md §6 阶段 0 的验收是"任一位不符即整体拒绝"，所以
这里的断言全部写成精确相等而不是范围——抽象解释一旦精度退化（表错一条、常量内存
被误清、provenance 退化），唯一率会静默下滑，而下游只会表现为"某些块跑不动"，
根本追不回这里。

三合约的分析各自 < 0.2s（JSON 加载占大头），因此**没有**标 ``slow``：本文件里
"二元分布"和"自校验"两条是方案最核心的结构性发现，必须留在日常 ``-m "not slow"``
回归里。
"""

import functools
import os

import pytest

from evm_ir.json_parser import load_ir_from_json
from evm_ir.models import EVMBlock, EvmOperator
from evm_ir.program import EVMProgram
from tools.msize_absint import (
    MEM_CAP,
    TOP,
    MSizeAnalysisError,
    TopSource,
    analyze_memory_size,
    validate_stack_effects,
)

_DATA_ROOT = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts"
)

CONTRACTS = {
    "ENSRegistry": os.path.join(_DATA_ROOT, "ens_registry", "ENSRegistry.json"),
    "CErc20": os.path.join(_DATA_ROOT, "compound_cerc20", "CErc20.json"),
    "Safe": os.path.join(_DATA_ROOT, "safe", "Safe.json"),
}

#: 方案 §3.3 的实测表：(合约块数, 唯一, 2–4 值, 5–16 值, ⊤)
EXPECTED_DISTRIBUTION = {
    "ENSRegistry": (127, 119, 8, 0, 0),
    "CErc20": (723, 315, 4, 0, 404),
    "Safe": (742, 385, 7, 0, 350),
}

#: 方案 §4.1 的五个成败点热块：pc -> (期望 MSize, 期望 fmp)
EXPECTED_HOT_BLOCKS = {
    "ENSRegistry": {1455: (frozenset({0x60}), 0x80)},
    "CErc20": {
        5343: (frozenset({0x60}), 0x80),
        8186: (TOP, TOP),
    },
    "Safe": {
        6275: (frozenset({0x60}), 0x80),
        5377: (TOP, TOP),
    },
}


@functools.lru_cache(maxsize=None)
def _blocks(name):
    return tuple(EVMProgram(load_ir_from_json(CONTRACTS[name])).blocks)


@functools.lru_cache(maxsize=None)
def _abstraction(name, context_sensitive=True, track_constant_memory=True):
    return analyze_memory_size(
        list(_blocks(name)),
        context_sensitive=context_sensitive,
        track_constant_memory=track_constant_memory,
    )


# ---------------------------------------------------------------------------
# 1. 自校验：抽象值栈的唯一强证据
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_stack_effect_matches_go_exported_depth(name):
    """Σ(per-op stack delta) 逐块等于 Go 导出的 EVMBlock.stack_depth。

    Go 编译器独立算出净栈效应，本模块用自己的 opcode 表算一遍——两者逐块相等是
    抽象值栈正确性的唯一强证据（静态 JUMP 不 pop、LOG 的 topic 数、DUP/SWAP 的
    零净效应都在这条里被覆盖）。
    """
    assert validate_stack_effects(list(_blocks(name))) == ()


def test_stack_effect_selfcheck_covers_1592_blocks():
    """三合约合计 1592 块，零处不符（方案 §6 阶段 0 的验收口径）。"""
    total = sum(len(_blocks(name)) for name in CONTRACTS)
    assert total == 1592
    for name in CONTRACTS:
        assert validate_stack_effects(list(_blocks(name))) == ()


# ---------------------------------------------------------------------------
# 2. 唯一率与二元分布
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_entry_msize_unique_ratio(name):
    """入口 MSize 静态唯一率：ENS 93.7% / CErc20 43.6% / Safe 51.9%。"""
    expected_blocks, expected_unique, _, _, _ = EXPECTED_DISTRIBUTION[name]
    stats = _abstraction(name).stats

    assert stats.contract_blocks == expected_blocks
    # 三合约的每个块都可达；不可达块不进映射（它们没有"入口值"可言）。
    assert stats.reachable_blocks == expected_blocks
    assert stats.unique_blocks == expected_unique

    expected_ratio = {"ENSRegistry": 93.7, "CErc20": 43.6, "Safe": 51.9}[name]
    assert round(stats.unique_ratio * 100, 1) == expected_ratio


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_value_set_distribution_is_binary(name):
    """**5–16 档恒为 0**：方案 §3.3 最重要的结构性发现。

    没有中间桶——深度类那种"按值分桶"在 MSize 上退化成「唯一 vs ⊤」两档。一旦
    这一档冒出非零，说明抽象域精度掉到了"能算但算不准"的中间地带，专门化的
    分桶策略（每块一个定理）就得重新设计，必须立刻发现。
    """
    _, unique, small, medium, top = EXPECTED_DISTRIBUTION[name]
    stats = _abstraction(name).stats

    assert stats.medium_set_blocks == 0
    assert stats.medium_set_blocks == medium
    assert stats.unique_blocks == unique
    assert stats.small_set_blocks == small
    assert stats.top_blocks == top
    assert unique + small + medium + top == stats.reachable_blocks


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_unique_values_concentrate_on_0x60(name):
    """唯一值高度集中在 0x60（scratch 区 0x00–0x60，free pointer 停在 0x80）。"""
    abstraction = _abstraction(name)
    expected = {"ENSRegistry": 113, "CErc20": 288, "Safe": 376}[name]
    with_0x60 = sum(
        1
        for values in abstraction.msize.values()
        if values is not TOP and 0x60 in values
    )
    assert with_0x60 == expected

    histogram = abstraction.stats.unique_value_histogram
    top_value = max(histogram, key=lambda v: histogram[v])
    assert top_value == 0x60
    # 唯一值块里 0x60 占绝大多数
    assert histogram[0x60] / abstraction.stats.unique_blocks > 0.9


# ---------------------------------------------------------------------------
# 3. 五个成败点热块（方案 §4.1 直接依赖）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(EXPECTED_HOT_BLOCKS))
def test_hot_block_conclusions(name):
    abstraction = _abstraction(name)
    for pc, (expected_msize, expected_fmp) in EXPECTED_HOT_BLOCKS[name].items():
        assert abstraction.msize[pc] == expected_msize, f"{name} pc={pc} msize"
        assert abstraction.fmp[pc] == expected_fmp, f"{name} pc={pc} fmp"

        if expected_msize is TOP:
            assert abstraction.is_top(pc)
            assert abstraction.unique_msize(pc) is None
            assert abstraction.specialization(pc) is None
        else:
            # 联合可专门化：§4.1 的判据是 msize 与 fmp **同时**具体。
            assert abstraction.specialization(pc) == (
                next(iter(expected_msize)),
                expected_fmp,
            )


def test_cerc20_8186_top_is_inherited_from_upstream():
    """CErc20 8186 是纯继承的 ⊤：源站点全在上游块 4236/7916/11250。"""
    abstraction = _abstraction("CErc20")
    sources = abstraction.top_sources[8186]
    assert {s.block_pc for s in sources} == {4236, 7916, 11250}
    assert all(s.block_pc != 8186 for s in sources)
    assert {s.cause for s in sources} == {"MLOAD@0x40"}


def test_safe_5377_top_comes_from_calldatacopy_site():
    """Safe 5377 是真·动态块（19 个内存 op 里 18 个偏移动态）。"""
    abstraction = _abstraction("Safe")
    assert abstraction.top_sources[5377] == (
        TopSource(9351, 9361, "CALLDATACOPY", "CALLDATALOAD"),
    )


def test_safe_6275_unique_msize_depends_on_provenance():
    """Safe 6275 的 0x60 是上下文敏感 CFG 挣来的：保守对照下退化成 ⊤。

    这条守的是"不要用裸 build_evm_cfg"这条纪律——静态返回边把 callee 连回所有
    caller，6275 就会在假路径上被 join 成 ⊤。
    """
    assert _abstraction("Safe").msize[6275] == frozenset({0x60})
    conservative = _abstraction("Safe", False, True)
    assert conservative.msize[6275] is TOP
    # 保守对照整体更差，是真结论的下界。
    assert conservative.stats.unique_blocks < _abstraction("Safe").stats.unique_blocks


# ---------------------------------------------------------------------------
# 4. ⊤ 的结构：msize=⊤ ⟺ fmp=⊤，且几乎全是继承
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_top_msize_implies_top_fmp(name):
    """msize=⊤ ⇒ fmp=⊤，零例外（CErc20 0/404、Safe 0/350）。

    两者同生共死是 §4.1"联合注入"能落地的前提：不存在"msize 不可知但 fmp 可知"
    的块，所以不需要为半可知的块设计第三种降级模式。
    """
    abstraction = _abstraction(name)
    exceptions = [pc for pc in abstraction.top_blocks() if abstraction.fmp[pc] is not TOP]
    assert exceptions == []


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_top_is_inherited_not_self_produced(name):
    """⊤ 几乎全是"继承"不是"自产"：CErc20 402/404、Safe 349/350。"""
    expected = {
        "ENSRegistry": (0, 0, 0),
        "CErc20": (402, 2, 0),
        "Safe": (349, 1, 0),
    }[name]
    stats = _abstraction(name).stats
    assert (
        stats.inherited_top_blocks,
        stats.self_top_blocks,
        stats.unattributed_top_blocks,
    ) == expected
    assert sum(expected) == stats.top_blocks


def test_top_source_sites_are_few_and_concentrated():
    """§4.5b 攻坚清单：源站点极少（28 / 8），且单站点解释成片的 ⊤ 块。"""
    cerc20 = _abstraction("CErc20")
    safe = _abstraction("Safe")

    assert len(cerc20.stats.top_source_sites) == 28
    assert len(safe.stats.top_source_sites) == 8

    (cerc20_site, cerc20_count), *_ = cerc20.top_source_ranking()
    assert cerc20_site == TopSource(4236, 4261, "MSTORE", "MLOAD@0x40")
    assert cerc20_count == 304
    assert cerc20_count >= 300

    (safe_site, safe_count), *_ = safe.top_source_ranking()
    assert safe_site == TopSource(9351, 9361, "CALLDATACOPY", "CALLDATALOAD")
    assert safe_count == 255
    assert safe_count >= 250


def test_ens_has_no_top_blocks():
    abstraction = _abstraction("ENSRegistry")
    assert abstraction.top_blocks() == ()
    assert abstraction.stats.top_source_sites == {}


# ---------------------------------------------------------------------------
# 5. 区间：下界有信息，上界没有（方案 §4.3 否决区间路线的依据）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", sorted(CONTRACTS))
def test_upper_bound_is_uninformative_on_top_blocks(name):
    """所有 ⊤ 块的上界恒为 CAP —— 区间上界零信息，不要指望它救 ⊤ 块。"""
    abstraction = _abstraction(name)
    assert all(
        abstraction.upper_bounds[pc] >= MEM_CAP for pc in abstraction.top_blocks()
    )


def test_lower_bound_is_informative():
    """下界不平凡：CErc20 的 0x60/0xa0/0xc0/0x120 是 §4.3 里"可做的小改进"的依据。"""
    abstraction = _abstraction("CErc20")
    histogram = {}
    for value in abstraction.lower_bounds.values():
        histogram[value] = histogram.get(value, 0) + 1
    assert histogram[0x60] == 594
    assert histogram[0xA0] == 78
    assert histogram[0xC0] == 31
    assert histogram[0x120] == 18


# ---------------------------------------------------------------------------
# 6. ⊤ 哨兵的语义
# ---------------------------------------------------------------------------


def test_top_is_a_distinct_sentinel():
    """⊤ 不是 None、不是空集、不是 falsy（方案 §2.3：它不是一个"桶"）。"""
    assert TOP is not None
    assert TOP != frozenset()
    assert TOP != 0
    assert bool(TOP) is True
    # 单例：两次构造是同一个对象，`is` 判等可靠。
    assert type(TOP)() is TOP

    abstraction = _abstraction("CErc20")
    top_pc = abstraction.top_blocks()[0]
    assert abstraction.msize[top_pc] is TOP
    assert abstraction.unique_msize(top_pc) is None
    assert abstraction.unique_fmp(top_pc) is None
    # 不可达 pc 一律按不可专门化处理，而不是 KeyError 或"默认值"。
    assert abstraction.is_top(-1)
    assert abstraction.specialization(-1) is None


# ---------------------------------------------------------------------------
# 7. 演化规则：以本仓库的实现为准，不是以协议直觉为准
# ---------------------------------------------------------------------------


def _op(kind, **kwargs):
    return EvmOperator(kind=kind, pc=kwargs.pop("pc", 0), **kwargs)


def _block(pc, operations, stack_depth, is_stop=False):
    return EVMBlock(
        pc=pc,
        stack_depth=stack_depth,
        min_depth=0,
        max_depth=1024,
        static_gas=0,
        is_jump_target=False,
        is_inner_block=False,
        is_stop=is_stop,
        operations=list(operations),
    )


def _pushes(values):
    """按 EVM 求值顺序压栈：values[0] 最先被 pop（即最后 PUSH）。"""
    return [_op("PUSH", immediate=v) for v in reversed(values)]


def _entry_msize_of_second_block(first_block_ops, stack_depth):
    """跑"块0（无控制流，落到块1）→ 块1(STOP)"，返回块1 的入口 MSize。"""
    blocks = [
        _block(0, first_block_ops, stack_depth),
        _block(1, [_op("STOP", pc=1)], 0, is_stop=True),
    ]
    return analyze_memory_size(blocks).msize[1]


def test_call_family_does_not_change_msize():
    """**CALL 族在当前模型里不改 MSize** —— 反直觉，但必须与实现一致。

    ``evm_ir/semantics.py::_write_call_return_data`` 明说不建模 host 内部的内存
    扩展，且 CALL 族的 gas 走纯 UF、不经过 ``charge_dynamic_gas``。按协议直觉
    给它补上 ``max(argsOff+argsLen, retOff+retLen)`` 的扩展，抽象解释就会与被
    验证的语义不一致——那不是"更保守"，而是把结论钉在证明域之外。
    """
    for kind, operands in (
        # gas, addr, value, argsOff, argsLen, retOff, retLen
        ("CALL", [0, 0, 0, 0x200, 0x20, 0x100, 0x20]),
        ("CALLCODE", [0, 0, 0, 0x200, 0x20, 0x100, 0x20]),
        # gas, addr, argsOff, argsLen, retOff, retLen
        ("DELEGATECALL", [0, 0, 0x200, 0x20, 0x100, 0x20]),
        ("STATICCALL", [0, 0, 0x200, 0x20, 0x100, 0x20]),
    ):
        ops = _pushes(operands) + [_op(kind, pc=10), _op("POP", pc=11)]
        assert _entry_msize_of_second_block(ops, 0) == frozenset({0}), kind


def test_create_family_does_change_msize():
    """CREATE/CREATE2 相反：它们走 charge_memory_and_word_gas，**要**扩。"""
    # value, offset, size
    ops = _pushes([0, 0x100, 0x20]) + [_op("CREATE", pc=10), _op("POP", pc=11)]
    assert _entry_msize_of_second_block(ops, 0) == frozenset({0x120})
    # value, offset, size, salt
    ops = _pushes([0, 0x100, 0x20, 0]) + [_op("CREATE2", pc=10), _op("POP", pc=11)]
    assert _entry_msize_of_second_block(ops, 0) == frozenset({0x120})


def test_zero_length_access_does_not_expand():
    """``calcMemSize64``：length == 0 ⇒ requested = 0，不扩容。"""
    # destOffset=0x100, offset=0, length=0
    ops = _pushes([0x100, 0, 0]) + [_op("CALLDATACOPY", pc=10)]
    assert _entry_msize_of_second_block(ops, 0) == frozenset({0})

    # 非零长度就要扩：0x100 + 0x20 = 0x120
    ops = _pushes([0x100, 0, 0x20]) + [_op("CALLDATACOPY", pc=10)]
    assert _entry_msize_of_second_block(ops, 0) == frozenset({0x120})


def test_expansion_rounds_up_to_32_bytes():
    """MSize' = max(MSize, ceil32(requested))。"""
    # MSTORE8 at 0x41 ⇒ requested 0x42 ⇒ ceil32 = 0x60
    ops = _pushes([0x41, 0xFF]) + [_op("MSTORE8", pc=10)]
    assert _entry_msize_of_second_block(ops, 0) == frozenset({0x60})


def test_free_memory_pointer_is_tracked():
    """``MSTORE(0x40, 0x80)`` 之后，下游块的 fmp 是具体的 0x80。"""
    ops = _pushes([0x40, 0x80]) + [_op("MSTORE", pc=10)]
    blocks = [
        _block(0, ops, 0),
        _block(1, [_op("STOP", pc=1)], 0, is_stop=True),
    ]
    abstraction = analyze_memory_size(blocks)
    assert abstraction.fmp[1] == 0x80
    assert abstraction.specialization(1) == (0x60, 0x80)
    # 关掉常量内存追踪即 free pointer 不可知（归因对照）。
    assert analyze_memory_size(blocks, track_constant_memory=False).fmp[1] is TOP


def test_dynamic_offset_makes_msize_top_with_source_site():
    """动态偏移的内存写把 MSize 打成 ⊤，并记下源站点。"""
    # 先压待写入的值，再让 CALLDATALOAD 产生一个**未知的偏移**留在栈顶。
    ops = [
        _op("PUSH", immediate=0xFF, pc=9),
        _op("PUSH", immediate=0, pc=10),
        _op("CALLDATALOAD", pc=11),
        _op("MSTORE", pc=12),
    ]
    blocks = [
        _block(0, ops, 0),
        _block(1, [_op("STOP", pc=1)], 0, is_stop=True),
    ]
    abstraction = analyze_memory_size(blocks)
    assert abstraction.msize[1] is TOP
    assert abstraction.top_sources[1] == (
        TopSource(0, 12, "MSTORE", "CALLDATALOAD"),
    )


# ---------------------------------------------------------------------------
# 8. fail-closed
# ---------------------------------------------------------------------------


def test_unmodelled_opcode_is_rejected():
    blocks = [_block(0, [_op("NOTANOPCODE", pc=0)], 0)]
    with pytest.raises(MSizeAnalysisError, match="未建模的 opcode"):
        analyze_memory_size(blocks)


def test_stack_depth_mismatch_is_rejected():
    """自校验失败必须抛，不能返回"尽力而为的部分结果"。"""
    blocks = [_block(0, [_op("PUSH", immediate=1)], stack_depth=7)]
    with pytest.raises(MSizeAnalysisError, match="自校验失败"):
        analyze_memory_size(blocks)


def test_iteration_budget_exhaustion_is_rejected():
    """不动点没收敛 ⇒ 拒绝返回（预算调到 1 制造这个情形）。"""
    with pytest.raises(MSizeAnalysisError, match="未在 1 次迭代内收敛"):
        analyze_memory_size(list(_blocks("CErc20")), iteration_budget=1)


def test_empty_program_is_rejected():
    with pytest.raises(MSizeAnalysisError):
        analyze_memory_size([])
