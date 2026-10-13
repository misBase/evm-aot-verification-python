import os

import pytest
from z3 import (
    And,
    Array,
    BitVec,
    BitVecSort,
    BitVecVal,
    Not,
    Select,
    Solver,
    Store,
    ULE,
    ULT,
    sat,
    unknown,
    unsat,
)

import x86_64.summaries.copy_loop as copy_loop_module

from state.smt_state import PointerTag, SMTState
from common.memory_copy import (
    relational_getdata_copy_memory,
    relational_mcopy_memory,
)
from x86_64.cfg import identify_basic_blocks
from x86_64.cfg_executor import X86SymbolicExecutor
from x86_64.disassembler import disassemble_hex
from x86_64.loop_analysis import build_x86_cfg
from x86_64.models import Register
from x86_64.summaries import (
    SummaryPreconditionError,
    X86SummaryConfig,
    build_x86_summary_runtime,
)
from x86_64.summaries.base import (
    SummaryContinuation,
    SummaryDiscoveryContext,
    SummarySingleEntryError,
    X86Summary,
    find_summary_bypass_edges,
    require_single_entry,
)
from x86_64.summaries.copy_loop import COPY_LOOP_SUMMARY_KIND, CopyLoopPayload

from tests.unit.test_tier2_templates import _CDC_HEX

_CERC20_HEX = os.path.join(
    os.path.dirname(__file__), "..", "data", "ext_contracts",
    "compound_cerc20", "CErc20.hex",
)


def _cdc_blocks():
    return identify_basic_blocks(disassemble_hex(_CDC_HEX, base_addr=0))


def _cerc20_runtime(hex_str=None):
    if hex_str is None:
        hex_str = open(_CERC20_HEX).read().strip()
    blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    return build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )


def _cerc20_ctx():
    """CErc20 的 discovery 上下文（strict 测试用，绕开 runtime 构造）。"""
    blocks = identify_basic_blocks(
        disassemble_hex(open(_CERC20_HEX).read().strip(), base_addr=0)
    )
    return SummaryDiscoveryContext(
        blocks=blocks,
        blocks_by_addr={b.start_addr: b for b in blocks},
        block_index={b.start_addr: i for i, b in enumerate(blocks)},
    )


def _mcopy_high_summary(runtime):
    return next(
        s for s in runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
        if s.payload.template == "mcopy-high-word"
    )


def _mcopy_low_summary(runtime):
    return next(
        s for s in runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
        if s.payload.template == "mcopy-low-word"
    )


def _seed_mcopy_high_state(binding, *, dst, src, size):
    state = SMTState.create_initial_state(num_inputs=0)
    r15 = BitVecVal(0x1000, 64)
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["DST"]), dst)
    state.x86_registers.set_pointer_tag(Register(binding["DST"]), PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["SRC"]), src)
    state.x86_registers.set_pointer_tag(Register(binding["SRC"]), PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["S"]), size)
    return state, r15


def test_copy_loop_summary_is_explicitly_enabled():
    blocks = _cdc_blocks()

    disabled = build_x86_summary_runtime(blocks, summary_config=X86SummaryConfig.disabled())
    enabled = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )

    assert disabled.summaries == []
    assert len(enabled.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)) == 1
    summary = enabled.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    assert isinstance(summary.payload, CopyLoopPayload)
    assert summary.payload.template == "makedata-byte-copy"


def test_summary_precondition_error_keeps_full_premise_but_truncates_message():
    premise = "p" * 2000
    error = SummaryPreconditionError(
        kind="copy_loop",
        label="test",
        premise=premise,
        result=unknown,
        location=(0x10, 0),
    )

    assert error.premise == premise
    assert "<truncated 1000 chars>" in str(error)
    assert len(str(error)) < 1200


def test_makedata_copy_loop_summary_applies_getdata_closed_form():
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    r15 = BitVecVal(0x1000, 64)
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["S"]), BitVecVal(3, 64))
    state.x86_registers.set_register(Register(binding["OFF"]), BitVecVal(0, 64))
    state.x86_registers.set_register(Register(binding["LEN"]), BitVecVal(2, 64))
    state.x86_registers.set_register(Register(binding["DST"]), BitVecVal(0, 64))
    state.x86_registers.set_register(Register(binding["INP"]), state.callengine_input_pointer)
    state.x86_registers.set_pointer_tag(Register(binding["INP"]), PointerTag.CALLDATA_PTR)

    mem0 = Array("copy_loop_test_mem0", BitVecSort(64), BitVecSort(8))
    addr = BitVec("copy_loop_test_addr", 64)
    state.x86_memory.evm_mem = mem0

    out = runtime.apply(summary, state, path_condition=True)

    solver = Solver()
    solver.add(
        Not(
            Select(out.x86_memory.evm_mem, r15 + BitVecVal(0, 64))
            == Select(state.calldata, BitVecVal(0, 64))
        )
    )
    assert solver.check() == unsat

    solver = Solver()
    solver.add(
        Not(
            Select(out.x86_memory.evm_mem, r15 + BitVecVal(1, 64))
            == Select(state.calldata, BitVecVal(1, 64))
        )
    )
    assert solver.check() == unsat

    solver = Solver()
    solver.add(
        Not(
            Select(out.x86_memory.evm_mem, r15 + BitVecVal(2, 64))
            == BitVecVal(0, 8)
        )
    )
    assert solver.check() == unsat


@pytest.mark.skip(
    reason="relational memory 抽象（SMTState.abstract_mcopy_memory / "
    "abstract_getdata_copy_memory）在 develop 上未启用。它**必须与 "
    "evm_ir/semantics.py 的对应分支成对开启**——只开 x86 一侧，两侧内存表示"
    "不同，等价性检查必然 SAT。copy_loop.py 用 getattr(..., False) 读这两个开关，"
    "缺字段即恒 False，相关分支静态死，因此 summary 本身照常工作。"
)
def test_makedata_copy_loop_summary_uses_shared_relational_transformer():
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    state.abstract_getdata_copy_memory = True
    state.callengine_memory_base = BitVecVal(0, 64)
    state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["S"]), BitVecVal(3, 64))
    state.x86_registers.set_register(Register(binding["OFF"]), BitVecVal(5, 64))
    state.x86_registers.set_register(Register(binding["LEN"]), BitVecVal(2, 64))
    state.x86_registers.set_register(Register(binding["DST"]), BitVecVal(0x40, 64))
    state.x86_registers.set_register(
        Register(binding["INP"]),
        state.callengine_input_pointer,
    )
    state.x86_registers.set_pointer_tag(
        Register(binding["INP"]),
        PointerTag.CALLDATA_PTR,
    )
    mem0 = Array("copy_loop_relational_mem0", BitVecSort(64), BitVecSort(8))
    state.x86_memory.evm_mem = mem0

    out = runtime.apply(summary, state, path_condition=True)

    assert out.x86_memory.evm_mem.eq(
        relational_getdata_copy_memory(
            mem0,
            state.calldata,
            BitVecVal(0x40, 64),
            BitVecVal(5, 64),
            BitVecVal(3, 64),
            BitVecVal(2, 64),
        )
    )


def test_makedata_byte_copy_rejects_unproved_symbolic_no_wrap():
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.R15, BitVecVal(0x1000, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["S"]), BitVec("copy_size", 64))
    state.x86_registers.set_register(Register(binding["OFF"]), BitVec("copy_off", 64))
    state.x86_registers.set_register(Register(binding["LEN"]), BitVec("copy_len", 64))
    state.x86_registers.set_register(Register(binding["DST"]), BitVec("copy_dst", 64))
    state.x86_registers.set_register(Register(binding["INP"]), state.callengine_input_pointer)
    state.x86_registers.set_pointer_tag(Register(binding["INP"]), PointerTag.CALLDATA_PTR)

    with pytest.raises(SummaryPreconditionError, match="no-wrap#0"):
        runtime.apply(summary, state, path_condition=True)

    assert state.assumptions is None
    assert runtime.assumed_premises == []


def test_fallback_mode_executes_original_loop_after_precondition_failure():
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    binding = summary.payload.binding
    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.R15, BitVecVal(0x1000, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    for name in ("S", "OFF", "LEN", "DST"):
        state.x86_registers.set_register(
            Register(binding[name]), BitVec(f"fallback_{name}", 64)
        )
    state.x86_registers.set_register(
        Register(binding["INP"]), state.callengine_input_pointer
    )
    state.x86_registers.set_pointer_tag(
        Register(binding["INP"]), PointerTag.CALLDATA_PTR
    )

    executor = X86SymbolicExecutor(
        blocks,
        max_depth=3,
        use_reachability_check=False,
        enable_go_bridge=False,
        enable_merge=False,
        summary_runtime=runtime,
    )
    executor.execute(state, entry_addr=summary.start_block_addr)

    assert len(runtime.precondition_failures) == 1
    assert runtime.assumed_premises == []
    assert not executor.path_coverage_certificate().complete


def test_unknown_summary_premise_is_fail_closed(monkeypatch):
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="strict"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    state = SMTState.create_initial_state(num_inputs=0)
    binding = summary.payload.binding
    state.x86_registers.set_register(
        Register(binding["INP"]), state.callengine_input_pointer
    )
    state.x86_registers.set_pointer_tag(
        Register(binding["INP"]), PointerTag.CALLDATA_PTR
    )
    monkeypatch.setattr(
        copy_loop_module,
        "_implication_result",
        lambda *_args, **_kwargs: unknown,
    )

    with pytest.raises(SummaryPreconditionError) as raised:
        runtime.apply(summary, state, path_condition=True)

    assert raised.value.result == unknown
    assert state.assumptions is None


def test_copy_summary_uses_runtime_precondition_timeout(monkeypatch):
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="strict"),
    )
    runtime.precondition_timeout_ms = 12345
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    state = SMTState.create_initial_state(num_inputs=0)
    binding = summary.payload.binding
    state.x86_registers.set_register(
        Register(binding["INP"]), state.callengine_input_pointer
    )
    state.x86_registers.set_pointer_tag(
        Register(binding["INP"]), PointerTag.CALLDATA_PTR
    )
    seen = []

    def _record_timeout(*_args, **kwargs):
        seen.append(kwargs.get("timeout_ms"))
        return unknown

    monkeypatch.setattr(copy_loop_module, "_implication_result", _record_timeout)
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, path_condition=True)

    assert seen
    assert all(timeout == 12345 for timeout in seen)


def test_combined_unknown_accepts_only_when_all_components_are_proved(monkeypatch):
    results = iter((unknown, unsat, unsat))
    cache_ids = []

    def _result(*_args, **kwargs):
        cache_ids.append(id(kwargs["_forward_cache"]))
        return next(results)

    monkeypatch.setattr(
        copy_loop_module,
        "_implication_result",
        _result,
    )

    copy_loop_module._require_all_implied(
        path_condition=True,
        assumptions=[],
        labelled_premises=(
            ("first", BitVecVal(1, 8) == BitVecVal(1, 8)),
            ("second", BitVecVal(2, 8) == BitVecVal(2, 8)),
        ),
        timeout_ms=321,
    )
    assert len(set(cache_ids)) == 1


def test_combined_unknown_reports_first_unproved_component(monkeypatch):
    results = iter((unknown, unsat, unknown))
    monkeypatch.setattr(
        copy_loop_module,
        "_implication_result",
        lambda *_args, **_kwargs: next(results),
    )

    with pytest.raises(SummaryPreconditionError, match="second") as raised:
        copy_loop_module._require_all_implied(
            path_condition=True,
            assumptions=[],
            labelled_premises=(
                ("first", BitVecVal(1, 8) == BitVecVal(1, 8)),
                ("second", BitVecVal(2, 8) == BitVecVal(2, 8)),
            ),
            timeout_ms=321,
        )

    assert raised.value.result == unknown


def test_combined_sat_remains_fail_closed_even_if_components_report_unsat(
    monkeypatch,
):
    results = iter((sat, unsat, unsat))
    monkeypatch.setattr(
        copy_loop_module,
        "_implication_result",
        lambda *_args, **_kwargs: next(results),
    )

    with pytest.raises(
        SummaryPreconditionError, match="combined summary premises"
    ) as raised:
        copy_loop_module._require_all_implied(
            path_condition=True,
            assumptions=[],
            labelled_premises=(
                ("first", BitVecVal(1, 8) == BitVecVal(1, 8)),
                ("second", BitVecVal(2, 8) == BitVecVal(2, 8)),
            ),
            timeout_ms=321,
        )

    assert raised.value.result == sat


def test_summary_premise_proof_forwards_exact_deep_store_chain():
    memory = Array("copy_premise_memory", BitVecSort(64), BitVecSort(8))
    address = BitVec("copy_premise_address", 64)
    updated = memory
    for offset in range(128):
        updated = Store(
            updated,
            address + BitVecVal(offset, 64),
            BitVecVal(offset, 8),
        )

    copy_loop_module._require_all_implied(
        path_condition=True,
        assumptions=[],
        labelled_premises=(
            (
                "forwarded-byte",
                Select(updated, address + BitVecVal(73, 64))
                == BitVecVal(73, 8),
            ),
        ),
        timeout_ms=1000,
    )


@pytest.mark.parametrize("fact_source", ("path", "assumptions"))
def test_summary_premise_structural_fact_fast_path_flattens_nested_and(
    monkeypatch,
    fact_source,
):
    address = BitVecVal(0x1000, 64)
    value = BitVec("copy_structural_fact_value", 8)
    expected = BitVecVal(0x42, 8)
    memory = Store(
        Array("copy_structural_fact_memory", BitVecSort(64), BitVecSort(8)),
        address,
        value,
    )
    for offset in range(256):
        memory = Store(
            memory,
            BitVecVal(offset, 64),
            BitVecVal(offset & 0xFF, 8),
        )
    giant_fact = Select(memory, address) == expected
    nested_fact = And(
        BitVecVal(1, 8) == BitVecVal(1, 8),
        And(
            BitVecVal(2, 8) == BitVecVal(2, 8),
            giant_fact,
        ),
    )

    def reject_solver(*_args, **_kwargs):
        raise AssertionError("exact antecedent fact should bypass SolverFor")

    monkeypatch.setattr(copy_loop_module, "SolverFor", reject_solver)
    result = copy_loop_module._implication_result(
        nested_fact if fact_source == "path" else True,
        [nested_fact] if fact_source == "assumptions" else [],
        value == expected,
        timeout_ms=1,
        _forward_cache={},
    )

    assert result == unsat


@pytest.mark.parametrize(
    ("antecedent", "premise"),
    (
        (
            lambda value: Not(value == BitVecVal(7, 64)),
            lambda value: value == BitVecVal(7, 64),
        ),
        (
            lambda value: ULE(value, BitVecVal(10, 64)),
            lambda value: ULT(value, BitVecVal(10, 64)),
        ),
    ),
)
def test_summary_premise_structural_fact_fast_path_rejects_nonmatches(
    monkeypatch,
    antecedent,
    premise,
):
    value = BitVec("copy_structural_nonmatch_value", 64)
    real_solver_for = copy_loop_module.SolverFor
    solver_calls = []

    def recording_solver_for(*args, **kwargs):
        solver_calls.append((args, kwargs))
        return real_solver_for(*args, **kwargs)

    monkeypatch.setattr(copy_loop_module, "SolverFor", recording_solver_for)
    result = copy_loop_module._implication_result(
        antecedent(value),
        [],
        premise(value),
        timeout_ms=1000,
        _forward_cache={},
    )

    assert result == sat
    assert solver_calls


def test_array_reading_premise_is_tried_by_the_plain_solver_first(monkeypatch):
    # Operands loaded from a Store chain: forwarding the premise is the slow
    # part, so a bounded plain query runs first. Only UNSAT short-circuits.
    memory = Array("copy_plain_first_memory", BitVecSort(64), BitVecSort(8))
    for offset in range(64):
        memory = Store(memory, BitVecVal(offset, 64), BitVec(f"copy_plain_first_{offset}", 8))
    size = Select(memory, BitVec("copy_plain_first_address", 64))
    real_forward_selects = copy_loop_module.forward_selects
    forwarded = []
    monkeypatch.setattr(copy_loop_module, "forward_selects",
                        lambda expr, _cache=None: forwarded.append(1) or real_forward_selects(expr, _cache=_cache))
    implied = copy_loop_module._implication_result(ULT(size, 100), [], ULT(size, 200), timeout_ms=1000)
    assert implied == unsat and not forwarded
    refuted = copy_loop_module._implication_result(ULT(size, 200), [], ULT(size, 100), timeout_ms=1000)
    assert refuted == sat and forwarded


def test_structural_fact_fallback_reuses_one_forward_cache(monkeypatch):
    left = BitVec("copy_shared_cache_left", 64) == BitVecVal(1, 64)
    right = BitVec("copy_shared_cache_right", 64) == BitVecVal(2, 64)
    path_condition = And(left, And(right))
    real_forward_selects = copy_loop_module.forward_selects
    cache_ids = []
    solver_checks = []

    def recording_forward_selects(expr, _cache=None):
        cache_ids.append(id(_cache))
        return real_forward_selects(expr, _cache=_cache)

    class UnknownSolver:
        def set(self, *_args, **_kwargs):
            return None

        def add(self, *_args, **_kwargs):
            return None

        def check(self):
            solver_checks.append(True)
            return unknown

    monkeypatch.setattr(
        copy_loop_module,
        "forward_selects",
        recording_forward_selects,
    )
    monkeypatch.setattr(
        copy_loop_module,
        "SolverFor",
        lambda *_args, **_kwargs: UnknownSolver(),
    )

    copy_loop_module._require_all_implied(
        path_condition=path_condition,
        assumptions=[],
        labelled_premises=(("left", left), ("right", right)),
        timeout_ms=1,
    )

    assert len(solver_checks) == 1
    assert cache_ids
    assert len(set(cache_ids)) == 1


def test_makedata_byte_copy_rejects_shifted_source_pointer():
    blocks = _cdc_blocks()
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)[0]
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    state.x86_registers.set_register(Register.R15, BitVecVal(0x1000, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["S"]), BitVecVal(2, 64))
    state.x86_registers.set_register(Register(binding["OFF"]), BitVecVal(0, 64))
    state.x86_registers.set_register(Register(binding["LEN"]), BitVecVal(2, 64))
    state.x86_registers.set_register(Register(binding["DST"]), BitVecVal(0, 64))
    state.x86_registers.set_register(
        Register(binding["INP"]),
        state.callengine_input_pointer + BitVecVal(1, 64),
    )
    state.x86_registers.set_pointer_tag(Register(binding["INP"]), PointerTag.CALLDATA_PTR)

    with pytest.raises(ValueError, match="source.*pointer value"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_cerc20_copy_loop_summary_discovers_both_mcopy_clusters():
    runtime = _cerc20_runtime()
    summaries = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
    successors, _unresolved = build_x86_cfg(runtime.blocks)
    clusters = sorted(
        (
            summary for summary in summaries
            if summary.payload.template.startswith("mcopy")
        ),
        key=lambda s: s.entry_addr,
    )

    assert len(summaries) == 36
    # 这 36 条全部通过了 §5.4 的单入口检查（发现期强制，见
    # TestSingleEntryCheck）——CErc20 上没有任何外部边绕过 summary 入口直插
    # 覆盖区中段，所以折叠数不受该检查影响。
    assert [
        (s.payload.template, s.entry_addr, s.continuation.block_addr)
        for s in clusters
    ] == [
        ("mcopy-high-word", 0xAD23D, 0xAD2AA),
        ("mcopy-low-word", 0xAD2AC, 0xAD2E5),
    ]

    high = clusters[0]
    covered = set(high.covered_block_addrs)
    # preamble/align + glue1/glue2 必须被替换吞掉；trampoline 留给执行器
    assert {0xAD23D, 0xAD246, 0xAD274, 0xAD277} <= covered
    assert 0xAD2AA not in covered


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_summary_applies_closed_form():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding

    state, r15 = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x1040, 64),
        src=BitVecVal(0x1020, 64),
        size=BitVecVal(12, 64),
    )
    mem0 = Array("mcopy_high_test_mem0", BitVecSort(64), BitVecSort(8))
    state.x86_memory.evm_mem = mem0

    out = runtime.apply(summary, state, path_condition=True)

    for k in (0, 11):
        solver = Solver()
        solver.add(
            Not(
                Select(out.x86_memory.evm_mem, r15 + BitVecVal(0x40 + k, 64))
                == Select(mem0, BitVecVal(0x1020 + k, 64))
            )
        )
        assert solver.check() == unsat, f"copied byte {k} mismatch"

    solver = Solver()
    solver.add(
        Not(
            Select(out.x86_memory.evm_mem, r15 + BitVecVal(0x40 + 12, 64))
            == Select(mem0, BitVecVal(0x104C, 64))
        )
    )
    assert solver.check() == unsat, "byte outside copy region must be untouched"

    solver = Solver()
    solver.add(
        Not(
            out.x86_registers.get_register(Register(binding["S"]))
            == BitVecVal(0, 64)
        )
    )
    assert solver.check() == unsat, "size register must drain to zero"


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
@pytest.mark.skip(
    reason="relational memory 抽象（SMTState.abstract_mcopy_memory / "
    "abstract_getdata_copy_memory）在 develop 上未启用。它**必须与 "
    "evm_ir/semantics.py 的对应分支成对开启**——只开 x86 一侧，两侧内存表示"
    "不同，等价性检查必然 SAT。copy_loop.py 用 getattr(..., False) 读这两个开关，"
    "缺字段即恒 False，相关分支静态死，因此 summary 本身照常工作。"
)
def test_mcopy_high_summary_uses_shared_relational_transformer_when_enabled():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding
    state, _ = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x40, 64),
        src=BitVecVal(0x20, 64),
        size=BitVecVal(12, 64),
    )
    state.x86_registers.set_register(Register.R15, BitVecVal(0, 64))
    state.callengine_memory_base = BitVecVal(0, 64)
    state.abstract_mcopy_memory = True
    mem0 = Array("mcopy_relational_mem0", BitVecSort(64), BitVecSort(8))
    state.x86_memory.evm_mem = mem0

    out = runtime.apply(summary, state, path_condition=True)

    assert out.x86_memory.evm_mem.eq(
        relational_mcopy_memory(
            mem0,
            BitVecVal(0x40, 64),
            BitVecVal(0x20, 64),
            BitVecVal(12, 64),
        )
    )


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_summary_requires_evm_pointer_tags():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    r15 = BitVecVal(0x1000, 64)
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["DST"]), r15 + BitVecVal(0x40, 64))
    state.x86_registers.set_register(Register(binding["SRC"]), r15 + BitVecVal(0x20, 64))
    state.x86_registers.set_register(Register(binding["S"]), BitVecVal(12, 64))

    with pytest.raises(ValueError, match="destination.*evm_ptr"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_summary_rejects_wrong_direction():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding

    state, _ = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x1020, 64),
        src=BitVecVal(0x1040, 64),
        size=BitVecVal(12, 64),
    )

    with pytest.raises(ValueError, match="direction premise"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_summary_rejects_small_size():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding

    state, _ = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x1040, 64),
        src=BitVecVal(0x1020, 64),
        size=BitVecVal(4, 64),
    )

    with pytest.raises(ValueError, match="size premise"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_summary_rejects_unproved_symbolic_no_wrap():
    runtime = _cerc20_runtime()
    summary = _mcopy_high_summary(runtime)
    binding = summary.payload.binding

    r15 = BitVecVal(0x1000, 64)
    dst = BitVec("mcopy_high_dst", 64)
    src = BitVec("mcopy_high_src", 64)
    size = BitVec("mcopy_high_size", 64)
    state, _ = _seed_mcopy_high_state(binding, dst=dst, src=src, size=size)

    path_condition = And(
        ULT(src - r15, dst - r15),
        ULT(BitVecVal(8, 64), size),
    )
    with pytest.raises(SummaryPreconditionError, match="no-wrap#0"):
        runtime.apply(summary, state, path_condition=path_condition)

    assert state.assumptions is None
    assert runtime.assumed_premises == []


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_high_discovery_fail_closed_on_perturbed_align_block():
    hex_str = open(_CERC20_HEX).read().strip().lower()
    # align 块（0xad246）唯一序列：add rax,rdx; add rcx,rdx; sub rcx,8; sub rax,8
    original = "4801d04801d14883e9084883e808"
    perturbed = "4801d04801d14883e9044883e808"  # sub rcx,8 → sub rcx,4
    assert hex_str.count(original) == 1
    runtime = _cerc20_runtime(hex_str.replace(original, perturbed))

    summaries = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
    templates = {s.payload.template for s in summaries}
    assert "mcopy-high-word" not in templates
    assert "mcopy-low-word" in templates


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_low_summary_requires_evm_pointer_tags():
    blocks = identify_basic_blocks(
        disassemble_hex(open(_CERC20_HEX).read().strip(), base_addr=0)
    )
    runtime = build_x86_summary_runtime(
        blocks,
        summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
    )
    summary = next(
        s for s in runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
        if s.payload.template == "mcopy-low-word"
    )
    binding = summary.payload.binding

    state = SMTState.create_initial_state(num_inputs=0)
    r15 = BitVecVal(0x1000, 64)
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(binding["DST"]), r15)
    state.x86_registers.set_register(Register(binding["SRC"]), r15 + BitVecVal(0x20, 64))
    state.x86_registers.set_register(Register(binding["S"]), BitVecVal(8, 64))

    with pytest.raises(ValueError, match="destination.*evm_ptr"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_low_summary_accepts_reversed_overlap_when_size_is_small():
    runtime = _cerc20_runtime()
    summary = _mcopy_low_summary(runtime)
    binding = summary.payload.binding
    state, r15 = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x1024, 64),
        src=BitVecVal(0x1020, 64),
        size=BitVecVal(4, 64),
    )
    mem0 = Array("mcopy_low_small_mem0", BitVecSort(64), BitVecSort(8))
    state.x86_memory.evm_mem = mem0

    out = runtime.apply(summary, state, path_condition=True)

    for k in range(4):
        solver = Solver()
        solver.add(
            Not(
                Select(out.x86_memory.evm_mem, r15 + BitVecVal(0x24 + k, 64))
                == Select(mem0, r15 + BitVecVal(0x20 + k, 64))
            )
        )
        assert solver.check() == unsat, f"copied byte {k} mismatch"


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_low_summary_rejects_reversed_overlap_when_size_exceeds_qword():
    runtime = _cerc20_runtime()
    summary = _mcopy_low_summary(runtime)
    binding = summary.payload.binding
    state, _ = _seed_mcopy_high_state(
        binding,
        dst=BitVecVal(0x1040, 64),
        src=BitVecVal(0x1020, 64),
        size=BitVecVal(12, 64),
    )

    with pytest.raises(SummaryPreconditionError, match="dispatch premise"):
        runtime.apply(summary, state, path_condition=True)


@pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
def test_mcopy_low_signed_dispatch_proves_under_normalized_memory_base():
    runtime = _cerc20_runtime()
    summary = _mcopy_low_summary(runtime)
    binding = summary.payload.binding
    r15 = BitVec("normalized_mcopy_r15", 64)
    d0 = BitVec("normalized_mcopy_d0", 64)
    s0 = BitVec("normalized_mcopy_s0", 64)
    size = BitVecVal(12, 64)
    state, _ = _seed_mcopy_high_state(
        binding,
        dst=r15 + d0,
        src=r15 + s0,
        size=size,
    )
    state.x86_registers.set_register(Register.R15, r15)
    state.callengine_memory_base = r15
    state.add_assumption(r15 == BitVecVal(0, 64))
    path_condition = And(
        # Actual codegen dispatch is a signed pointer comparison.
        r15 + d0 <= r15 + s0,
        ULT(d0, BitVecVal(1 << 63, 64)),
        ULT(s0, BitVecVal(1 << 63, 64)),
        ULE(d0, d0 + size),
        ULE(s0, s0 + size),
    )

    runtime.apply(summary, state, path_condition=path_condition)

    assert runtime.assumed_premises == []


def test_mcopy_low_summary_does_not_claim_an_unproved_src_final_value():
    """FromLow 的 SRC 终值必须 clobber，不能设成 `src + size`。

    `compileEVMMCOPYFromLow` 的两段循环对 SRC 不对称：word 循环每轮
    `ADDQ 8, srcReg`，尾字节循环只推进 DST、**不动 SRC**（进尾循环前已把最后
    那个 qword 整个载入 tmp）。真实终值是 `s0 + 8*⌊size/8⌋`：

    - `size = 9`   ⇒ 真实 `s0+8`，写成 `s0+9` 就错了
    - `size = 1..7` ⇒ word 循环一轮不跑，SRC 完全不变

    而复合引理 `prove_mcopy_low_composition` 只证了 tmp / mem / DST / S，从未
    证过 SRC。summary 若断言一个既无引理支撑、事实上还错误的值，后续读 SRC 的
    机器码就会在错误状态上继续，可能掩盖不等价——假绿。
    """
    from z3 import BitVec, BitVecVal, Solver, sat

    from x86_64.summaries.copy_loop import _apply_mcopy_low

    # 直接检查源码级契约：SRC 必须出现在 clobber 集合里，而不是 _set_reg
    import inspect

    source = inspect.getsource(_apply_mcopy_low)
    set_reg_lines = [
        line for line in source.splitlines()
        if "_set_reg(result" in line
    ]
    assert not any('binding["SRC"]' in line for line in set_reg_lines), (
        "FromLow summary 又给 SRC 设了精确终值；该值没有引理支撑且与 codegen "
        "不符（尾循环不推进 SRC）"
    )
    assert 'binding["SRC"]' in source.split("_clobber(")[-1], (
        "SRC 没有被 clobber"
    )


class TestStrictModeReportsUnmatchedCandidates:
    """`strict` 参数必须真的被读取（codex review 的降级项）。

    此前 `discover_copy_loop_summaries` 收下 `strict` 却从不使用，于是"看着像
    copy loop 但模板细节对不上"的候选被静默跳过——strict 退化成普通 fallback。
    结论仍健全（该循环照常逐指令执行），但调用方以为折叠生效了。
    """

    def test_strict_is_silent_when_everything_matches(self):
        """CErc20 上 36 条全部命中，strict 不应报任何东西。"""
        from x86_64.summaries.copy_loop import discover_copy_loop_summaries

        ctx = _cerc20_ctx()
        summaries = list(discover_copy_loop_summaries(ctx, strict=True))
        assert len(summaries) == 36

    def test_strict_reports_a_template_that_is_not_proven(self, monkeypatch):
        """模板匹配上了但不在已证集合里 ⇒ strict 必须报告。

        这是 §6 守卫的核心语义：命中一个**未经引理证明**的模板时，静默跳过会
        让调用方以为"这里没有 copy loop"，而实际上有一个没被任何引理覆盖的
        循环被原样执行了。
        """
        import pytest

        import x86_64.summaries.copy_loop as copy_loop_mod
        from x86_64.summaries.base import SummaryMatchError

        ctx = _cerc20_ctx()
        # 把一个真实命中的模板从"已证"集合里摘掉
        reduced = {
            name: spec for name, spec in copy_loop_mod.TEMPLATES.items()
            if name != "returndata-byte-copy"
        }
        monkeypatch.setattr(copy_loop_mod, "TEMPLATES", reduced)

        with pytest.raises(SummaryMatchError, match="not a proven template"):
            list(copy_loop_mod.discover_copy_loop_summaries(ctx, strict=True))

    def test_non_strict_stays_silent_on_the_same_input(self, monkeypatch):
        """同一输入在非 strict 下不抛异常，只是少发现几条（fallback 语义）。"""
        import x86_64.summaries.copy_loop as copy_loop_mod

        ctx = _cerc20_ctx()
        full = list(copy_loop_mod.discover_copy_loop_summaries(ctx))

        reduced = {
            name: spec for name, spec in copy_loop_mod.TEMPLATES.items()
            if name != "returndata-byte-copy"
        }
        monkeypatch.setattr(copy_loop_mod, "TEMPLATES", reduced)
        fewer = list(copy_loop_mod.discover_copy_loop_summaries(ctx))

        assert len(fewer) < len(full)

    def test_copy_loop_shape_heuristic_needs_both_read_and_write(self):
        """`_looks_like_copy_loop` 只用于 strict 的**诊断**，判据保守。

        它要求循环体同时有内存读与内存写——那正是 codegen 拷贝循环的形状。
        判据放松会让 strict 对普通循环发出噪声报告。
        """
        from types import SimpleNamespace

        from x86_64.summaries.copy_loop import _looks_like_copy_loop

        def _blocks(*op_strs):
            insns = [
                SimpleNamespace(mnemonic="mov", op_str=op) for op in op_strs
            ]
            return {0: SimpleNamespace(instructions=insns)}

        loop = SimpleNamespace(body={0})
        assert _looks_like_copy_loop(
            loop, _blocks("rax, qword ptr [rsi]", "qword ptr [rdi], rax")
        )
        # 只读不写 / 只写不读都不算
        assert not _looks_like_copy_loop(loop, _blocks("rax, qword ptr [rsi]"))
        assert not _looks_like_copy_loop(loop, _blocks("qword ptr [rdi], rax"))


# --------------------------------------------------------------------------
# §5.4 单入口检查
# --------------------------------------------------------------------------

# 最小 x86 序列（4 块）。三个变体只差 `je` 的目标或末块的跳转形态：
#
#   0x00  cmp rax,1 ; je <T>    —— covered 区**之外**的块，两条出边
#   0x06  inc rax   ; jmp 0xb   —— summary 入口块（covered）
#   0x0b  inc rax   ; jmp 0x10  —— covered 区里的**非入口**块
#   0x10  ret                   —— continuation，covered 区之外
#
# `je` 指向 0x0b = 外部边绕过入口直插覆盖区中段；指向 0x06 = 只能从入口进来。
_SINGLE_ENTRY_BYPASS_HEX = "4883f801740548ffc0eb0048ffc0eb00c3"
_SINGLE_ENTRY_CLEAN_HEX = "4883f801740048ffc0eb0048ffc0eb00c3"
# 末块 `ret` 换成 `jmp rax`：静态解析不出目标，build_x86_cfg 记进 unresolved
_SINGLE_ENTRY_INDIRECT_HEX = "4883f801740048ffc0eb0048ffc0eb00ffe0"


def _single_entry_cfg(hex_str):
    blocks = identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    return build_x86_cfg(blocks)


def _synthetic_summary(*, covered=(0x06, 0x0B), continuation=(0x10, 0)):
    """入口 0x06、覆盖 0x06/0x0b 的假 summary（只用来喂单入口检查）。

    payload/clobber 一律留空：这条检查是纯 CFG 结构判定，不碰任何语义。
    """
    return X86Summary(
        kind=COPY_LOOP_SUMMARY_KIND,
        entry_addr=0x06,
        start_block_addr=0x06,
        start_instruction_index=0,
        continuation=SummaryContinuation(*continuation),
        covered_block_addrs=covered,
        clobber_registers=(),
        payload=CopyLoopPayload(template="makedata-byte-copy", binding={}),
    )


class TestSingleEntryCheck:
    """docs/循环处理增强方案.md §5.4「单入口检查(证书折叠的前置条件)」。

    summary 只在命中 `start_key` 时折叠。外部边直插 covered 区中段时，那条路径
    上的块会被原样逐指令执行——**结论仍然健全**，但「折叠一定生效」不成立，
    Tier 1 证书折叠的前置条件随之塌掉。因此必须在**发现期**拒绝，且要显式抛错
    留痕，不能把这条 summary 悄悄删掉（删掉之后「这里没有循环」与「有但被拒」
    在上层无法区分）。
    """

    def test_external_edge_into_a_non_entry_covered_block_is_rejected(self):
        succs, unresolved = _single_entry_cfg(_SINGLE_ENTRY_BYPASS_HEX)
        summary = _synthetic_summary()

        assert find_summary_bypass_edges(summary, succs) == ((0x00, 0x0B),)
        with pytest.raises(SummarySingleEntryError) as raised:
            require_single_entry(summary, succs, unresolved)

        # 原因必须可读到能直接定位：哪条 summary、入口在哪、被哪条边绕过
        message = str(raised.value)
        assert "copy_loop summary at 0x6 is not single entry" in message
        assert "0x0->0xb" in message
        assert raised.value.bypass_edges == ((0x00, 0x0B),)

    def test_entry_only_predecessors_are_accepted(self):
        """正常形态：外部只从入口块进来，检查放行，summary 照常应用。"""
        succs, unresolved = _single_entry_cfg(_SINGLE_ENTRY_CLEAN_HEX)
        summary = _synthetic_summary()

        assert find_summary_bypass_edges(summary, succs) == ()
        require_single_entry(summary, succs, unresolved)

    def test_covered_internal_edges_are_not_bypasses(self):
        """区内边（0x6→0xb）是折叠自身的一部分，不能被算成绕过。

        判据写成「目标在 covered 且不是入口」而漏掉「源不在 covered」的话，
        任何多块 summary 都会被自己的内部边判死——那是把检查写成永假。
        """
        succs, _ = _single_entry_cfg(_SINGLE_ENTRY_CLEAN_HEX)
        summary = _synthetic_summary()

        # 覆盖区内确实存在一条指向非入口覆盖块的边（0x6→0xb），它必须被放行
        assert 0x0B in succs[0x06]
        assert {0x06, 0x0B} <= set(summary.covered_block_addrs)
        assert find_summary_bypass_edges(summary, succs) == ()

    def test_unresolved_indirect_jump_is_fail_closed(self):
        """间接跳转目标未知 ⇒ 拒绝，不能拿「没看见边」冒充「没有边」。"""
        succs, unresolved = _single_entry_cfg(_SINGLE_ENTRY_INDIRECT_HEX)
        summary = _synthetic_summary()

        # 静态边本身是干净的，被拒的唯一理由就是那条解析不出目标的跳转
        assert find_summary_bypass_edges(summary, succs) == ()
        assert unresolved == [0x10]
        with pytest.raises(SummarySingleEntryError, match="no statically"):
            require_single_entry(summary, succs, unresolved)

    def test_same_block_summary_is_exempt(self):
        """covered 区只有入口块时没有可被绕过的块，检查平凡成立。

        豁免必须建立在「不存在非入口覆盖块」上，而不是「这个 kind 看着是同块
        summary」——后者是按名字放行，改个 spec 就漏。
        """
        succs, unresolved = _single_entry_cfg(_SINGLE_ENTRY_INDIRECT_HEX)
        summary = _synthetic_summary(covered=(0x06,), continuation=(0x06, 1))

        require_single_entry(summary, succs, unresolved)

    def test_discovery_rejects_a_bypassed_copy_loop(self, monkeypatch):
        """检查真的挂在发现期链路上，而不是一段没人调用的死代码。

        往 CDC core 的静态 CFG 注入一条 0x23→0x58 的边（0x23 在循环外，0x58 是
        循环体里的非入口块，入口是 0x41）。只 patch copy_loop 模块里的
        `build_x86_cfg` 绑定：`analyze_x86_blocks` 用的是 loop_analysis 自己的
        全局名字，循环识别结果不受影响——于是这条边就是一条纯粹的绕过边。
        """
        blocks = _cdc_blocks()
        ctx = SummaryDiscoveryContext(
            blocks=blocks,
            blocks_by_addr={b.start_addr: b for b in blocks},
            block_index={b.start_addr: i for i, b in enumerate(blocks)},
        )
        real_build_x86_cfg = copy_loop_module.build_x86_cfg

        def _inject_bypass_edge(target_blocks):
            succs, unresolved = real_build_x86_cfg(target_blocks)
            succs[0x23] = list(succs[0x23]) + [0x58]
            return succs, unresolved

        monkeypatch.setattr(
            copy_loop_module, "build_x86_cfg", _inject_bypass_edge
        )

        with pytest.raises(SummarySingleEntryError) as raised:
            list(copy_loop_module.discover_copy_loop_summaries(ctx))

        assert raised.value.bypass_edges == ((0x23, 0x58),)
        assert "0x23->0x58" in str(raised.value)

    def test_discovery_keeps_the_unmodified_copy_loop_and_still_applies_it(self):
        """同一入口不注入边时：照常发现、照常折叠（检查不误伤正常形态）。"""
        blocks = _cdc_blocks()
        succs, _ = build_x86_cfg(blocks)
        runtime = build_x86_summary_runtime(
            blocks,
            summary_config=X86SummaryConfig.enabled(copy_loop="fallback"),
        )
        summaries = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)

        assert len(summaries) == 1
        summary = summaries[0]
        # 非入口覆盖块确实存在，检查不是因为覆盖区退化成单块才通过的
        assert set(summary.covered_block_addrs) - {summary.start_block_addr}
        assert find_summary_bypass_edges(summary, succs) == ()

        binding = summary.payload.binding
        state = SMTState.create_initial_state(num_inputs=0)
        r15 = BitVecVal(0x1000, 64)
        state.x86_registers.set_register(Register.R15, r15)
        state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
        state.x86_registers.set_register(Register(binding["S"]), BitVecVal(2, 64))
        state.x86_registers.set_register(Register(binding["OFF"]), BitVecVal(0, 64))
        state.x86_registers.set_register(Register(binding["LEN"]), BitVecVal(2, 64))
        state.x86_registers.set_register(Register(binding["DST"]), BitVecVal(0, 64))
        state.x86_registers.set_register(
            Register(binding["INP"]), state.callengine_input_pointer
        )
        state.x86_registers.set_pointer_tag(
            Register(binding["INP"]), PointerTag.CALLDATA_PTR
        )
        state.x86_memory.evm_mem = Array(
            "single_entry_ok_mem0", BitVecSort(64), BitVecSort(8)
        )

        out = runtime.apply(summary, state, path_condition=True)

        solver = Solver()
        solver.add(
            Not(
                Select(out.x86_memory.evm_mem, r15 + BitVecVal(0, 64))
                == Select(state.calldata, BitVecVal(0, 64))
            )
        )
        assert solver.check() == unsat
        assert runtime.assumed_premises == []

    @pytest.mark.skipif(not os.path.exists(_CERC20_HEX), reason="CErc20 hex missing")
    def test_cerc20_mcopy_clusters_pass_a_non_vacuous_check(self):
        """真实 fixture 上这条检查不是空转：mcopy cluster 的覆盖区是拼出来的。

        单个 natural loop 的 body 天然前驱闭合（body 是从 latch 起的反向闭包，
        只在 header 停），所以 28+6 条单循环模板必定通过。真正被检查到的是两条
        mcopy cluster——它们把多个循环体 + glue + preamble/align 拼成一个覆盖
        区，内部那几个循环头的外部前驱没有任何结构性保证。这里断言它们确实有
        多个非入口覆盖块、且零绕过边，CErc20 的 36 条因此一条不少。
        """
        runtime = _cerc20_runtime()
        summaries = runtime.summaries_for_kind(COPY_LOOP_SUMMARY_KIND)
        succs, unresolved = build_x86_cfg(runtime.blocks)
        clusters = [
            s for s in summaries if s.payload.template.startswith("mcopy")
        ]

        assert len(summaries) == 36
        assert unresolved == []
        assert len(clusters) == 2
        for cluster in clusters:
            non_entry = set(cluster.covered_block_addrs) - {
                cluster.start_block_addr
            }
            assert len(non_entry) >= 4, cluster.payload.template
            assert find_summary_bypass_edges(cluster, succs) == ()
