from dataclasses import replace

import pytest
from z3 import Array, BitVec, BitVecSort, BitVecVal, BoolVal, ULE

from state.smt_state import SMTState, PointerTag, MemoryDomain
from verification.block_summaries import VerifiedSummaryRuntime
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig, SummaryPreconditionError
from tests.unit.test_copy_loop_summary import _cdc_blocks


def copy_case(size):
    runtime = VerifiedSummaryRuntime(_cdc_blocks(), X86SummaryConfig.enabled(copy_loop="strict"), timeout_ms=2000)
    summary = runtime.summaries[0]
    binding = summary.payload.binding
    state = SMTState.create_initial_state(num_inputs=0)
    state.assume_calldata_offset_no_overflow = False
    state.x86_registers.set_register(Register.R15, BitVecVal(0x1000, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    for name, value in (("S", size), ("OFF", 0), ("LEN", 5), ("DST", 0)):
        state.x86_registers.set_register(Register(binding[name]), BitVecVal(value, 64))
    state.x86_registers.set_register(Register(binding["INP"]), state.callengine_input_pointer)
    state.x86_registers.set_pointer_tag(Register(binding["INP"]), PointerTag.CALLDATA_PTR)
    state.x86_memory.evm_mem = Array("summary_frame_memory", BitVecSort(64), BitVecSort(8))
    return runtime, summary, state


@pytest.mark.parametrize("size", [0, 7, 8, 9])
def test_copy_per_hit_proves_zero_padding_frame_and_finite_execution(size):
    runtime, summary, state = copy_case(size)
    runtime.apply(summary, state)
    assert len(runtime.certificates) == 1 and runtime.certificates[0].complete
    assert not replace(runtime.certificates[0], finite=False).complete


def test_summary_wrong_memory_effect_rejected(monkeypatch):
    runtime, summary, state = copy_case(7)
    original = runtime.runtime.manager.apply
    def wrong(*args, **kw):
        result = original(*args, **kw)
        result.x86_memory = result.x86_memory.store_byte(BitVecVal(0x1000, 64), BitVecVal(255, 8), domain=MemoryDomain.EVM)
        return result
    monkeypatch.setattr(runtime.runtime.manager, "apply", wrong)
    with pytest.raises(SummaryPreconditionError): runtime.apply(summary, state)
    assert not runtime.certificates


def test_summary_missing_progress_is_rejected():
    runtime, summary, state = copy_case(9)
    runtime.max_depth = 1
    with pytest.raises(SummaryPreconditionError, match="incomplete"):
        runtime.apply(summary, state)


def test_summary_cannot_cross_a_block_cutpoint():
    runtime, summary, state = copy_case(7)
    runtime.cutpoints.add(summary.entry_addr)
    with pytest.raises(SummaryPreconditionError, match="ownership"):
        runtime.apply(summary, state)


def calldata_case(offset, size=32):
    from pathlib import Path
    from x86_64.program import X86Program
    from x86_64.cfg import identify_basic_blocks
    from x86_64.summaries.calldataload import ConstLimbLocation, RegisterLimbLocation, StackLimbLocation
    x86 = X86Program.from_hex(Path("tests/data/muti_block_08.hex").read_text(), base_addr=0)
    runtime = VerifiedSummaryRuntime(identify_basic_blocks(x86.instructions),
        X86SummaryConfig.enabled(calldataload="fallback"), timeout_ms=2000, max_depth=300)
    summary = next(s for s in runtime.summaries if s.payload.require_concrete_offset)
    state = SMTState.create_initial_state(num_inputs=0)
    state.assume_calldata_offset_no_overflow = False
    state.callengine_input_size_bytes = BitVecVal(size, 64)
    state.calldatasize = BitVecVal(size, 64)
    base = BitVecVal(0x8000, 64)
    state.x86_registers.set_register(Register.R14, base)
    for index, loc in enumerate(summary.payload.offset_limb_locs):
        value = offset if index == 0 else BitVecVal(0, 64)
        if isinstance(loc, RegisterLimbLocation):
            state.x86_registers.set_register(loc.reg, value)
        elif isinstance(loc, StackLimbLocation):
            state.x86_memory = state.x86_memory.store_limb(base + loc.offset, value, domain=MemoryDomain.STACK)
        else:
            assert isinstance(loc, ConstLimbLocation) and loc.value == 0 and index != 0
    return runtime, summary, state


@pytest.mark.parametrize("size", [0, 7, 8, 9, 31, 32])
def test_calldata_actual_slice_zero_padding(size):
    runtime, summary, state = calldata_case(BitVecVal(0, 64), size)
    runtime.apply(summary, state)
    assert runtime.certificates[-1].complete


def test_symbolic_calldata_offset_is_proved_under_current_guard():
    offset = BitVec("summary_symbolic_offset", 64)
    runtime, summary, state = calldata_case(offset)
    runtime.apply(summary, state, path_condition=ULE(offset, BitVecVal(32, 64)))
    assert runtime.certificates[-1].complete


def test_calldata_wrap_boundary_never_gets_an_assumed_no_overflow():
    runtime, summary, state = calldata_case(BitVecVal((1 << 64) - 1, 64))
    runtime.apply(summary, state)
    assert runtime.certificates[-1].complete
    assert not state.assumptions


@pytest.mark.parametrize("template,dst,src", [
    ("mcopy-low-word", 0x1000, 0x1002), ("mcopy-high-word", 0x1002, 0x1000)])
def test_actual_mcopy_overlap_and_direction(template, dst, src):
    from tests.unit.test_copy_loop_summary import _cerc20_runtime, _seed_mcopy_high_state
    blocks = _cerc20_runtime().blocks
    runtime = VerifiedSummaryRuntime(blocks, X86SummaryConfig.enabled(copy_loop="fallback"),
                                     timeout_ms=3000, max_depth=100)
    summary = next(s for s in runtime.summaries if s.payload.template == template)
    state, _ = _seed_mcopy_high_state(summary.payload.binding, dst=BitVecVal(dst, 64),
                                    src=BitVecVal(src, 64), size=BitVecVal(9, 64))
    state.assume_calldata_offset_no_overflow = False
    state.x86_memory.evm_mem = Array("overlap_symbolic_memory", BitVecSort(64), BitVecSort(8))
    runtime.apply(summary, state)
    assert runtime.certificates[-1].complete


def test_summary_deadline_expiry_is_not_converted_to_raw_fallback():
    from time import monotonic
    from verification.block_equivalence import ProofBudgetExceeded
    runtime, summary, state = calldata_case(BitVecVal(0, 64))
    runtime.deadline = monotonic() - 1
    with pytest.raises(ProofBudgetExceeded, match="deadline exhausted"):
        runtime.apply(summary, state)
    assert not runtime.certificates and runtime.proof_queries == 0


def test_raw_replay_timeout_is_not_converted_to_fallback(monkeypatch):
    runtime, summary, state = copy_case(7)
    def timed_out(*args, **kwargs):
        raise TimeoutError("raw replay deadline")
    monkeypatch.setattr("verification.block_summaries.run_x86_segment", timed_out)
    with pytest.raises(TimeoutError, match="raw replay deadline"):
        runtime.apply(summary, state)
    assert not runtime.certificates


def test_calldata_uint64_wrap_counterexample_cannot_be_summarized_away(monkeypatch):
    # Actual codegen computes offset+32 in uint64. With this model input it
    # wraps to zero and takes a full-word read, while EVM zero-pads two bytes.
    runtime, summary, state = calldata_case(BitVecVal((1 << 64) - 32, 64), (1 << 64) - 2)
    monkeypatch.setattr("verification.block_summaries.run_x86_segment",
                        lambda *a, **kw: pytest.fail("inapplicable summary must skip raw replay"))
    with pytest.raises(SummaryPreconditionError, match="calldata_no_wrap: sat"):
        runtime.apply(summary, state)
    assert not runtime.certificates
    assert not state.assumptions


def test_summary_hit_certificate_requires_manifest_match():
    from verification.block_equivalence import Obligation
    from verification.block_summaries import SummaryHitCertificate
    proved = lambda n: Obligation(n, "true", "unsat")
    ok = (proved("entry"), proved("coverage"), proved("effect_0"))
    names = tuple(o.name for o in ok)
    assert SummaryHitCertificate("id", ok, 1, True, names).complete
    # An issued assumption obligation that went missing from the records.
    assert not SummaryHitCertificate("id", ok, 1, True, names[:2] + ("assumption_0_2",) + names[2:]).complete
    assert not SummaryHitCertificate("id", ok, 1, True).complete
