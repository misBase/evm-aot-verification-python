"""memoryGasCost summary: matcher, per-shape lemma (fail-closed), exit-guard split, EVM refactor."""

from pathlib import Path

import pytest
from z3 import And, BitVec, BitVecVal, Extract, If, LShR, Not, UDiv, UGT, ZeroExt, is_true, simplify, unsat, Solver

from state.evm_gas_state import memory_expansion_fee, memory_fee_for_size
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig, build_x86_summary_runtime
from x86_64.summaries.base import SummaryPreconditionError
from x86_64.summaries.memgas import MemGasSummaryMatchError, discover_memgas_summaries, exit_guard
from x86_64.summaries.memgas_proof import (
    MemGasProofError,
    clear_proof_cache,
    generic_memgas_state,
    prove_memgas_slice,
    prove_memgas_slice_cached,
)

DATA = Path(__file__).resolve().parents[1] / "data"

# The Go template with S=rdi, T=r8, T2=r9 (every real codegen site uses
# rbx/rcx/rsi), assembled by clang: `mov r10, rdi` prefix, the template, and
# END: `mov [r13+0x108], r10; ret`.
RENAMED_HEX = (
    "4989fa4885ff0f849400000049b8e0ffffff1f0000004939f8727449c7c0ffffffff49c1e0054939f8720a4883c71f"
    "48c1ef05eb0a48bf00000000000000084989f848c1e7054d8b4d184939f973514c89c048f7e04889c749c7c1030000"
    "004c89c049f7e14989c04889f848c7c70002000048c7c20000000048f7f74901c04c89c04d8b4d204d29c849894520"
    "eb1841c685e00000000c49c7452802000000c349c7c0000000004d899508010000c3"
)


@pytest.fixture(autouse=True)
def _isolated_proof_cache():
    clear_proof_cache()
    yield
    clear_proof_cache()


def _blocks(hex_code):
    return identify_basic_blocks(disassemble_hex(hex_code, 0))


def _fixture(name):
    return (DATA / f"{name}.hex").read_text().strip()


@pytest.mark.parametrize("name", ["gas_mload", "gas_log1", "gas_sha3", "gas_create"])
def test_matcher_on_real_slices_of_different_opcodes(name):
    [summary] = discover_memgas_summaries(_blocks(_fixture(name)), strict=True)
    p = summary.payload
    assert (p.size_reg, p.fee_reg, p.tmp_reg) == (Register.RBX, Register.RCX, Register.RSI)
    assert p.entry_addr < p.oog_addr < p.zero_addr < p.continuation_addr
    assert summary.is_cross_block and summary.continuation.block_addr == p.continuation_addr
    assert set(summary.clobber_registers) == {Register.RBX, Register.RCX, Register.RSI, Register.RAX, Register.RDX}


def test_matcher_is_register_parametric():
    [summary] = discover_memgas_summaries(_blocks(RENAMED_HEX), strict=True)
    p = summary.payload
    assert (p.size_reg, p.fee_reg, p.tmp_reg) == (Register.RDI, Register.R8, Register.R9)
    assert (summary.start_block_addr, summary.start_instruction_index, p.entry_addr) == (0, 1, 3)
    assert (p.oog_addr, p.zero_addr, p.continuation_addr, p.oog_stack_pointer) == (0x8F, 0xA0, 0xA7, 2)


def test_lemma_proves_all_paths_and_is_cached_by_shape():
    blocks = _blocks(_fixture("gas_mload"))
    [summary] = discover_memgas_summaries(blocks, strict=True)
    lemma, status = prove_memgas_slice_cached(summary, blocks)
    assert status == "proven" and lemma.complete and lemma.path_count == 3
    # Another opcode, same template shape (only the OOG stack pointer may differ).
    other = _blocks(_fixture("gas_sha3"))
    [again] = discover_memgas_summaries(other, strict=True)
    assert prove_memgas_slice_cached(again, other)[1] == "cache_hits"
    lemma, status = prove_memgas_slice_cached(*discover_memgas_summaries(_blocks(RENAMED_HEX)), _blocks(RENAMED_HEX))
    assert status == "proven" and lemma.complete


def _mutate(hex_code, entry, mnemonic, op_str, new_bytes):
    insns = disassemble_hex(hex_code, 0)
    target = next(i for i in insns if i.addr > entry and i.mnemonic == mnemonic and i.op_str == op_str)
    raw = bytearray.fromhex(hex_code)
    raw[target.addr:target.addr + target.size] = bytes.fromhex(new_bytes)
    return raw.hex()


@pytest.mark.parametrize("mnemonic,op_str,new_bytes", [
    ("shr", "rbx, 5", "48c1eb04"),                        # SHRQ 5 -> 4
    ("movabs", "rcx, 0x1fffffffe0", "48b9e0ffffff0f000000"),  # cap with one bit flipped
    ("sub", "rcx, rsi", "4801f1"),                        # fee = total + last
])
def test_corrupted_template_is_rejected_by_matcher_and_lemma(mnemonic, op_str, new_bytes):
    good = _fixture("gas_mload")
    blocks = _blocks(good)
    [summary] = discover_memgas_summaries(blocks, strict=True)
    bad = _mutate(good, summary.entry_addr, mnemonic, op_str, new_bytes)
    assert discover_memgas_summaries(_blocks(bad)) == []
    if mnemonic != "movabs":  # the cap-flipped slice is no longer even a candidate
        with pytest.raises(MemGasSummaryMatchError):
            discover_memgas_summaries(_blocks(bad), strict=True)
    # The lemma does not trust the matcher: the good summary against the bad code fails.
    with pytest.raises(MemGasProofError, match="effect_|raw"):
        prove_memgas_slice_cached(summary, _blocks(bad))


def _guard_holds(condition, guard):
    solver = Solver()
    solver.add(condition, Not(guard))
    return solver.check() == unsat


def test_exit_guard_split_runs_raw_oog_under_g_and_summary_otherwise():
    from verification.loop_induction import run_x86_segment

    blocks = _blocks(RENAMED_HEX)
    runtime = build_x86_summary_runtime(blocks, summary_config=X86SummaryConfig.enabled(memgas="strict"))
    [summary] = runtime.summaries
    state = generic_memgas_state()
    s0 = state.x86_registers.get_register(Register.RDI)
    guard = exit_guard(summary.payload, state)
    paths, defects, _ = run_x86_segment(blocks, state, 0, {0xA7}, max_depth=50,
                                        use_reachability_check=True, summary_runtime=runtime)
    assert not defects and runtime.hit_count("memgas") == 1
    [oog] = [p for p in paths if p.kind == "terminal"]
    [fast] = [p for p in paths if p.kind != "terminal"]
    # G fork: the raw slice ran (prefix included) and left through the OOG exit.
    assert _guard_holds(oog.condition, guard)
    assert simplify(oog.state.callengine_status_code).eq(BitVecVal(12, 8))
    assert simplify(oog.state.x86_registers.get_register(Register.R10) == s0).eq(simplify(s0 == s0))
    # not G fork: summary applied, fee in T, clobbers fresh.
    assert _guard_holds(fast.condition, Not(guard)) and fast.location == 0xA7
    fee = memory_fee_for_size(state.callengine_memory_size_bytes, state.callengine_memory_gas_used, s0)[0]
    assert fast.state.x86_registers.get_register(Register.R8).eq(fee)
    assert "memgas_summary" in str(fast.state.x86_registers.get_register(Register.RDI))


def test_block_runtime_instantiates_the_lemma_under_the_excluded_guard():
    from verification.block_summaries import VerifiedSummaryRuntime

    blocks = _blocks(RENAMED_HEX)
    runtime = VerifiedSummaryRuntime(blocks, X86SummaryConfig.enabled(memgas="strict"), timeout_ms=30000)
    [summary] = runtime.summaries
    state = generic_memgas_state()
    guard = exit_guard(summary.payload, state)
    runtime.apply(summary, state, path_condition=Not(guard))
    [certificate] = runtime.certificates
    names = {o.name for o in certificate.obligations}
    assert certificate.complete and certificate.raw_path_count == 3
    assert {"entry", "memgas_exit_guard_excluded", "coverage", "effect_2"} <= names
    with pytest.raises(SummaryPreconditionError, match="memgas_exit_guard_excluded"):
        runtime.apply(summary, state)
    assert len(runtime.certificates) == 1


def _old_memory_expansion_fee(mem_size_bytes, last_gas_cost, requested_size_64):
    """memory_expansion_fee verbatim before the split into memory_fee_for_size."""
    thirty_one = BitVecVal(31, 64)
    memory_size = LShR(requested_size_64 + thirty_one, BitVecVal(5, 64)) << BitVecVal(5, 64)
    mem_words = LShR(memory_size + thirty_one, BitVecVal(5, 64))
    rounded = mem_words << BitVecVal(5, 64)
    square_128 = ZeroExt(64, mem_words * mem_words)
    quad_64 = Extract(63, 0, UDiv(square_128, BitVecVal(512, 128)))
    new_total = mem_words * BitVecVal(3, 64) + quad_64
    expands = UGT(rounded, mem_size_bytes)
    return (If(expands, new_total - last_gas_cost, BitVecVal(0, 64)),
            If(expands, rounded, mem_size_bytes), If(expands, new_total, last_gas_cost))


def test_memory_expansion_fee_refactor_is_ast_identical():
    args = (BitVec("msize", 64), BitVec("last", 64), BitVec("requested", 64))
    for new, old in zip(memory_expansion_fee(*args), _old_memory_expansion_fee(*args)):
        assert new.eq(old)
