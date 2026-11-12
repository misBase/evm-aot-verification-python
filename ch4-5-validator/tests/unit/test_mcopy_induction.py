"""MCOPY per-hit induction: the real CErc20 codegen proves; tampered bytes cannot."""
from dataclasses import replace

import pytest
from z3 import Array, BitVec, BitVecSort, And

from state.smt_state import SMTState, PointerTag
from verification.block_summaries import VerifiedSummaryRuntime
from verification.mcopy_induction import mcopy_domain
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig, build_x86_summary_runtime
from x86_64.summaries.base import SummaryPreconditionError

# compileEVMMCOPY dispatch + FromHigh + FromLow bytes of CErc20
# (calldataload_fixed) at 0xae232..0xae2e5, then a `ret` as the continuation.
BASE = 0xAE232
CLUSTER = (
    "4839c87e754883fa087e6f"
    "0f1f004883fa087c314801d04801d14883e9084883e8084883fa007450488b194889184883ea08"
    "4883e9084883fa087c064883e808ebe04829d0488b1948c7c1080000004829d14883f900740a48"
    "c1eb084883e901ebf04883fa007410881848c1eb084883ea014883c001ebeaeb394883fa007433"
    "4883fa087c14488b194889184883c1084883c0084883ea08ebe0488b194883fa007410881848c1"
    "eb084883ea014883c001ebea" "c3")


def _blocks(hex_str):
    return identify_basic_blocks(disassemble_hex(hex_str, base_addr=BASE))


def _patch(addr, old, new):
    i = (addr - BASE) * 2
    assert CLUSTER[i:i + len(old)] == old
    return CLUSTER[:i] + new + CLUSTER[i + len(old):]


def case(template, hex_str=CLUSTER):
    # Templates are discovered on the genuine bytes; replay uses `hex_str`.
    genuine = build_x86_summary_runtime(_blocks(CLUSTER),
        summary_config=X86SummaryConfig.enabled(copy_loop="strict"))
    runtime = VerifiedSummaryRuntime(_blocks(hex_str), None, timeout_ms=20000, runtime=genuine)
    summary, = [s for s in genuine.summaries if s.payload.template == template]
    b = summary.payload.binding
    state = SMTState.create_initial_state(num_inputs=0)
    r15 = BitVec("mcopy_mem_base", 64)
    d0, s0, size = (BitVec("mcopy_" + n, 64) for n in ("d0", "s0", "size"))
    state.x86_registers.set_register(Register.R15, r15)
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    for role, value in (("DST", r15 + d0), ("SRC", r15 + s0)):
        state.x86_registers.set_register(Register(b[role]), value)
        state.x86_registers.set_pointer_tag(Register(b[role]), PointerTag.EVM_PTR)
    state.x86_registers.set_register(Register(b["S"]), size)
    state.x86_memory.evm_mem = Array("mcopy_old_memory", BitVecSort(64), BitVecSort(8))
    return runtime, summary, state, mcopy_domain(template, r15 + d0, r15 + s0, size, r15)


@pytest.mark.parametrize("template", ["mcopy-low-word", "mcopy-high-word"])
def test_symbolic_length_mcopy_has_complete_certificate(template):
    runtime, summary, state, domain = case(template)
    runtime.apply(summary, state, domain)
    certificate, = runtime.certificates
    assert certificate.complete
    names = {o.name for o in certificate.obligations}
    assert any(n.startswith("progress_") for n in names) and any(n.startswith("exit_") for n in names)
    # Dropping any obligation breaks the manifest.
    assert not replace(certificate, obligations=certificate.obligations[:-1]).complete
    assert not replace(certificate, raw_path_count=certificate.raw_path_count + 1).complete


TAMPERS = {
    # word loop `cmp rdx, 8` -> 7: a qword store with 7 bytes left (off-by-one bound)
    "low-bound": ("mcopy-low-word", 0xAE2B2, "4883fa08", "4883fa07"),
    # byte tail `add rax, 1` -> 2: skips every other destination byte
    "low-skip": ("mcopy-low-word", 0xAE2DF, "4883c001", "4883c002"),
    # high word loop `sub rcx, 8` -> `add rcx, 8`: source walks the wrong way
    "high-direction": ("mcopy-high-word", 0xAE264, "4883e908", "4883c108"),
    # high glue `sub rax, rdx` dropped (nop): head bytes land at the wrong place
    "high-glue": ("mcopy-high-word", 0xAE274, "4829d0", "0f1f00"),
}


@pytest.mark.parametrize("name", sorted(TAMPERS))
def test_tampered_loop_cannot_mint_a_certificate(name):
    template, addr, old, new = TAMPERS[name]
    runtime, summary, state, domain = case(template, _patch(addr, old, new))
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, domain)
    assert not runtime.certificates


def test_forward_copy_is_refused_for_reverse_overlap():
    # Correct bytes, but the premise does not exclude a large reverse overlap:
    # the FromLow loop is only memmove for dst <= src or size <= 8.
    runtime, summary, state, domain = case("mcopy-low-word")
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, And(*domain.children()[1:]))
    assert not runtime.certificates


def test_induction_itself_rejects_forward_copy_under_reverse_overlap(monkeypatch):
    # Disable BOTH gates in front of the induction (summary precondition and
    # mcopy_domain shape). The memmove invariant alone must then refuse.
    import verification.mcopy_induction as module
    import x86_64.summaries.copy_loop as copy_loop
    monkeypatch.setattr(copy_loop, "_require_all_implied", lambda **kwargs: None)
    shapeless = module.mcopy_domain
    monkeypatch.setattr(module, "mcopy_domain",
                        lambda *args: And(*shapeless(*args).children()[1:]))
    runtime, summary, state, domain = case("mcopy-low-word")
    with pytest.raises(SummaryPreconditionError, match=r"(step|exit)_\d+_\w+: sat"):
        runtime.apply(summary, state, And(*domain.children()[1:]))
    assert not runtime.certificates


def test_hit_on_infeasible_path_is_vacuous_not_replayed():
    from verification.mcopy_induction import DeadHitCertificate
    runtime, summary, state, domain = case("mcopy-high-word")
    size = state.x86_registers.get_register(Register(summary.payload.binding["S"]))
    assert runtime.apply(summary, state, And(domain, size == 0)) is not None
    certificate, = runtime.certificates
    assert isinstance(certificate, DeadHitCertificate) and certificate.complete


def test_second_hit_reuses_the_lemma_but_proves_its_own_instance():
    import time
    runtime, summary, state, domain = case("mcopy-low-word")
    runtime.apply(summary, state, domain)
    other = state.copy()
    other.x86_memory.evm_mem = Array("mcopy_other_memory", BitVecSort(64), BitVecSort(8))
    started = time.monotonic()
    runtime.apply(summary, other, domain)
    assert time.monotonic() - started < 20
    first, second = runtime.certificates
    assert first.complete and second.complete and first.identity != second.identity
    assert first.required == second.required


def test_lemma_is_shared_across_residual_values_and_nodes(monkeypatch):
    # Different paths leave different copy-irrelevant values (numerals, other
    # symbolic terms, DST/SRC expressions) behind; a later node has its own
    # runtime. One lemma serves all; each hit still proves its instance.
    import verification.mcopy_induction as module
    from z3 import BitVecVal
    proofs = []
    original = module._prove_lemma
    monkeypatch.setattr(module, "_prove_lemma", lambda *a, **k: proofs.append(1) or original(*a, **k))
    runtime, summary, state, domain = case("mcopy-low-word")
    state.x86_registers.set_register(Register.R8, BitVecVal(5, 64))
    runtime.apply(summary, state, domain)
    node = VerifiedSummaryRuntime(runtime.blocks, None, timeout_ms=20000, runtime=runtime.runtime)
    other = state.copy()
    other.x86_registers.set_register(Register.R8, BitVecVal(7, 64))
    other.x86_registers.set_register(Register.R9, BitVec("residue", 64) + 3)
    other.x86_registers.set_flag("CF", BitVecVal(1, 1))
    node.apply(summary, other, domain)
    assert len(proofs) == 1
    first, = runtime.certificates
    second, = node.certificates
    assert first.complete and second.complete and "mcopy_param_entry" in second.required
