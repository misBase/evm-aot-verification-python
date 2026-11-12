"""Raw-cycle induction must reject missing paths, frames and new assumptions."""
from dataclasses import replace

import pytest
from z3 import Array, BitVec, BitVecSort, BoolVal, And, ULE, ULT

from state.smt_state import SMTState, PointerTag
from verification.block_summaries import VerifiedSummaryRuntime
from x86_64.models import Register
from x86_64.summaries import X86SummaryConfig
from x86_64.summaries.base import SummaryPreconditionError
from tests.unit.test_copy_loop_summary import _cdc_blocks


def symbolic_case(hex_str=None, templates=None):
    # Templates are discovered on the genuine bytes; replay uses `hex_str`.
    from x86_64.cfg import identify_basic_blocks
    from x86_64.disassembler import disassemble_hex
    from x86_64.summaries import build_x86_summary_runtime
    if templates is None:
        templates = build_x86_summary_runtime(_cdc_blocks(),
            summary_config=X86SummaryConfig.enabled(copy_loop="strict"))
    blocks = _cdc_blocks() if hex_str is None else identify_basic_blocks(disassemble_hex(hex_str, base_addr=0))
    runtime = VerifiedSummaryRuntime(blocks, None, timeout_ms=5000, runtime=templates)
    summary = runtime.summaries[0]
    state = SMTState.create_initial_state(num_inputs=0)
    state.assume_calldata_offset_no_overflow = False
    state.x86_registers.set_register(Register.R15, BitVec("copy_mem_base", 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    values = {name: BitVec("copy_" + name, 64) for name in ("S", "OFF", "LEN", "DST")}
    for name, value in values.items():
        state.x86_registers.set_register(Register(summary.payload.binding[name]), value)
    source = Register(summary.payload.binding["INP"])
    state.x86_registers.set_register(source, state.callengine_input_pointer)
    state.x86_registers.set_pointer_tag(source, PointerTag.CALLDATA_PTR)
    state.x86_memory.evm_mem = Array("copy_old_memory", BitVecSort(64), BitVecSort(8))
    size, off, dst = (values[n] for n in ("S", "OFF", "DST"))
    domain = And(ULT(size, 1 << 63), ULE(dst, dst + size), ULE(off, off + size))
    return runtime, summary, state, domain


def test_symbolic_copy_has_complete_induction_certificate():
    runtime, summary, state, domain = symbolic_case()
    runtime.apply(summary, state, domain)
    certificate, = runtime.certificates
    assert certificate.complete and certificate.raw_path_count == 3
    assert not replace(certificate, obligations=certificate.obligations[:-1]).complete


@pytest.mark.parametrize("mutation", ["path", "frame", "memory", "progress", "assumption"])
def test_raw_cycle_mutations_cannot_mint_a_certificate(monkeypatch, mutation):
    import verification.block_summaries as module
    raw = module.run_x86_segment
    runtime, summary, state, domain = symbolic_case()

    def corrupt(blocks, head, entry, stops, **kwargs):
        paths, defects, count = raw(blocks, head, entry, stops, **kwargs)
        if mutation == "path":
            paths = paths[:-1]
        elif mutation == "assumption":
            # Coverage still holds; the added assumption appears in its own guard.
            paths[0].state.add_assumption(BoolVal(False))
            paths[0] = replace(paths[0], condition=And(paths[0].condition, BoolVal(False)))
            paths.append(replace(paths[1], condition=BoolVal(True)))
        elif mutation == "memory":
            from z3 import Store, BitVecVal
            paths[0].state.x86_memory.evm_mem = Store(paths[0].state.x86_memory.evm_mem,
                BitVecVal(0, 64), BitVecVal(255, 8))
        elif mutation == "progress":
            reg = Register(summary.payload.binding["S"])
            paths[0].state.x86_registers.set_register(reg, head.x86_registers.get_register(reg))
        else:
            paths[0].state.callengine_gas += 1
        return paths, defects, count

    monkeypatch.setattr(module, "run_x86_segment", corrupt)
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, domain)
    assert not runtime.certificates
    if mutation == "assumption":
        assert any(o.name.startswith("copy_assumption_") and o.answer == "sat"
                   for o in runtime.last_records)


def test_parameterized_result_must_instantiate_the_actual_candidate(monkeypatch):
    from z3 import Store, BitVecVal
    runtime, summary, state, domain = symbolic_case()
    apply = runtime.runtime.manager.apply
    calls = 0

    def corrupt_actual(*args, **kwargs):
        nonlocal calls
        result = apply(*args, **kwargs)
        calls += 1
        if calls == 1:
            # The universal candidate stays correct; only this hit is corrupted.
            result.x86_memory.evm_mem = Store(result.x86_memory.evm_mem,
                BitVecVal(0, 64), BitVecVal(255, 8))
        return result

    monkeypatch.setattr(runtime.runtime.manager, "apply", corrupt_actual)
    with pytest.raises(SummaryPreconditionError, match="copy_param_result"):
        runtime.apply(summary, state, domain)
    assert not runtime.certificates


# --- the induction is a lemma shared by every hit of the program ------------

def _count_lemma_proofs(monkeypatch):
    import verification.copy_induction as module
    proofs = []
    original = module._prove_lemma
    monkeypatch.setattr(module, "_prove_lemma", lambda *a, **k: proofs.append(1) or original(*a, **k))
    return proofs


def test_lemma_is_proved_once_and_shared_across_paths_and_nodes(monkeypatch):
    from z3 import BitVecVal
    proofs = _count_lemma_proofs(monkeypatch)
    runtime, summary, state, domain = symbolic_case()
    state.x86_registers.set_register(Register.R9, BitVecVal(5, 64))
    runtime.apply(summary, state, domain)
    # Another path of the same node: copy-irrelevant residue differs.
    other = state.copy()
    other.x86_memory.evm_mem = Array("copy_other_memory", BitVecSort(64), BitVecSort(8))
    other.x86_registers.set_register(Register.R9, BitVecVal(7, 64))
    other.x86_registers.set_register(Register.R10, BitVec("residue", 64) + 3)
    other.x86_registers.set_flag("CF", BitVecVal(1, 1))
    runtime.apply(summary, other, domain)
    # A later node has its own runtime but the same template runtime.
    node = VerifiedSummaryRuntime(runtime.blocks, None, timeout_ms=5000, runtime=runtime.runtime)
    third = other.copy()
    third.x86_registers.set_register(Register.R9, BitVecVal(9, 64))
    node.apply(summary, third, domain)
    assert len(proofs) == 1
    certificates = runtime.certificates + node.certificates
    assert len(certificates) == 3 and all(c.complete for c in certificates)
    assert len({c.identity for c in certificates}) == 3
    # Every hit carries its own instance obligations plus the lemma's records.
    for c in certificates:
        names = [o.name for o in c.obligations]
        assert names[:3] == ["entry", "copy_domain", "copy_param_entry"]
        assert names[-1] == "copy_param_result" and "copy_base" in names and "coverage" in names


TAMPERS = {
    # `sub rax, 1` -> `add rax, 1`: the counter walks the wrong way
    "direction": (0x49, "4883e801", "4883c001"),
    # `sub rax, 1` -> `sub rax, 2`: skips every other byte
    "step": (0x49, "4883e801", "4883e802"),
    # `cmp rax, 1` -> `cmp rax, 0`: one iteration past the end (counter wraps)
    "bound": (0x43, "4883f801", "4883f800"),
    # `add rdx, r8` -> `sub rdx, r8`: wrong destination
    "store": (0x68, "4c01c2", "4c29c2"),
}


@pytest.mark.parametrize("name", sorted(TAMPERS))
def test_tampered_loop_gets_no_lemma_even_after_the_genuine_one_is_cached(monkeypatch, name):
    from tests.unit.test_tier2_templates import _CDC_HEX
    addr, old, new = TAMPERS[name]
    assert _CDC_HEX[addr * 2:addr * 2 + len(old)] == old
    tampered = _CDC_HEX[:addr * 2] + new + _CDC_HEX[addr * 2 + len(old):]
    genuine, summary, state, domain = symbolic_case()
    genuine.apply(summary, state, domain)
    proofs = _count_lemma_proofs(monkeypatch)
    runtime, summary, state, domain = symbolic_case(tampered, templates=genuine.runtime)
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, domain)
    assert proofs and not runtime.certificates  # re-proved on the tampered bytes, refused


@pytest.mark.parametrize("drop", ["copy_domain", "copy_param_entry", "copy_param_result", "copy_base",
                                  "coverage", "copy_progress_", "copy_exit_", "effect_0", "effect_1_other"])
def test_certificate_missing_any_obligation_is_not_proved(drop):
    runtime, summary, state, domain = symbolic_case()
    runtime.apply(summary, state, domain)
    certificate, = runtime.certificates
    assert certificate.complete
    kept = tuple(o for o in certificate.obligations
                 if not (o.name == drop or (drop.endswith("_") and o.name.startswith(drop))))
    assert len(kept) < len(certificate.obligations)
    # Even a self-consistent manifest (required == what was proved) is refused.
    assert not replace(certificate, obligations=kept, required=tuple(o.name for o in kept)).complete


def test_certificate_with_an_unproved_obligation_is_not_proved():
    runtime, summary, state, domain = symbolic_case()
    runtime.apply(summary, state, domain)
    certificate, = runtime.certificates
    for i in range(len(certificate.obligations)):
        for answer in {"sat", "unknown", "unsat"} - {certificate.obligations[i].expected}:
            obligations = list(certificate.obligations)
            obligations[i] = replace(obligations[i], answer=answer)
            assert not replace(certificate, obligations=tuple(obligations)).complete


def test_source_register_must_equal_its_pointer_field_per_hit(monkeypatch):
    # The key does not contain INP (tied to the pointer field in the lemma).
    # With the summary's own pointer gate disabled, copy_param_entry refuses.
    import x86_64.summaries.copy_loop as copy_loop
    runtime, summary, state, domain = symbolic_case()
    runtime.apply(summary, state, domain)
    monkeypatch.setattr(copy_loop, "_require_implied_pointer_value", lambda **kwargs: None)
    source = Register(summary.payload.binding["INP"])
    state.x86_registers.set_register(source, state.callengine_input_pointer + 1)
    state.x86_registers.set_pointer_tag(source, PointerTag.CALLDATA_PTR)
    with pytest.raises(SummaryPreconditionError, match="copy_param_entry"):
        runtime.apply(summary, state, domain)
    assert len(runtime.certificates) == 1


@pytest.mark.parametrize("change", ["residue_tag", "source_provenance"])
def test_too_coarse_key_fails_closed(change):
    runtime, summary, state, domain = symbolic_case()
    runtime.apply(summary, state, domain)
    lemma, = [v for v in runtime.runtime._copy_lemmas.values() if v is not None]

    class Coarse(dict):  # every key hits the calldata lemma
        def __contains__(self, key):
            return True

        def __getitem__(self, key):
            return lemma

    runtime.runtime.__dict__["_copy_lemmas"] = Coarse()
    if change == "residue_tag":
        state.x86_registers.set_pointer_tag(Register.R9, PointerTag.EVM_PTR)
    else:
        source = Register(summary.payload.binding["INP"])
        state.x86_registers.set_register(source, state.callengine_code_pointer)
        state.x86_registers.set_pointer_tag(source, PointerTag.CODE_PTR)
    with pytest.raises(SummaryPreconditionError):
        runtime.apply(summary, state, domain)
    assert len(runtime.certificates) == 1


def test_nontrivial_scratch_provenance_is_refused():
    runtime, summary, state, domain = symbolic_case()
    state.x86_registers.set_pointer_tag(Register(summary.payload.binding["T"]), PointerTag.EVM_PTR)
    with pytest.raises(SummaryPreconditionError, match="scratch"):
        runtime.apply(summary, state, domain)
    assert not runtime.certificates
