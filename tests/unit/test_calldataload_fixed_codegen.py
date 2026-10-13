"""CALLDATALOAD summary on the fixed (``sub size, offset; cmp size, 32``) codegen."""
from functools import lru_cache
from pathlib import Path

import pytest
from z3 import ULE, BitVec, BitVecVal

from state.smt_state import SMTState
from verification.block_summaries import VerifiedSummaryRuntime
from x86_64.cfg import identify_basic_blocks
from x86_64.models import Register
from x86_64.program import X86Program
from x86_64.summaries import SummaryPreconditionError, X86SummaryConfig
from x86_64.disassembler import disassemble_hex
from x86_64.summaries.calldataload import (RegisterLimbLocation, discover_calldataload_summaries,
                                          pointer_tag_dead_at)

from verification.block_summaries import movable_slice as _MOVABLE_SLICE  # before monkeypatching
from verification.block_summaries import shifted_slice as _SHIFTED_SLICE

HEX = Path("tests/data/ext_contracts/calldataload_fixed/CErc20.hex")
SYMBOLIC_ENTRY = 0xAE1B5      # offset limbs in rax/rcx/rdx/rbx
CONST_ENTRY = 0x6C4           # offset = 0
PARTIAL_CMP2 = 0x760          # "cmp rax, 2" guarding byte 1 of CONST_ENTRY's partial path


@lru_cache(maxsize=None)
def _hex():
    return HEX.read_text().strip()


def _runtime(hex_code):
    x86 = X86Program.from_hex(hex_code, base_addr=0)
    return VerifiedSummaryRuntime(identify_basic_blocks(x86.instructions),
                                  X86SummaryConfig.enabled(calldataload="fallback"),
                                  timeout_ms=30000, max_depth=300)


def _state():
    state = SMTState.create_initial_state(num_inputs=0)
    state.assume_calldata_offset_no_overflow = False
    size = BitVec("fixed_cdl_size", 64)
    state.callengine_input_size_bytes = size
    state.calldatasize = size
    state.x86_registers.set_register(Register.R14, BitVecVal(0x8000, 64))
    return state


def test_matcher_recognizes_every_fixed_codegen_slice():
    x86 = X86Program.from_hex(_hex(), base_addr=0)
    summaries = discover_calldataload_summaries(identify_basic_blocks(x86.instructions))
    assert len(summaries) == 26
    assert all(s.wrap_free and not s.require_concrete_offset for s in summaries.values())


@pytest.mark.parametrize("offset", [
    (1 << 64) - 32,   # old codegen wrapped offset+32 to 0 here (SAT under the legacy shape)
    None,             # symbolic offset, bounded by the path condition below
])
def test_fixed_slice_is_proved_without_no_overflow_assumption(offset):
    # Symbolic calldata size over all of uint64; no offset/size assumption is added.
    # ponytail: a fully unbounded symbolic offset times out in effect_0 (Z3 unknown
    # at 300s); such hits fall back to raw execution.
    runtime = _runtime(_hex())
    summary = next(s for s in runtime.summaries if s.entry_addr == SYMBOLIC_ENTRY)
    state = _state()
    low = BitVec("fixed_cdl_off", 64) if offset is None else BitVecVal(offset, 64)
    for i, loc in enumerate(summary.payload.offset_limb_locs):
        assert isinstance(loc, RegisterLimbLocation)
        state.x86_registers.set_register(loc.reg, low if i == 0 else BitVecVal(0, 64))
    runtime.apply(summary, state,
                  path_condition=ULE(low, BitVecVal(32, 64)) if offset is None else None)
    assert runtime.certificates[-1].complete
    assert not state.assumptions


def test_tampered_partial_path_zero_fill_is_rejected():
    # cmp rax, 2 -> cmp rax, 3: byte 1 is zero-filled although it is in bounds.
    hex_code = _hex()
    at = PARTIAL_CMP2 * 2
    assert hex_code[at:at + 8] == "4883f802"
    runtime = _runtime(hex_code[:at] + "4883f803" + hex_code[at + 8:])
    summary = next(s for s in runtime.summaries if s.entry_addr == CONST_ENTRY)
    with pytest.raises(SummaryPreconditionError, match="effect_"):
        runtime.apply(summary, _state())
    assert not runtime.certificates


@pytest.mark.parametrize("code,dead", [
    ("488b06c3", False),             # mov rax, [rsi]; ret  -> tag observed
    ("4889f0c3", False),             # mov rax, rsi; ret    -> tag propagated
    ("48c7c600000000488b06c3", True),  # mov rsi, 0 kills it first
    ("f3a448c7c600000000c3", False),  # rep movsb reads rsi implicitly before the kill
])
def test_pointer_tag_liveness(code, dead):
    blocks = identify_basic_blocks(disassemble_hex(code, 0x100))
    assert pointer_tag_dead_at(blocks, 0x100, Register.RSI) is dead


@pytest.mark.slow
def test_generic_lemma_proved_once_then_instantiated(monkeypatch):
    from verification.block_summaries import LemmaInstanceCertificate
    monkeypatch.setenv("BLOCK_SUMMARY_LEMMAS", "1")
    runtime = _runtime(_hex())
    summary = next(s for s in runtime.summaries if s.entry_addr == SYMBOLIC_ENTRY)
    for n in range(2):
        state = _state()
        for i, loc in enumerate(summary.payload.offset_limb_locs):
            state.x86_registers.set_register(loc.reg, BitVec(f"lemma_off_{n}_{i}", 64))
        queries = runtime.proof_queries
        runtime.apply(summary, state)  # fully unbounded offset, no path condition
        cert = runtime.certificates[-1]
        assert isinstance(cert, LemmaInstanceCertificate) and cert.complete
        if n:  # second hit: no solver work at all
            assert runtime.proof_queries == queries
    assert not state.assumptions


def test_lemma_proof_uses_its_own_budget_and_restores_the_node_deadline(monkeypatch):
    # An exhausted node deadline must not starve the shared lemma (it would
    # never be cached); the node deadline is restored afterwards.
    from time import monotonic
    from verification import block_summaries as bs
    runtime = _runtime(_hex())
    summary = next(s for s in runtime.summaries if s.entry_addr == SYMBOLIC_ENTRY)
    expired = monotonic() - 1
    runtime.deadline = expired
    seen = []

    def generic_apply(self, summary, state, path_condition=None):
        seen.append(self.deadline)
        raise ValueError("lemma not provable in this test")

    monkeypatch.setattr(bs.VerifiedSummaryRuntime, "apply", generic_apply)
    key, lemma = runtime._lemma(summary, _state())
    assert seen and seen[0] > monotonic()          # lemma budget, not the expired node one
    assert lemma is None and runtime.deadline == expired
    assert runtime._lemma(summary, _state()) == (key, None) and len(seen) == 1   # cached, not retried


# --- position-independent lemma keys -------------------------------------------------------------

def _same_shape_pair(runtime):
    from verification.block_summaries import _relocated
    groups = {}
    for s in runtime.summaries:
        if s.kind == "calldataload":
            entry, continuation, owned = runtime._geometry(s)
            fingerprint = _MOVABLE_SLICE(runtime.blocks, owned, entry, continuation)
            groups.setdefault((fingerprint, repr(_relocated(s, entry))), []).append(s)
    a, b = next(g for key, g in groups.items() if key[0] is not None and len(g) > 1)[:2]
    assert a.entry_addr != b.entry_addr
    return a, b


def _fake_generic_proof(monkeypatch, joined=()):
    """Replace the ~5 min generic proof by a recorder; returns the list of proved entries."""
    from types import SimpleNamespace
    from verification import block_summaries as bs
    proved = []

    def generic_apply(self, summary, state, path_condition=None):
        proved.append(summary.entry_addr)
        self._joined.update(joined)
        self.certificates.append(SimpleNamespace(complete=True))
        return state

    monkeypatch.setattr(bs.VerifiedSummaryRuntime, "apply", generic_apply)
    return proved


def _lemma_pair(monkeypatch):
    """Lemmas for two same-shape slices under the movable key (the shifted
    key, tried first, is disabled here); the generic proof is faked."""
    from verification import block_summaries as bs
    runtime = _runtime(_hex())
    a, b = _same_shape_pair(runtime)
    monkeypatch.setattr(bs, "shifted_slice", lambda *args: None)
    proved = _fake_generic_proof(monkeypatch)
    (key_a, lemma_a), (key_b, lemma_b) = runtime._lemma(a, _state()), runtime._lemma(b, _state())
    return proved, (a, key_a, lemma_a), (b, key_b, lemma_b), runtime


def test_same_shape_slices_at_different_addresses_share_one_lemma(monkeypatch):
    proved, (a, key_a, lemma_a), (b, key_b, lemma_b), runtime = _lemma_pair(monkeypatch)
    assert proved == [a.entry_addr] and key_a == key_b and lemma_b is lemma_a
    entry_a, entry_b = runtime._geometry(a)[0], runtime._geometry(b)[0]
    assert lemma_a.origin == entry_a
    # The translation argument was checked on this pair, instruction by instruction.
    assert runtime.runtime._summary_lemmas[("steps", key_b, entry_b)] > 200


def test_failed_step_check_falls_back_to_the_per_address_lemma(monkeypatch):
    from verification import block_summaries as bs
    monkeypatch.setattr(bs, "same_step_semantics", lambda *args: None)
    proved, (a, key_a, _), (b, key_b, _), _ = _lemma_pair(monkeypatch)
    assert proved == [a.entry_addr, b.entry_addr] and key_a != key_b


def test_unmovable_slice_uses_the_per_address_key(monkeypatch):
    from verification import block_summaries as bs
    monkeypatch.setattr(bs, "movable_slice", lambda *args: None)
    proved, (a, key_a, _), (b, key_b, _), _ = _lemma_pair(monkeypatch)
    assert proved == [a.entry_addr, b.entry_addr] and key_a != key_b


@pytest.mark.parametrize("code,owned,continuation,movable", [
    ("4801d87400c3", (0, 3), 5, True),                # add; je -> continuation
    ("4801d8740390909090c3", (0, 3), 5, False),       # je leaves the slice
    ("488d050100000090c3", (0, 7), 8, False),          # lea rax, [rip+1]: value moves with the code
    ("488b042500100000c3", (0,), 8, False),            # absolute memory operand
    ("4801d8c3", (0, 3), 4, False),                   # ret inside the slice
])
def test_movable_slice_counterexamples(code, owned, continuation, movable):
    # The same bytes at two addresses: only a movable slice gets a shared fingerprint.
    from verification.block_summaries import movable_slice
    prints = [movable_slice(identify_basic_blocks(disassemble_hex(code, base)),
                            {base + o for o in owned}, base, base + continuation) for base in (0x100, 0x200)]
    assert (prints[0] is not None and prints[0] == prints[1]) is movable
    assert (prints[0] is None) is (not movable)


def test_step_semantics_distinguishes_rip_relative_code():
    from verification.block_summaries import generalize_state, same_step_semantics
    generic = generalize_state(SMTState.create_initial_state(num_inputs=0))
    at = lambda base: disassemble_hex("488d05010000004801d8", base)  # lea rax, [rip+1]; add rax, rbx
    assert same_step_semantics(at(0x100), at(0x200), generic) is None
    assert same_step_semantics(at(0x100)[1:], at(0x200)[1:], generic) == 1


# --- stack-shifted lemma keys (same slice at another stack depth) ---------------------------------

DEPTH_A, DEPTH_B = 0xB3144, 0xB46F2   # same slice, result slot r14-32 vs r14-64 (different bytes/layout)


def _summary(runtime, entry_addr):
    return next(s for s in runtime.summaries if s.entry_addr == entry_addr)


def test_slices_differing_only_in_stack_depth_share_one_lemma(monkeypatch):
    runtime = _runtime(_hex())
    a, b = _summary(runtime, DEPTH_A), _summary(runtime, DEPTH_B)
    assert b.payload.result_stack_offset - a.payload.result_stack_offset == -32
    (entry_a, cont_a, owned_a), (entry_b, cont_b, owned_b) = runtime._geometry(a), runtime._geometry(b)
    assert _MOVABLE_SLICE(runtime.blocks, owned_a, entry_a, cont_a) != _MOVABLE_SLICE(runtime.blocks, owned_b, entry_b, cont_b)
    proved = _fake_generic_proof(monkeypatch)
    (key_a, lemma_a), (key_b, lemma_b) = runtime._lemma(a, _state()), runtime._lemma(b, _state())
    assert proved == [a.entry_addr] and key_a == key_b and lemma_b is lemma_a
    assert lemma_a.origin == entry_a and lemma_a.origin_summary is a
    assert runtime.runtime._summary_lemmas[("shift", key_b, entry_b)] > 200   # proved step by step


def test_failed_shift_check_falls_back_to_the_existing_keys(monkeypatch):
    from verification import block_summaries as bs
    monkeypatch.setattr(bs, "shifted_step_semantics", lambda *args: None)
    runtime = _runtime(_hex())
    a, b = _summary(runtime, DEPTH_A), _summary(runtime, DEPTH_B)
    proved = _fake_generic_proof(monkeypatch)
    (key_a, _), (key_b, _) = runtime._lemma(a, _state()), runtime._lemma(b, _state())
    assert proved == [a.entry_addr, b.entry_addr] and key_a != key_b


def test_shifted_lemma_not_reused_where_a_joined_tag_is_live(monkeypatch):
    # 0xae1b5 and 0xb07d5 share the shifted key, but r8 is live after 0xb07d5's slice:
    # a lemma that joined r8's path-dependent tag (legal only when dead) must not apply there.
    runtime = _runtime(_hex())
    a, b = _summary(runtime, 0xAE1B5), _summary(runtime, 0xB07D5)
    assert runtime._shifted_key(a, _state())[0] == runtime._shifted_key(b, _state())[0]
    proved = _fake_generic_proof(monkeypatch, joined={Register.R8})
    (key_a, lemma_a), (key_b, lemma_b) = runtime._lemma(a, _state()), runtime._lemma(b, _state())
    assert lemma_a.joined == (Register.R8,)
    assert proved == [a.entry_addr, b.entry_addr] and key_a != key_b
    # without the joined fact the same pair shares
    runtime = _runtime(_hex())
    proved = _fake_generic_proof(monkeypatch)
    assert runtime._lemma(a, _state())[1] is runtime._lemma(b, _state())[1] and len(proved) == 1


def _shift_print(code, owned, continuation, anchor, base=0x100):
    from verification.block_summaries import shifted_slice
    blocks = identify_basic_blocks(disassemble_hex(code, base))
    found = shifted_slice(blocks, {base + o for o in owned}, base, base + continuation, anchor)
    return None if found is None else found[0]


SHIFT_BASE = ("49894608" "4801d8" "7400" "c3", (0, 4, 7), 9, 8)   # mov [r14+8], rax; add rax, rbx; je cont


@pytest.mark.parametrize("code,owned,continuation,anchor,shared", [
    # mov [r14], rax (shorter encoding) + alignment nop: same slice 8 bytes lower
    ("498906" "0f1f4000" "4801d8" "7400" "c3", (0, 3, 7, 10), 12, 0, True),
    ("49894628" "4801d8" "7400" "c3", (0, 4, 7), 9, 0x28, True),       # 0x20 higher
    ("49894628" "4801d8" "7400" "c3", (0, 4, 7), 9, 0x20, False),      # displacement moved alone
    ("49894608" "4883c001" "7400" "c3", (0, 4, 8), 10, 8, False),      # immediate instead of rbx
    ("49894608" "4801c8" "7400" "c3", (0, 4, 7), 9, 8, False),         # rcx instead of rbx
    ("49894608" "4801d8" "74f7" "c3", (0, 4, 7), 9, 8, False),         # je back to the entry
])
def test_shifted_slice_fingerprint(code, owned, continuation, anchor, shared):
    base = _shift_print(*SHIFT_BASE)
    assert base is not None
    assert (_shift_print(code, owned, continuation, anchor) == base) is shared


@pytest.mark.parametrize("code,owned,continuation", [
    ("4c89f0" "4801d8" "c3", (0, 3), 6),          # mov rax, r14: r14 used as a value
    ("4d8d7608" "4801d8" "c3", (0, 4), 7),        # lea r14, [r14+8]: stack base written
    ("4189c6" "4801d8" "c3", (0, 3), 6),          # mov r14d, eax: sub-register write
    ("4489f0" "4801d8" "c3", (0, 3), 6),          # mov eax, r14d: sub-register read
    ("488d0501000000" "90" "c3", (0, 7), 8),      # rip-relative
])
def test_shifted_slice_rejects(code, owned, continuation):
    assert _shift_print(code, owned, continuation, 0) is None


def test_shifted_step_semantics_proves_the_shift():
    from verification.block_summaries import generalize_state, shifted_step_semantics
    generic = generalize_state(_state())
    a = disassemble_hex("49894608" "4d8b4628" "4801d8", 0x100)   # mov [r14+8], rax; mov r8, [r14+0x28]; add
    b = disassemble_hex("498906" "4d8b4620" "4801d8", 0x200)     # the same 8 bytes lower
    assert shifted_step_semantics(a, b, [], -8, generic) == 3
    assert shifted_step_semantics(a, b, [], 8, generic) is None          # wrong delta
    assert shifted_step_semantics(a[:1], b[:1], [], -8, generic) == 1
    assert shifted_step_semantics(a[1:2], b[:1], [], -8, generic) is None  # load vs store
    # real slices: the proof depends on the exact delta
    runtime = _runtime(_hex())
    x, y = (runtime._shifted_slice(_summary(runtime, e)) for e in (DEPTH_A, DEPTH_B))
    assert shifted_step_semantics(x[4][1], y[4][1], x[4][2] + y[4][2], -32, generic) > 200
    assert shifted_step_semantics(x[4][1], y[4][1], [], -24, generic) is None


def test_shifted_summary_semantics_checks_offsets():
    from dataclasses import replace
    from verification.block_summaries import generalize_state, shifted_summary_semantics
    generic = generalize_state(_state())
    runtime = _runtime(_hex())
    a, b = _summary(runtime, DEPTH_A), _summary(runtime, DEPTH_B)
    assert shifted_summary_semantics(a, b, -32, generic)
    assert not shifted_summary_semantics(a, b, -24, generic)
    moved = replace(b, payload=replace(b.payload, result_stack_offset=b.payload.result_stack_offset + 8))
    assert not shifted_summary_semantics(a, moved, -32, generic)
    locs = b.payload.offset_limb_locs
    swapped = replace(b, payload=replace(b.payload, offset_limb_locs=(locs[1], locs[0], *locs[2:])))
    assert not shifted_summary_semantics(a, swapped, -32, generic)


# --- persisted lemma statements (proof_cache.statement_key) ---------------------------------------

def _persisted_lemma(monkeypatch, tmp_path, field, bound):
    """_prove_lemma in a FRESH runtime and cache connection, with a generic
    apply that builds its statement like the real one (entry/coverage via
    check, one effect refutation). Returns (lemma, solver calls)."""
    from types import SimpleNamespace
    from z3 import And, BoolVal, Not, ULT
    from verification import block_summaries as bs, proof_cache
    from verification.block_equivalence import Obligation
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "lemmas.sqlite"))
    proof_cache._CONNECTIONS.clear()
    calls = []
    real_solve, real_refute = bs.solve_query, bs.refute_goal
    monkeypatch.setattr(bs, "solve_query", lambda *a: calls.append(1) or real_solve(*a))
    monkeypatch.setattr(bs, "refute_goal", lambda *a: calls.append(1) or real_refute(*a))

    def generic_apply(self, summary, state, path_condition=None):
        assert self._generic_mode
        x = getattr(state, field)  # a generic constant named after the field path
        pre, goal = ULT(x, 10), ULT(x, bound)
        self._statement += [("entry", "sat", BoolVal(True), None),
                            ("coverage", "unsat", BoolVal(False), None),
                            ("effect_0", "unsat", And(pre, Not(goal)), (pre, goal))]
        records = tuple(Obligation(n, "", e, e) for n, e, _, _ in self._statement)
        self.certificates.append(bs.SummaryHitCertificate("id", records, 1, True, ("entry", "coverage", "effect_0")))
        return SimpleNamespace(x86_registers=None)

    monkeypatch.setattr(bs.VerifiedSummaryRuntime, "apply", generic_apply)
    runtime = bs.VerifiedSummaryRuntime([], None, runtime=SimpleNamespace())
    state = SimpleNamespace(**{field: BitVec("hit", 64)})
    _, lemma = runtime._prove_lemma({}, "key", SimpleNamespace(clobber_registers=()), state)
    return lemma, len(calls)


def test_proved_lemma_statement_is_reused_by_a_fresh_runtime_without_solving(monkeypatch, tmp_path):
    lemma, calls = _persisted_lemma(monkeypatch, tmp_path, "x", 11)
    assert lemma.complete and calls > 0
    # Fresh runtime and connection; the field (hence every symbol name) differs: alpha-equal statement.
    lemma, calls = _persisted_lemma(monkeypatch, tmp_path, "y", 11)
    assert lemma.complete and calls == 0


def test_changed_lemma_statement_is_not_reused(monkeypatch, tmp_path):
    from verification import proof_cache
    assert _persisted_lemma(monkeypatch, tmp_path, "x", 11)[0].complete
    lemma, calls = _persisted_lemma(monkeypatch, tmp_path, "x", 12)   # another (also true) statement
    assert lemma.complete and calls > 0
    lemma, calls = _persisted_lemma(monkeypatch, tmp_path, "x", 9)    # false: x = 9 refutes the effect
    assert lemma is None and calls > 0
    # ... and a failed statement is never recorded: the next runtime solves it again.
    lemma, calls = _persisted_lemma(monkeypatch, tmp_path, "x", 9)
    assert lemma is None and calls > 0
    assert proof_cache.lookup_hint("key") is None


def test_persisted_origin_hint_makes_another_process_prove_at_the_same_slice(monkeypatch, tmp_path):
    from verification import proof_cache
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "lemmas.sqlite"))
    proof_cache._CONNECTIONS.clear()
    runtime = _runtime(_hex())
    a, b = _summary(runtime, DEPTH_A), _summary(runtime, DEPTH_B)
    proved = _fake_generic_proof(monkeypatch)
    key_a, _ = runtime._lemma(a, _state())                 # "process 1" proves at A
    runtime = _runtime(_hex())                             # "process 2" first meets B
    key_b, lemma = runtime._lemma(b, _state())
    assert key_a == key_b and proved == [a.entry_addr, a.entry_addr]   # proved at A again (same statement)
    assert lemma.origin == runtime._geometry(a)[0]
    assert runtime.runtime._summary_lemmas[("shift", key_b, runtime._geometry(b)[0])] > 200
