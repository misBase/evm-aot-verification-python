"""Premise composition checks with synthetic paths, not an arithmetic slice proof."""
from dataclasses import replace

import pytest
from z3 import And, Bool, Bools, If, Not, Or, SolverFor

from tests.integration.test_single_ins_equivalence import X86_SDIV_CORE_HEX_SEQUENCE
from verification import block_equivalence as be
from verification.loop_induction import SegmentPath
from x86_64.aot_profile import AOT_COMPILER_PROFILE
from x86_64.cfg import identify_basic_blocks
from x86_64.disassembler import disassemble_hex
from x86_64.summaries import sdiv, signed_proof


def _synthetic_paths(monkeypatch, *, bad_assumption=False):
    blocks = identify_basic_blocks(disassemble_hex(X86_SDIV_CORE_HEX_SEQUENCE))
    [summary] = sdiv.discover_sdiv_summaries(blocks, strict=True)
    a, b = Bools("signed_premise_A signed_premise_B")
    captured = {"initial": None, "candidate": None, "paths": [], "effect_calls": []}
    real_effect = signed_proof.refute_signed_effect

    def raw_runner(blocks, initial, entry, stops, **kwargs):
        assert entry == summary.entry_addr and stops == {summary.payload.continuation_addr}
        assert not kwargs["summary_config"].builtin_modes
        captured["initial"] = initial
        for i, pc in enumerate((a, Not(a))):
            raw = initial.copy()
            raw.assumptions = [b if bad_assumption and i == 0 else pc]
            # A nontrivial scalar equality, established under the original pc.
            raw.callvalue = If(pc, initial.callvalue, initial.callvalue + 1)
            captured["paths"].append(SegmentPath("exit", summary.payload.continuation_addr, pc, raw))
        return captured["paths"], [], []

    def candidate_apply(payload, initial, **kwargs):
        candidate = initial.copy()
        captured["candidate"] = candidate
        return candidate, Bool("signed_premise_unused_took")

    def effect(pre, goal, timeout_ms):
        captured["effect_calls"].append((pre, goal))
        return real_effect(pre, goal, timeout_ms)

    monkeypatch.setattr("verification.loop_induction.run_x86_segment", raw_runner)
    monkeypatch.setattr(sdiv, "apply_sdiv_summary", candidate_apply)
    monkeypatch.setattr(signed_proof, "refute_signed_effect", effect)
    return summary, blocks, a, b, captured


def test_each_effect_uses_only_previously_proved_raw_assumptions(monkeypatch):
    summary, blocks, a, _, captured = _synthetic_paths(monkeypatch)
    queries, real_solve = [], be.solve_query

    def observed(query, timeout_ms):
        answer = real_solve(query, min(timeout_ms, 1000))
        queries.append((query, answer))
        return answer

    monkeypatch.setattr(be, "solve_query", observed)
    lemma = signed_proof.prove_signed_slice(summary, blocks, profile=AOT_COMPILER_PROFILE, timeout_ms=1000)
    assert lemma.complete and lemma.path_count == 2
    by_name = {record.name: record for record in lemma.obligations}
    assert by_name["coverage"].formula == Not(Or(a, Not(a))).sexpr()
    assert by_name["coverage"].proved
    assert len(captured["effect_calls"]) == 2
    assert any(query.eq(Not(Or(a, Not(a)))) and answer == "unsat" for query, answer in queries)

    for i, (pc, (pre, goal)) in enumerate(zip((a, Not(a)), captured["effect_calls"])):
        name = f"assumption_{i}_0"
        assumption = by_name[name]
        original_check = And(pc, Not(pc))
        assert assumption.formula == original_check.sexpr() and assumption.proved
        assert any(query.eq(original_check) and answer == "unsat" for query, answer in queries)
        # Both original PC and separately justified assumption must reach the gate.
        assert pre.num_args() == 2 and all(child.eq(pc) for child in pre.children())
        effect = by_name[f"effect_{i}"]
        assert effect.formula == And(pc, Not(goal)).sexpr()
        assert effect.provenance == "signed_full_state"
        assert effect.lemmas[0] is assumption
        assert effect.required_lemmas == tuple(child.name for child in effect.lemmas)
        assert name in effect.required_lemmas and "part_0" in effect.required_lemmas
        assert all(child.proved for child in effect.lemmas) and effect.proved
        assert not replace(effect, lemmas=effect.lemmas[1:]).proved
        assert not replace(effect, required_lemmas=effect.required_lemmas[1:]).proved
        unknown = replace(assumption, answer="unknown")
        assert not replace(effect, lemmas=(unknown, *effect.lemmas[1:])).proved

    assert not captured["initial"].assumptions and not captured["candidate"].assumptions


@pytest.mark.parametrize("failure", ["sat", "unknown"])
def test_an_unjustified_or_unknown_assumption_rejects_before_effect(monkeypatch, failure):
    summary, blocks, a, b, captured = _synthetic_paths(monkeypatch, bad_assumption=True)
    queries, real_solve = [], be.solve_query
    target = And(a, Not(b))

    def observed(query, timeout_ms):
        if failure == "unknown" and query.eq(target):
            # A real Z3 resource exhaustion, rather than a mocked solver answer.
            solver = SolverFor("QF_AUFBV")
            solver.set(timeout=1000, rlimit=1)
            solver.add(query)
            answer = str(solver.check())
            assert answer == "unknown" and "resource" in solver.reason_unknown()
        else:
            answer = real_solve(query, min(timeout_ms, 1000))
        queries.append((query, answer))
        return answer

    monkeypatch.setattr(be, "solve_query", observed)
    with pytest.raises(signed_proof.SignedProofError, match=f"assumption_0_0.*solver={failure}"):
        signed_proof.prove_signed_slice(summary, blocks, profile=AOT_COMPILER_PROFILE, timeout_ms=1000)
    assert any(query.eq(target) and answer == failure for query, answer in queries)
    assert not captured["effect_calls"]
    assert not captured["initial"].assumptions and not captured["candidate"].assumptions
    assert len(captured["paths"][0].state.assumptions) == 1
    assert captured["paths"][0].state.assumptions[0].eq(b)


def test_false_unproved_assumptions_cannot_make_a_wrong_effect_vacuous(monkeypatch):
    from verification import loop_induction
    summary, blocks, a, _, captured = _synthetic_paths(monkeypatch)
    synthetic_runner = loop_induction.run_x86_segment

    def wrong_runner(*args, **kwargs):
        paths, defects, notes = synthetic_runner(*args, **kwargs)
        paths[0].state.assumptions = [Not(a)]
        paths[0].state.callvalue = captured["initial"].callvalue + 1
        return paths, defects, notes

    monkeypatch.setattr(loop_induction, "run_x86_segment", wrong_runner)
    with pytest.raises(signed_proof.SignedProofError, match="assumption_0_0"):
        signed_proof.prove_signed_slice(summary, blocks, profile=AOT_COMPILER_PROFILE, timeout_ms=1000)
    assert not captured["effect_calls"]
    # The effect really is wrong on the original PC; adding its contradictory
    # assumption would turn that same query vacuously UNSAT.
    wrong = captured["paths"][0].state.callvalue != captured["candidate"].callvalue
    solver = SolverFor("QF_AUFBV")
    solver.set(timeout=1000)
    solver.add(a, wrong)
    assert str(solver.check()) == "sat"
    solver.add(Not(a))
    assert str(solver.check()) == "unsat"
