"""Task N4 (remaining-blocks-4): fixes 16 and later (cloud-inputs/reports/remaining-blocks-4.md)."""
from hashlib import sha256

from time import monotonic
from types import SimpleNamespace

from z3 import And, BitVec, BoolVal, UGE, ULT

import verification.block_equivalence as be

from tests.unit.test_block_summary_certificates import copy_case
from verification.block_parallel import slim
from verification.block_summaries import summary_text


# --- fix 16: summary-hit obligations keep the fingerprint, not the text -----------

def test_summary_text_is_the_fingerprint_slim_records(monkeypatch):
    monkeypatch.delenv("BLOCK_KEEP_SUMMARY_TEXT", raising=False)
    x = BitVec("n4_text_x", 64)
    formula = And(ULT(x, 7), ULT(3, x))
    assert summary_text(formula) == "sha256:" + sha256(formula.sexpr().encode()).hexdigest()
    monkeypatch.setenv("BLOCK_KEEP_SUMMARY_TEXT", "1")
    assert summary_text(formula) == formula.sexpr()


def test_hit_certificate_keeps_names_and_answers_and_slim_keeps_the_fingerprint(monkeypatch):
    monkeypatch.delenv("BLOCK_KEEP_SUMMARY_TEXT", raising=False)
    runtime, summary, state = copy_case(7)
    runtime.apply(summary, state)
    certificate = runtime.certificates[0]
    assert certificate.complete and all(o.formula.startswith("sha256:") and len(o.formula) == 71
                                        for o in certificate.obligations)
    # What a worker sends to the parent is unchanged: slim() keeps a fingerprint as it is.
    assert all(slim(o).formula == o.formula for o in certificate.obligations)


# --- fix 17: a row's remaining conjunct implications, proved as one group --------------

def _row(condition):
    return SimpleNamespace(kind="exit", location=0, condition=condition)


def test_row_group_proves_every_member_with_one_refutation():
    x = BitVec("n4_row_x", 8)
    conjuncts = [UGE(x, 10), ULT(x, 200), x != 50, x != 3, ULT(x, 255)]
    evm, x86 = [_row(And(*conjuncts))], [_row(And(UGE(x, 20), ULT(x, 40)))]
    done = {(0, 1): "already"}  # proved by a prefix pass: not regrouped
    be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._prove_row_groups(
        BoolVal(True), evm, x86, (0,), done, monotonic() + 60)
    assert set(done) == {(0, k) for k in range(5)} and done[(0, 1)] == "already"
    group = {done[(0, k)].formula for k in (0, 2, 3, 4)}
    assert len(group) == 1 and all(done[(0, k)].proved and done[(0, k)].name == f"x86_maps_0_{k}"
                                   for k in (0, 2, 3, 4))
    # The shared record is the group query, a weakening of each member's own query.
    assert "or" in next(iter(group)) or "not (and" in next(iter(group))


def test_failing_group_is_halved_and_never_proves_a_false_member():
    x = BitVec("n4_row_y", 8)
    conjuncts = [UGE(x, 10), ULT(x, 200), x != 50, x != 3, x != 25, ULT(x, 255), UGE(x, 20), x != 7]
    evm, x86 = [_row(And(*conjuncts))], [_row(And(UGE(x, 20), ULT(x, 40)))]  # x != 25 fails
    done = {}
    be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._prove_row_groups(
        BoolVal(True), evm, x86, (0,), done, monotonic() + 60)
    order = [c.sexpr() for c in be._conjuncts(evm[0].condition)]  # the indices x86_maps_j_k use
    false = order.index((x != 25).sexpr())  # x86 path x = 25 violates it
    assert (0, false) not in done and done and all(r.proved for r in done.values())
    # Only the half without it is proved; its own half (4 members) is too small to split.
    half = set(range(4)) if false >= 4 else set(range(4, 8))
    assert {k for _, k in done} == half


def test_row_groups_skip_unmapped_rows_and_small_remainders():
    x = BitVec("n4_row_z", 8)
    evm = [_row(And(UGE(x, 10), ULT(x, 200), x != 3))]
    x86 = [_row(UGE(x, 20)), _row(ULT(x, 5))]
    done = {}
    be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._prove_row_groups(
        BoolVal(True), evm, x86, (0, "all"), done, monotonic() + 60)
    assert done == {}  # row 0: 3 conjuncts < _ROW_GROUP_MIN; row 1 is not a kept row
