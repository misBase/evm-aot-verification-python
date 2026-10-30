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


# --- fix 18: short register-only diamonds merged at their join (executor) --------------

# cmp rax, rbx; jb L; add rbx, 0x1f; jmp J; L: movabs rbx, 2^59; J: mov rcx, rbx; ret
_DIAMOND = "4839d8" "7206" "4883c31f" "eb0a" "48bb0000000000000008" "4889d9" "c3"
# The same, but the jb side also stores rbx to [r15] (memory differs: never merged).
_DIAMOND_STORE = "4839d8" "7206" "4883c31f" "eb0d" "48bb0000000000000008" "49891f" "4889d9" "c3"


def _run_diamond(hex_code, merge):
    from z3 import BitVecVal
    from state.smt_state import PointerTag, SMTState
    from x86_64.cfg import identify_basic_blocks
    from x86_64.cfg_executor import X86SymbolicExecutor
    from x86_64.disassembler import disassemble_hex
    from x86_64.models import Register
    blocks = identify_basic_blocks(disassemble_hex(hex_code, base_addr=0x1000))
    state = SMTState()
    state.x86_registers.set_register(Register.R15, BitVecVal(0x2000, 64))
    state.x86_registers.set_pointer_tag(Register.R15, PointerTag.EVM_PTR)
    executor = X86SymbolicExecutor(blocks, max_depth=20, enable_merge=False, merge_diamonds=merge)
    return executor, executor.execute(state)


def test_register_only_diamond_merges_into_one_exact_state():
    from z3 import BitVec, BitVecVal, If, Solver, ULT, unsat
    from x86_64.models import Register
    executor, finals = _run_diamond(_DIAMOND, merge=0)
    _, apart = _run_diamond(_DIAMOND, merge=None)
    assert len(apart) == 2 and len(finals) == 1 and executor.merged_diamonds == 1
    (final,) = finals
    rax, rbx = BitVec("rax_init", 64), BitVec("rbx_init", 64)
    expected = If(ULT(rax, rbx), BitVecVal(1 << 59, 64), rbx + 0x1f)
    solver = Solver()  # the merged rcx is the program's on every input, and the path is all inputs
    solver.add(final.mstate.x86_registers.get_register(Register.RCX) != expected)
    solver.add(final.get_constraints().as_bool())
    assert solver.check() == unsat
    covers = Solver()
    covers.add(final.get_constraints().as_bool() == False)  # noqa: E712
    assert covers.check() == unsat


def test_diamonds_merge_only_once_the_run_has_more_paths_than_the_threshold():
    # One fork, no earlier paths: a threshold of 1 is not reached, so the run stays as unmerged.
    executor, finals = _run_diamond(_DIAMOND, merge=1)
    assert len(finals) == 2 and executor.merged_diamonds == 0


def test_diamond_whose_sides_differ_in_memory_stays_apart():
    executor, finals = _run_diamond(_DIAMOND_STORE, merge=0)
    assert len(finals) == 2 and executor.merged_diamonds == 0


# --- fix 19: unify_across stops after a stall without merges ---------------------------

def test_unify_across_stops_after_a_stall_and_never_merges_unproved():
    from z3 import BitVecSort, Function, Solver, unsat
    g = Function("n4_stall_g", BitVecSort(8), BitVecSort(8))
    a, b, d = BitVec("n4_stall_a", 8), BitVec("n4_stall_b", 8), BitVec("n4_stall_d", 8)
    f1 = And(a == b, g(a) != g(b))
    f2 = And(a == b, d == 1, g(a) != g(b))
    out, lemmas = be.unify_across([f1, f2], 3000, stall_seconds=0)  # stalled before any candidate
    assert not lemmas and out[0].eq(f1) and out[1].eq(f2)
    out, lemmas = be.unify_across([f1, f2], 3000, stall_seconds=60)  # a merge in time: unchanged behaviour
    assert lemmas and all(Solver().check(f) == unsat for f in out)


# --- fix 20: the shared forwarding cache is bounded at hit boundaries ------------------

def test_shared_forward_cache_is_kept_within_a_scope_and_dropped_between_scopes(monkeypatch):
    from z3 import Array, BitVecSort, BitVecVal, Select, Store
    import common.store_forwarding as sf
    monkeypatch.setattr(sf, "_SHARED_FORWARD_LIMIT", 10)
    sf._SHARED_FORWARD.clear()
    a, k = Array("n4_fw_a", BitVecSort(64), BitVecSort(8)), BitVec("n4_fw_k", 64)
    chain = a
    for i in range(8):
        chain = Store(chain, k + i, BitVecVal(i, 8))
    sf.shared_forward_scope()
    loads = [Select(chain, k + i) for i in range(8)]
    for load in loads:  # one scope: never dropped, however large it grows
        assert sf.forward_selects_shared(load).eq(sf.forward_selects(load))
    size = len(sf._SHARED_FORWARD)
    assert size >= 10
    sf.shared_forward_scope()  # next hit: over the bound, so dropped
    assert not sf._SHARED_FORWARD
    assert sf.forward_selects_shared(loads[3]).eq(BitVecVal(3, 8))
    sf._SHARED_FORWARD.clear()


# --- fix 21: correspondence size estimate counts divergence groups, not EVM pairs -------

def test_correspondence_is_kept_when_disjointness_needs_few_group_queries():
    x = BitVec("n4_corr_x", 8)
    # Executor-shaped: And(constraints in execution order), so path i diverges from all later ones at once.
    evm = [_row(And(*(x != k for k in range(i)), x == i)) for i in range(9)]
    evm.append(_row(And(*(x != k for k in range(9)), UGE(x, 9))))  # 10 paths, 45 EVM pairs
    x86 = [_row(x == i) for i in (0, 3, 5, 7)] + [_row(UGE(x, 20))]  # 5 rows: 50 product pairs
    assert len(be.disjoint_groups(BoolVal(True), [e.condition for e in evm])) < 45
    records = []
    corr = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._correspondence(evm, x86, BoolVal(True), records)
    # Counted per EVM pair (45 + 2·5 >= 50) this was the full product.
    assert corr == (0, 3, 5, 7, 9)
    assert {r.name for r in records} == {f"evm_disjoint_{i}_{k}" for i in range(10) for k in range(i + 1, 10)}


# --- fix 22: the lia route's limb joins respect the route deadline ---------------------

def test_lia_limb_joins_stop_at_the_deadline(monkeypatch):
    import time
    x = BitVec("n4_lia_x", 64)
    calls = []

    def slow(query, timeout_ms):
        calls.append(timeout_ms)
        time.sleep(0.05)
        return "unknown"
    monkeypatch.setattr(be, "_nonlinear_mul_terms", lambda t: True)
    monkeypatch.setattr(be, "split_limb_joins", lambda t: [(x + i, x + i + 1) for i in range(100)])
    monkeypatch.setattr(be, "solve_query", slow)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)
    prover.deadline = monotonic() + 0.3
    started = monotonic()
    assert prover._retry_over_lia(ULT(x, 3))[1] == "unknown"
    assert monotonic() - started < 2 and len(calls) < 20  # 100 joins x 4 rounds without the check
