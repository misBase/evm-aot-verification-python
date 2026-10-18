"""Task L (r3c unknown blocks): three generic fixes.

- entry_nonempty: a SAT-expected check never trusts a cached timeout
  (Permit2 1327 m=192 / 4837 m=384: "entry predicate empty or unknown" in
  0s for a premise that is SAT in 0.01s in a fresh process).
- model_domain_nonempty: the constant-function witness also restricts UFs
  over binder terms (PoolManager 5802: sha3_bytes_58 of bytes read through
  the R15 offset view λa. M[a - R15]; no array-parameter UF at all).
- shift_split: one case per value of a shift-amount constant (Permit2 4837
  x86_maps_12_0 / 14_0: 256-bit SHL against x86's limb-wise shift).
"""
from pathlib import Path

import pytest
from z3 import (And, Array, BitVec, BitVecSort, BitVecVal, Concat, Extract, Function, If, Lambda, LShR, Not, Select,
                Solver, ULE, ULT, UGT, ZeroExt, parse_smt2_file, parse_smt2_string, unsat)

import verification.block_equivalence as be
from verification import proof_cache
from verification.block_relation import BlockRelationSchema
from verification.block_specialization import BlockSpecialization

SMT2 = Path(__file__).resolve().parents[2] / "cloud-inputs" / "r3c" / "smt2"
BV8, BV64, BV256 = BitVecSort(8), BitVecSort(64), BitVecSort(256)


@pytest.fixture(autouse=True)
def _no_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _refuted(lemma):
    """A lemma's recorded query, re-solved from its own text."""
    solver = Solver()
    solver.set(timeout=60000)
    solver.add(parse_smt2_string(f"(assert {lemma.formula})", decls=_DECLS))
    return solver.check() == unsat


_DECLS = {}


# --- entry_nonempty: cached timeouts ------------------------------------------


def _entry_premise(spec):
    context = BlockRelationSchema().build_havoc(
        prefix=f"blk{spec.pc}_{spec.stack_depth}_{spec.memory_size}_{spec.free_memory_pointer}",
        host_gas_uf_enabled=True, assume_calldata_offset_no_overflow=False,
        abstract_calldataload_words=False, **spec.as_havoc_kwargs())
    return And(*(context.state.assumptions or []))


def test_cached_timeout_no_longer_fails_entry_nonempty(tmp_path, monkeypatch):
    # One timeout under load (here: forced) is recorded as {"unknown": 30000}; every
    # later alpha-equal entry premise (any pc/depth with m=384, f=256) then answered
    # "unknown" from the cache at once.
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    proof_cache._CONNECTIONS.clear()
    premise = _entry_premise(BlockSpecialization(4837, 9, 384, 256, ()))
    real = be._solve_query
    monkeypatch.setattr(be, "_solve_query", lambda f, t: "unknown")
    assert be.solve_query(be.simplify(premise), 30000) == "unknown"
    monkeypatch.setattr(be, "_solve_query", real)
    assert be.solve_query(be.simplify(premise), 30000) == "unknown"  # unsat-side behaviour unchanged
    assert be.solve_query(be.simplify(premise), 30000, trust_unknown=False) == "sat"
    other = _entry_premise(BlockSpecialization(1327, 10, 384, 256, ()))  # alpha-equal: same cache entry
    records = []
    assert be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._check(
        "entry_nonempty", other, records, expected="sat")
    assert records[-1].answer == "sat"
    proof_cache._CONNECTIONS.clear()


def test_entry_premises_of_the_r3c_instances_are_sat():
    for spec in (BlockSpecialization(1327, 10, 192, 128, ()), BlockSpecialization(4837, 9, 384, 256, ())):
        records = []
        assert be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._check(
            "entry_nonempty", _entry_premise(spec), records, expected="sat")


def test_decided_cached_answers_are_still_trusted(tmp_path, monkeypatch):
    monkeypatch.setenv("BLOCK_PROOF_CACHE", str(tmp_path / "cache.sqlite"))
    proof_cache._CONNECTIONS.clear()
    x = BitVec("ub_x", 8)
    assert be.solve_query(ULT(x, 4), 5000) == "sat"
    monkeypatch.setattr(be, "_solve_query", lambda f, t: (_ for _ in ()).throw(AssertionError("solved again")))
    assert be.solve_query(ULT(x, 4), 5000, trust_unknown=False) == "sat"
    proof_cache._CONNECTIONS.clear()


# --- model_domain_nonempty: witness tiers -------------------------------------

M = Array("ub_M", BV64, BV8)
r15, p = BitVec("ub_r15", 64), BitVec("ub_p", 64)
a = BitVec("ub_a", 64)
view = Lambda([a], Select(M, a - r15))  # x86 reads EVM memory at R15 + offset
sha3_16 = Function("ub_sha3_bytes_2", BitVecSort(16), BV256)
host_gas = Function("ub_host_gas_sload", BV256, BV256, BV64)
digest = sha3_16(Concat(Select(view, r15 + p), Select(view, r15 + p + 1)))
oracle = ULE(host_gas(digest, BitVecVal(0, 256)), 2100)
entry = And(ULT(r15, 1 << 47), ULT(p, 1 << 20))


def test_lambda_inside_a_bitvector_argument_is_restricted():
    formula = And(entry, oracle)
    assert be._array_argument_ufs(formula) == []  # the old witness had nothing to restrict
    assert [f.name() for f in be._binder_argument_ufs(formula)] == ["ub_host_gas_sload", "ub_sha3_bytes_2"]
    assert be.sat_by_constant_array_ufs(formula, 9000) == "sat"
    records = []
    assert be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)._check(
        "model_domain_nonempty", formula, records, expected="sat")


def test_tiers_grow_and_end_with_every_uf():
    window = Lambda([a], Select(M, p + a))
    slice_ = Function("ub_sha3_slice", be.ArraySort(BV64, BV8), BV256, BV256)
    plain = Function("ub_plain", BV64, BV64)
    formula = And(entry, ULE(host_gas(slice_(window, BitVecVal(32, 256)), BitVecVal(0, 256)), 2100), plain(p) == 3)
    tiers = [[f.name() for f in t] for t in be._witness_tiers(formula)]
    assert tiers == [["ub_sha3_slice"], ["ub_host_gas_sload", "ub_sha3_slice"],
                     ["ub_host_gas_sload", "ub_plain", "ub_sha3_slice"]]


def test_witness_never_claims_sat_for_unsat():
    formula = And(entry, oracle, ULT(r15, 0))
    assert be.sat_by_constant_array_ufs(formula, 9000) == "unknown"
    # Needs two different digests: no constant restriction is a model; still never "unsat".
    other = sha3_16(Concat(Select(view, r15 + p + 2), Select(view, r15 + p + 3)))
    assert be.sat_by_constant_array_ufs(And(entry, digest != other), 9000) == "unknown"


@pytest.mark.skipif(not (SMT2 / "model_domain_nonempty_e765d561caaa.smt2").exists(), reason="r3c SMT2 absent")
def test_poolmanager_5802_model_domain_nonempty():
    formula = And(*parse_smt2_file(str(SMT2 / "model_domain_nonempty_e765d561caaa.smt2")))
    records = []
    assert be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._check(
        "model_domain_nonempty", formula, records, expected="sat")
    assert records[-1].elapsed_seconds < 20


# --- shift_split --------------------------------------------------------------

xs = [BitVec(f"ub_x{i}", 64) for i in range(4)]
ss = [BitVec(f"ub_s{i}", 64) for i in range(4)]
X, S = Concat(*reversed(xs)), Concat(*reversed(ss))
s6 = Extract(5, 0, ss[0])
_DECLS.update({str(c): c for c in (*xs, *ss)})  # for _refuted: lemma texts name these


def _limb(k):
    """x86's limb k of X << s for 0 < s < 64: (x_k << s) | (x_{k-1} >> (64 - s)) (s6 * 63 == -s mod 64)."""
    low = LShR(xs[k - 1], ZeroExt(58, s6 * 63)) if k else BitVecVal(0, 64)
    return (xs[k] << ZeroExt(58, s6)) | low


# x86 path condition: 0 < s < 65 by a borrow test, s6 != 0, high limbs zero.
X86_PATH = [Extract(64, 64, ZeroExt(1, ss[0]) - 65) == 1, s6 != 0, (ss[1] | ss[2] | ss[3]) == 0]


def _evm_limb(k):
    return If(ULT(S, 256), Extract(64 * k + 63, 64 * k, X << S), BitVecVal(0, 64))


def test_shift_split_refutes_limbwise_shl():
    formula = And(*X86_PATH, Not(And(*[_evm_limb(k) == _limb(k) for k in range(4)])))
    lemmas = be.shift_split(formula, 30000)
    assert isinstance(lemmas, tuple)
    names = [l.name for l in lemmas]
    assert names.count("shift_upper") == 4 and names.count("shift_lower") == 1  # s1..s3 fixed, s0 split
    assert sum(n.startswith("shift_case_") for n in names) == 63  # s0 in 1..63
    assert all(_refuted(l) for l in lemmas)
    records = []
    assert be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._check("x86_maps_0_0", formula, records)


def test_shift_split_reports_a_real_counterexample():
    # A limb without the bits carried in from below: wrong whenever they are nonzero,
    # so some case is SAT (a model of F), never lemmas.
    wrong = And(*X86_PATH, _evm_limb(2) != (xs[2] << ZeroExt(58, s6)))
    assert be.shift_split(wrong, 30000) == "sat"
    records = []
    assert not be.BlockEquivalenceProver([], [], {}, timeout_ms=30000)._check("x86_maps_0_0", wrong, records)
    assert records[-1].answer == "sat"


def test_shift_split_needs_small_bounds():
    # s0 < 1000 exceeds _SHIFT_MAX_CASES: s0 is not split, only the fixed high limbs are
    # substituted (one case). The limb form is wrong for s0 >= 64, so that case is SAT.
    unbounded = And((ss[1] | ss[2] | ss[3]) == 0, ULT(ss[0], 1000), _evm_limb(3) != _limb(3))
    assert be.shift_split(unbounded, 30000) == "sat"
    # Valid: every lemma is a refutation of a query implied by F (here the small-conjunct
    # bound search alone already refutes it, since the goal is a small conjunct too).
    valid = And((ss[1] | ss[2] | ss[3]) == 0, ULT(ss[0], 1000), (X << S) != (X << ZeroExt(192, ss[0])))
    lemmas = be.shift_split(valid, 30000)
    assert isinstance(lemmas, tuple) and lemmas and all(_refuted(l) for l in lemmas)
    assert be.shift_split(And(*X86_PATH, xs[0] == 1), 30000) is None  # no symbolic shift


def test_shift_split_empty_bounds_refute():
    formula = And(UGT(ss[0], 70), ULT(ss[0], 60), (X << S) == 0)
    lemmas = be.shift_split(formula, 30000)
    assert isinstance(lemmas, tuple) and {l.name for l in lemmas} == {"shift_lower", "shift_upper"}
    assert all(_refuted(l) for l in lemmas)


@pytest.mark.skipif(not (SMT2 / "x86_maps_14_0_3cedcf6f0591.smt2").exists(), reason="r3c SMT2 absent")
def test_permit2_4837_x86_maps_14_0():
    formula = And(*parse_smt2_file(str(SMT2 / "x86_maps_14_0_3cedcf6f0591.smt2")))
    lemmas = be.shift_split(formula, 30000)
    assert isinstance(lemmas, tuple) and sum(l.name.startswith("shift_case_") for l in lemmas) == 63


# --- unify_uf_arguments: level pairs before cross-level pairs -------------------

g = Function("ub_g", BV64, BV64)


def test_same_level_pairs_are_tried_first(monkeypatch):
    # Two chains h_k = g(..h_{k-1}..), one per side (EVM / x86 spelling of the same
    # argument). Each level pair is entailed; every cross-level pair is not.
    c = BitVec("ub_c", 64)
    evm = [c + 1]
    x86 = [If(c == 0, 1, c + 1)]
    for _ in range(2):
        evm.append(g(evm[-1]) + 1)
        x86.append(If(c == 0, g(x86[-1]) + 1, g(x86[-1]) + 1))
    formula = And(c != 0, g(evm[-1]) != g(x86[-1]))
    tried = []
    real = be._prove_equal

    def spy(premise, x, y, *rest, **kw):
        nx, ny = be._uf_nesting(x, g, {}), be._uf_nesting(y, g, {})
        tried.append(nx == ny)
        return real(premise, x, y, *rest, **kw)
    monkeypatch.setattr(be, "_prove_equal", spy)
    unified, lemmas = be.unify_uf_arguments(formula, 3000)
    assert lemmas and tried[:3] == [True, True, True]  # the three level merges come first
    solver = Solver()
    solver.add(unified)
    assert solver.check() == unsat


def test_nesting_counts_binder_bodies():
    arr = be.ArraySort(BV64, BV8)
    f = Function("ub_f", arr, BV64)
    inner = f(Lambda([a], Extract(7, 0, a + p)))
    outer = f(Lambda([a], Extract(7, 0, inner + a)))
    assert be._uf_nesting(inner, f, {}) == 1 and be._uf_nesting(outer, f, {}) == 2


# --- unification: probe the merged formula after each memory merge --------------

hash_ = Function("ub_hash", be.ArraySort(BV64, BV8), BV64)
gas = Function("ub_gas", BV64, BV64)
q = BitVec("ub_q", 64)
# One byte stored at p, read back as two different terms (equal windows).
evm_window = Lambda([a], Select(be.Store(M, p, BitVecVal(7, 8)), p + a))
x86_window = Lambda([a], If(a == 0, BitVecVal(7, 8), Select(M, p + a)))


def test_on_merge_can_stop_merging():
    formula = And(gas(hash_(evm_window)) != gas(hash_(x86_window)), gas(q + 1) != gas(1 + q + 0 * p))
    seen = []
    unified, lemmas = be.unify_uf_arguments(formula, 5000, on_merge=lambda f, l, t: seen.append(t) or True)
    assert len(seen) == 1 and lemmas  # stopped after the first merge


def test_memory_merge_probe_refutes_early(monkeypatch):
    # After the window merge the formula is refuted; the later pairs (q vs 2q) never merge
    # and are not tried once the probe succeeds.
    formula = And(ULT(p, 1 << 20), ULT(r15, 1 << 47),
                  gas(hash_(evm_window)) != gas(hash_(x86_window)), gas(q) != gas(2 * q))
    calls = []
    real = be.BlockEquivalenceProver._after_unification

    def spy(self, unified, lemmas, cap):
        calls.append(cap)
        return real(self, unified, lemmas, cap)
    monkeypatch.setattr(be.BlockEquivalenceProver, "_after_unification", spy)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=5000)
    proved, answer, lemmas = prover._retry_with_uf_unification(formula, "unknown")
    assert answer == "unsat" and calls == [be._QUICK_EXACT_MS]  # the per-merge probe, quick budget
    assert any(l.name.startswith("unify_") for l in lemmas)


def test_bitvector_merges_are_not_probed(monkeypatch):
    c = BitVec("ub_c", 64)
    formula = And(c != 0, h64(If(c == 0, 5, c + 1)) != h64(c + 1))
    calls = []
    monkeypatch.setattr(be.BlockEquivalenceProver, "_after_unification",
                        lambda self, u, l, cap: calls.append(cap))
    be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._retry_with_uf_unification(formula, "unknown")
    assert calls == [3000]  # only the final attempt, as before


h64 = Function("ub_h64", BV64, BV64)
