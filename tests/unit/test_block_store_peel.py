"""Safe 5377 d30 pair_68_58: peel matching store prefixes off a memory read
disequality (peel_matching_stores), and retry a timed-out light-premise probe.

A[i] ≠ B[i + d] with A = store(X, a, v), B = store(Y, a + d, v) implies
X[i] ≠ Y[i + d], so the peeled formula is implied by the original: only its
UNSAT transfers back.
"""
from random import Random

import pytest
from z3 import (And, Array, ArraySort, BitVec, BitVecSort, BitVecVal, BoolVal, Distinct, Extract, Function, If, Lambda,
                Not, Select, Store, ULT, simplify)

import verification.block_equivalence as be

BV64, BV8 = BitVecSort(64), BitVecSort(8)
M, C = Array("sp_M", BV64, BV8), Array("sp_C", BV64, BV8)
i, w, d, f, o, n = (BitVec(f"sp_{s}", 64) for s in "iwdfon")
x, y, z = (BitVec(f"sp_{s}", 64) for s in "xyz")


@pytest.fixture(autouse=True)
def _no_cache_no_pool(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def _chain(base, address, values):
    for k, value in enumerate(values):
        base = Store(base, address + k, value)
    return base


# The copy region as each side writes it: EVM counts from the copy start, x86 from R15 + start.
EVM_COPY = Lambda([i], If(ULT(i - f, n), Select(C, o + (i - f)), Select(M, i)))
X86_COPY = Lambda([i], If(ULT(i - d - f, n), Select(C, o + (i - d - f)), Select(M, i - d)))
WORD = [Extract(8 * k + 7, 8 * k, x) for k in range(8)]


def test_matching_stores_peel_down_to_the_bases():
    A, B = _chain(EVM_COPY, f, WORD), _chain(X86_COPY, d + f, WORD)
    F = And(x == y, Select(A, w) != Select(B, d + w))
    peeled, lemmas = be.peel_matching_stores(F)
    assert "store" not in peeled.sexpr()  # all 8 stores peeled, the base reads beta-reduced
    assert [l.name for l in lemmas] == ["store_peel_0"] and lemmas[0].answer == "unsat" and lemmas[0].proved
    assert be.solve_query(peeled, 5000) == "unsat"
    assert be.solve_query(F, 5000) == "unsat"


def test_distinct_and_flipped_offset_forms_peel_too():
    A, B = _chain(EVM_COPY, f, WORD), _chain(X86_COPY, f + d, WORD)
    assert be.peel_matching_stores(Distinct(Select(A, w), Select(B, w + d))) is not None
    assert be.peel_matching_stores(Not(Select(B, w + d) == Select(A, w))) is not None


def test_peeling_stops_at_the_first_mismatch():
    # Different values, or an address off by one: nothing peels.
    A = _chain(M, f, WORD)
    assert be.peel_matching_stores(Select(A, w) != Select(_chain(M, f, WORD[1:] + WORD[:1]), w)) is None
    assert be.peel_matching_stores(Select(A, w) != Select(_chain(M, f + 1, WORD), w)) is None
    # A store on top of one side only: the matching ones below it stay (no reordering).
    top = Store(_chain(M, f, WORD), z, BitVecVal(7, 8))
    assert be.peel_matching_stores(Select(top, w) != Select(_chain(M, f, WORD), w)) is None
    # Not a top-level read disequality: untouched.
    assert be.peel_matching_stores(Not(And(x == y, Select(A, w) == Select(A, w + 1)))) is None


def test_peeled_formula_is_only_a_weakening():
    # The bases differ exactly where the store overwrites them: F is UNSAT, the
    # peeled formula (which forgets w ≠ f) is SAT. Peeling must not hide this.
    X = Lambda([i], If(i == f, BitVecVal(0, 8), Select(M, i)))
    Y = Lambda([i], If(i == f, BitVecVal(5, 8), Select(M, i)))
    F = Select(Store(X, f, BitVecVal(1, 8)), w) != Select(Store(Y, f, BitVecVal(1, 8)), w)
    assert be.solve_query(F, 3000) == "unsat"
    peeled, _ = be.peel_matching_stores(F)
    assert be.solve_query(peeled, 3000) == "sat"


@pytest.mark.parametrize("seed", range(12))
def test_peeled_unsat_implies_original_unsat_on_random_chains(seed):
    rng = Random(seed)
    B8 = BitVecSort(8)
    P, Q = Array("sp_rp", B8, B8), Array("sp_rq", B8, B8)
    a, j, e = (BitVec(f"sp_r{s}", 8) for s in "aje")
    values = [rng.choice([BitVecVal(rng.getrandbits(8), 8), Select(P, a + k)]) for k in range(rng.randint(1, 4))]
    base_q = rng.choice([P, Q, Lambda([BitVec("sp_rk", 8)], Select(P, BitVec("sp_rk", 8) - e))])
    A = _chain(P, a, values)
    B = _chain(base_q, a + e, values)
    F = And(Select(A, j) != Select(B, j + e), *([Q == P] if rng.random() < 0.5 else []))
    peeled, _ = be.peel_matching_stores(F)
    if be.solve_query(peeled, 3000) == "unsat":
        assert be.solve_query(F, 3000) == "unsat"
    if be.solve_query(F, 3000) == "sat":
        assert be.solve_query(peeled, 3000) == "sat"


def _sha3_memory_goal():
    # Two sha3 applications that merge (pointwise equal slices under v == M[k]); both
    # memories store the hash's low byte above a copy region, the x86 side at R15 + addr.
    sha3 = Function("sp_sha3_slice", ArraySort(BV64, BV8), BV64, BV64)
    k, v = BitVec("sp_k", 64), BitVec("sp_v", 8)
    L_store = Lambda([i], If(ULT(i, n), Select(Store(M, k, v), i), BitVecVal(0, 8)))
    L_plain = Lambda([i], If(ULT(i, n), Select(M, i), BitVecVal(0, 8)))
    A = Store(_chain(EVM_COPY, f, WORD), f + 8, Extract(7, 0, sha3(L_store, n)))
    B = Store(_chain(X86_COPY, d + f, WORD), d + f + 8, Extract(7, 0, sha3(L_plain, n)))
    return And(v == Select(M, k), x * y == z, Select(A, w) != Select(B, d + w))


def test_unification_route_refutes_the_peeled_memory_goal():
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=10000)
    proved, answer, lemmas = prover._retry_with_uf_unification(_sha3_memory_goal(), "unknown")
    names = [l.name for l in lemmas]
    assert answer == "unsat" and "opaque_array_uf_peeled_light" in names and "store_peel_0" in names, names
    assert all(l.answer == "unsat" for l in lemmas)
    assert be.solve_query(simplify(proved), 5000) == "unsat"


def test_unpeeled_query_still_runs_when_the_peeled_one_is_not_refuted(monkeypatch):
    # A peeled formula too weak to refute (here: True, implied by anything) costs one
    # attempt; the unpeeled opaque query then runs as before.
    monkeypatch.setattr(be, "peel_matching_stores", lambda q: (BoolVal(True), ()))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=10000)
    _, answer, lemmas = prover._retry_with_uf_unification(_sha3_memory_goal(), "unknown")
    names = [l.name for l in lemmas]
    assert answer == "unsat" and "opaque_array_uf_light" in names, names
    assert not any(n.startswith(("opaque_array_uf_peeled", "store_peel")) for n in names), names


# Light-premise probe: one retry after a timeout ------------------------------------------

def test_timed_out_light_probe_is_retried_with_the_callers_budget(monkeypatch):
    calls = []
    answers = iter(["unknown", "unsat"])
    monkeypatch.setattr(be, "solve_query", lambda q, ms: calls.append(ms) or next(answers))
    parts = [x == y, x * y == z]
    assert be._refute_over_light_premise(parts, x != y, 2000, 30000) is not None
    assert calls == [2000, 30000]


def test_sat_light_probe_is_not_retried(monkeypatch):
    calls = []
    monkeypatch.setattr(be, "solve_query", lambda q, ms: calls.append(ms) or "sat")
    assert be._refute_over_light_premise([x == y, x * y == z], x != y, 2000, 30000) is None
    assert calls == [2000]
    calls.clear()
    monkeypatch.setattr(be, "solve_query", lambda q, ms: calls.append(ms) or "unknown")
    assert be._refute_over_light_premise([x == y, x * y == z], x != y, 2000) is None  # no retry budget
    assert calls == [2000]


def test_prove_equal_retries_with_its_budget_bounded_by_the_deadline(monkeypatch):
    from time import monotonic
    seen = []
    real = be._refute_over_light_premise
    monkeypatch.setattr(be, "_refute_over_light_premise",
                        lambda parts, goal, ms, retry=0: seen.append((ms, retry)) or real(parts, goal, ms, retry))
    assert be._prove_equal(And(x == y, x * y == z), x, y, 30000, None) is not None
    assert seen[-1] == (be._LIGHT_MS, 30000)
    be._prove_equal(And(x == y + 1, x * y == z), x, y, 30000, monotonic() + 5)
    assert seen[-1][0] <= be._LIGHT_MS and 0 < seen[-1][1] <= 5000
