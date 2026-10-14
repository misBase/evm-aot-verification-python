"""Path correspondence instead of the full EVM x x86 pair product."""
from types import SimpleNamespace

from z3 import And, BitVec, BoolVal, ULT, UGE

import verification.block_equivalence as be
from verification.block_equivalence import BlockTheorem, Obligation, pair_obligation_names


def _theorem(names, n, m, correspondence=(), answer="unsat", arity=()):
    base = ["entry_nonempty", "havoc_relation", "model_domain_nonempty", "evm_coverage", "x86_coverage"]
    required = tuple(base + names)
    obligations = tuple(Obligation(name, "f", answer) for name in required)
    return BlockTheorem("id", None, obligations, required, "d", n, m, True,
                        correspondence=correspondence, arity=arity)


def test_full_product_unchanged():
    names = pair_obligation_names(2, 3)
    assert _theorem(names, 2, 3).complete
    assert not _theorem(names[:-1], 2, 3).complete


def test_mapping_complete_only_with_disjointness_and_maps():
    corr, arity = (0, 1, None, "all"), (2, 1, 0, 0)
    names = pair_obligation_names(2, 4, corr, arity)
    assert {"evm_disjoint_0_1", "x86_maps_0_0", "x86_maps_0_1", "x86_empty_2", "pair_1_3"} <= set(names)
    assert _theorem(names, 2, 4, corr, arity=arity).complete
    for missing in ("evm_disjoint_0_1", "x86_maps_0_1", "pair_1_1", "x86_empty_2", "pair_0_3"):
        assert not _theorem([n for n in names if n != missing], 2, 4, corr, arity=arity).complete, missing


def test_under_reported_arity_is_rejected():
    # The manifest (required) carries the true arity; a theorem claiming fewer
    # conjuncts cannot match it.
    corr = (0, 1)
    required = pair_obligation_names(2, 2, corr, (3, 1))
    fewer = [n for n in required if n != "x86_maps_0_2"]
    base = ["entry_nonempty", "havoc_relation", "model_domain_nonempty", "evm_coverage", "x86_coverage"]
    obligations = tuple(Obligation(name, "f", "unsat") for name in base + fewer)
    theorem = BlockTheorem("id", None, obligations, tuple(base + required), "d", 2, 2, True,
                           correspondence=corr, arity=(2, 1))
    assert not theorem.complete


def test_mapping_rejects_bad_entries():
    names = pair_obligation_names(2, 2, (0, 1), (1, 1))
    for corr in ((0, 5), (0, True), (0, "x"), (0,)):
        assert not _theorem(names, 2, 2, corr, arity=(1, 1)).complete, corr
    assert not _theorem(names, 2, 2, (0, 1), arity=(1, 0)).complete


def test_unproved_mapping_obligation_blocks_theorem():
    corr = (0, 1)
    names = pair_obligation_names(2, 2, corr, (1, 1))
    assert not _theorem(names, 2, 2, corr, answer="unknown", arity=(1, 1)).complete


def _paths(conditions):
    return [SimpleNamespace(condition=c) for c in conditions]


def test_correspondence_maps_by_model_and_requires_disjoint_evm():
    x = BitVec("corr_x", 8)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    evm = _paths([ULT(x, 10), UGE(x, 10), BoolVal(False)])
    # x86 splits finer than EVM: many paths, each inside one EVM path.
    x86 = _paths([ULT(x, 3), And(UGE(x, 3), ULT(x, 10)), And(UGE(x, 10), ULT(x, 20)), UGE(x, 20), x == 255, x == 0])
    records = []
    corr = prover._correspondence(evm, x86, BoolVal(True), records)
    assert corr == (0, 0, 1, 1, 1, 0)
    assert {r.name for r in records} == {"evm_disjoint_0_1", "evm_disjoint_0_2", "evm_disjoint_1_2"}


def test_overlapping_evm_paths_fall_back_to_full_product():
    x = BitVec("corr_y", 8)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    evm = _paths([ULT(x, 10), ULT(x, 20), UGE(x, 20)])  # 0 and 1 overlap
    x86 = _paths([x == i for i in range(8)])
    records = []
    assert prover._correspondence(evm, x86, BoolVal(True), records) == ()
    assert records == []  # trial disjointness records are not kept


def test_small_nodes_keep_full_product():
    x = BitVec("corr_z", 8)
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    assert prover._correspondence(_paths([ULT(x, 1), UGE(x, 1)]), _paths([BoolVal(True)]), BoolVal(True), []) == ()


def test_empty_probe_only_for_unknown_rows_without_sibling_proposal(monkeypatch):
    import z3
    x = BitVec("corr_u", 8)
    at = lambda c, loc: SimpleNamespace(condition=c, kind="terminal", location=loc)
    evm = _paths([ULT(x, 10), And(UGE(x, 10), ULT(x, 20)), UGE(x, 20)])
    seven, big = x == 7, x == 200
    hard = {seven.get_id(), big.get_id()}  # rows whose quick query is "unknown"
    x86 = [at(ULT(x, 5), "A"), at(And(UGE(x, 5), ULT(x, 10)), "A"), at(UGE(x, 20), "C"), at(seven, "A"), at(big, "D")]
    real, probed = be.PrefixSolver.check, []
    monkeypatch.setattr(be.PrefixSolver, "check", lambda self, conjuncts, *a: z3.unknown
                        if any(c.get_id() in hard for c in conjuncts) else real(self, conjuncts, *a))
    monkeypatch.setattr(be.BlockEquivalenceProver, "_empty_by_bvabs", lambda self, p, x: probed.append(x.location) or True)
    corr = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)._correspondence(evm, x86, BoolVal(True), [])
    # Row 3's siblings at A agree on EVM 0 (prove() proposes it); only row 4 is probed for emptiness.
    assert corr == (0, 0, 2, "all", None) and probed == ["D"]


def test_all_rows_share_one_prefix_refutation_and_never_drop_a_real_pair():
    from time import monotonic
    x, y = BitVec("rows_x", 8), BitVec("rows_y", 8)
    p = lambda c: SimpleNamespace(kind="exit", location=0, condition=c)
    # Two "all" rows share x < 10 and differ afterwards; EVM path 0 (x >= 10)
    # conflicts with the shared prefix, EVM path 1 (x < 10, y == 1) only with row 1.
    evm = [p(UGE(x, 10)), p(And(ULT(x, 10), y == 1))]
    x86 = [p(And(ULT(x, 10), y == 1)), p(And(ULT(x, 10), y == 2))]
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=3000)
    done = prover._discharge_all_rows(BoolVal(True), evm, x86, [0, 1], monotonic() + 60)
    assert set(done) == {(0, 0), (0, 1), (1, 1)}  # (1, 0) is jointly satisfiable: a real pair
    assert all(r.proved for r in done.values()) and done[(0, 1)].name == "pair_0_1"
    assert done[(0, 0)].formula == done[(0, 1)].formula  # one shared prefix refutation
