"""Checked common-premise proofs remain local to bases that imply them."""
from dataclasses import replace
import gc
import pickle
import shutil
from time import monotonic
import zlib

import pytest
from z3 import And, Array, BitVec, BitVecSort, Bool, If, Lambda, Not, Select, Store

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.cutpoint_relation import RelationGoal


def prover():
    p = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    p.deadline = monotonic() + 30
    return p


def targets(goal):
    return [("target", (RelationGoal("gas", goal),))]


@pytest.fixture(autouse=True)
def no_persistent_cache(monkeypatch):
    monkeypatch.delenv("BLOCK_PROOF_CACHE", raising=False)
    monkeypatch.delenv("BLOCK_PAIR_WORKERS", raising=False)


def test_same_raw_goal_cannot_escape_its_checked_subgroup():
    x = BitVec("canonical_same_raw_x", 8)
    goal = If(x == 0, x, x + 1) == x
    bases = [x == 0] * 4 + [x == 1] * 4
    gs = [targets(goal)] * len(bases)
    p = prover()
    shared = bp.prepare_shared(p, bases, gs)
    assert shared["canonical_proofs"] and not shared["done"]
    records = [bp.close_edge(p, f"same_raw_{i}", base, g, shared)
               for i, (base, g) in enumerate(zip(bases, gs))]
    assert [r.proved for r in records] == [True] * 4 + [False] * 4
    assert all(r.answer == "sat" for r in records[4:])
    assert not any(v is not None for v in shared["done"].values())


@pytest.fixture
def canonical_edge():
    x, y = BitVec("canonical_forward_x", 8), BitVec("canonical_forward_y", 8)
    flag = Bool("canonical_forward_flag")
    array = Array("canonical_forward_array", BitVecSort(64), BitVecSort(8))
    branch = BitVec("canonical_forward_branch", 8)
    bases = [And(Not(flag), branch == i) for i in range(4)]
    goals = [targets(If(flag, y, x) == Select(Store(Store(array, 0, x), i + 1, y), 0))
             for i in range(4)]
    p = prover()
    shared = bp.prepare_shared(p, bases, goals)
    assert len(shared["canonical_proofs"]) == 1
    assert len({g[0][1][0].condition.get_id() for g in goals}) == 4
    records = [bp.close_edge(p, f"canonical_forward_{i}", base, goal, shared)
               for i, (base, goal) in enumerate(zip(bases, goals))]
    assert all(r.proved and r.required_lemmas for r in records)
    assert all(r.lemmas[0].name.startswith(f"canonical_forward_{i}_canonical_")
               for i, r in enumerate(records))
    assert not shared["done"]
    return records[0]


def test_different_store_chains_share_only_an_exact_normalized_goal(canonical_edge):
    assert canonical_edge.proved


def test_singletons_and_binders_do_not_run_extra_solvers(monkeypatch):
    def unexpected(*args, **kwargs):
        pytest.fail("a singleton or binder must not cause a common-premise proof")
    monkeypatch.setattr(be, "refute_conditional_ites", unexpected)
    monkeypatch.setattr(be, "solve_query", unexpected)
    bases = [And()] * 4
    goals = []
    for i in range(4):
        x, y = BitVec(f"canonical_singleton_x{i}", 8), BitVec(f"canonical_singleton_y{i}", 8)
        goals.append(targets(If(Bool(f"canonical_singleton_flag{i}"), x, y) == x))
    assert not bp.prepare_shared(prover(), bases, goals)["canonical_proofs"]
    i = BitVec("canonical_bound_i", 64)
    array = Array("canonical_bound_array", BitVecSort(64), BitVecSort(8))
    binder = Lambda(i, If(i == 0, Select(array, i), 0))
    assert "canonical_proofs" not in bp.prepare_shared(prover(), bases, [targets(binder == array)] * 4)


def test_unknown_common_attempt_keeps_the_original_edge_fallback(monkeypatch):
    flag = Bool("canonical_unknown_flag")
    x, y = BitVec("canonical_unknown_x", 8), BitVec("canonical_unknown_y", 8)
    goal = If(flag, y, x) == x
    bases = [Not(flag)] * 4 + [And(flag, x != y)] * 4
    with monkeypatch.context() as mp:
        mp.setattr(be, "refute_conditional_ites", lambda f, *a, **kw: (f, "unknown", ()))
        mp.setattr(be, "solve_query", lambda *a, **kw: "unknown")
        shared = bp.prepare_shared(prover(), bases, [targets(goal)] * len(bases))
    assert not shared["canonical_proofs"] and not shared["done"]
    assert bp.close_edge(prover(), "original_fallback", Not(flag), targets(goal), shared).proved
    assert not bp.close_edge(prover(), "false_fallback", And(flag, x != y), targets(goal), shared).proved


def test_shared_pure_memo_keeps_aliases_inputs_and_ast_ids_distinct():
    a = Array("canonical_memo_array", BitVecSort(64), BitVecSort(8))
    i, j = BitVec("canonical_memo_i", 64), BitVec("canonical_memo_j", 64)
    x = BitVec("canonical_memo_x", 8)
    first = Select(Store(a, i, x), i) == x
    other = Select(Store(a, i, x), j) == x
    shared = dict(bases={}, done={}, forwarded={}, joined={})
    p = prover()
    assert bp.close_edge(p, "memo_hit", And(), targets(first), shared).proved
    gc.collect()
    assert not bp.close_edge(p, "memo_alias", And(i != j, Select(a, j) != x), targets(other), shared).proved
    for cache in (shared["forwarded"], shared["joined"]):
        alive = {term.get_id() for term in cache["alive"]}
        assert all(key in alive for key in cache if isinstance(key, int))


def test_common_preparation_obeys_the_original_deadline():
    p = prover(); p.deadline = monotonic() - 1
    x = BitVec("canonical_expired_x", 8)
    with pytest.raises(be.ProofBudgetExceeded):
        bp.prepare_shared(p, [And()] * 4, [targets(If(x == 0, x, x + 1) == x)] * 4)


@pytest.fixture(scope="module")
def native_run(tmp_path_factory):
    directory = tmp_path_factory.mktemp("canonical-native")
    options = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=3000,
                   node_seconds=300, first_pass_node_seconds=None, max_parameter_values=8,
                   max_depth=400, max_instances=2048, wall_seconds=900, summaries=False)
    result = bp.verify_parallel("tests/data/lockstep_counter_loop", options, workers=1, results_dir=directory)
    assert result.verified, result.message
    return directory, options


@pytest.mark.parametrize("mutation", ["valid", "common_deleted", "leaf_deleted", "leaf_unknown", "whole_subtree"])
def test_native_consumer_requires_every_checked_dependency(native_run, canonical_edge, tmp_path, mutation):
    directory, options = native_run
    copied = tmp_path / "native"
    shutil.copytree(directory, copied)
    for path in copied.rglob("*.pkl.z"):
        node = pickle.loads(zlib.decompress(path.read_bytes()))
        if node["edges"]:
            break
    else:
        pytest.fail("the actual native result has no boundary edges")
    edge = node["edges"][0]
    # Preserve its genuine proof; append a separately proved implication as a
    # redundant dependency to exercise the actual native consumer boundary.
    outer = replace(edge.obligation, lemmas=(*edge.obligation.lemmas, canonical_edge), required_lemmas=None)
    composition = canonical_edge
    wrapper = composition.lemmas[0]
    common = wrapper.lemmas[0]
    if mutation == "common_deleted":
        wrapper = replace(wrapper, lemmas=())
    elif mutation in ("leaf_deleted", "leaf_unknown"):
        index = next(i for i, g in enumerate(common.lemmas) if g.lemmas)
        guard = common.lemmas[index]
        leaves = guard.lemmas[1:] if mutation == "leaf_deleted" else (replace(guard.lemmas[0], answer="unknown"), *guard.lemmas[1:])
        common = replace(common, lemmas=(*common.lemmas[:index], replace(guard, lemmas=leaves), *common.lemmas[index+1:]))
        wrapper = replace(wrapper, lemmas=(common,))
    composition = replace(composition, lemmas=(wrapper,))
    outer = replace(outer, lemmas=outer.lemmas[:-1] if mutation == "whole_subtree" else (*outer.lemmas[:-1], composition))
    node = dict(node, edges=(replace(edge, obligation=bp.slim(outer)), *node["edges"][1:]))
    path.write_bytes(zlib.compress(pickle.dumps(node), 6))
    assert bp.load_stored(path.parent, node["spec"], node["contexts"], node["identity"]) is not None
    result = bp.verify_parallel("tests/data/lockstep_counter_loop", options, workers=1, results_dir=copied)
    assert result.verified == (mutation == "valid")
    if mutation != "valid":
        assert any("parallel certificate consumer rejected" in reason for reason in result.reasons)
