"""Constant-insensitive proof instances in the discover-first schedule
(docs/块级实例常量去敏化方案.md §8: T3, M1-M5)."""
import time
from dataclasses import replace
from time import monotonic

import pytest

from verification import block_parallel
from verification.block_equivalence import digest
from verification.block_parallel import (build_inputs, discover, load_stored, load_worker, proof_groups,
                                         prove_instance, stored_path, verify_parallel)
from verification.block_program import BlockProgramResult
from verification.block_specialization import BlockSpecialization as S, dropped

ON = dict(gas_check="full", gas_budget=1_000_000_000, num_inputs=0, timeout_ms=3000, node_seconds=300,
          first_pass_node_seconds=None, max_parameter_values=8, max_depth=400, max_instances=2048,
          wall_seconds=900, summaries=False, constant_insensitive=True)


def counts(r):
    check, = (c for c in r.closure_checks if c["phase"] == "proof_instances")
    return check["contexts"], check["proof_instances"]


def verify_dropping_every_constant(stem):
    # A deliberately bad π: drops constants the block consumes (the counter
    # an ADD reads, a return tag a JUMP pops). π is untrusted: the result
    # must still be a sound certificate (k proves on the larger domain, or
    # fails and the group falls back to its contexts).
    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(block_parallel, "sensitive_slots", lambda block: frozenset())
        return verify_parallel(stem, ON, workers=2)


@pytest.fixture(scope="module")
def grouped():
    r = verify_dropping_every_constant("tests/data/lockstep_counter_loop")
    assert r.verified, r.message
    return r


def test_nothing_to_drop_proves_every_context(tmp_path):
    r = verify_parallel("tests/data/three_block", ON, workers=2, results_dir=tmp_path)
    assert r.verified, r.message
    contexts, instances = counts(r)
    assert contexts == instances == len(r.certificate.nodes)
    assert all(n["proof_spec"] == n["spec"] for n in r.certificate.nodes)
    # M5: the projection rule versions the store; nothing is shared with the off mode.
    store, = tmp_path.iterdir()
    assert store.name.endswith(block_parallel.PROJECTION_VERSION) and len(list(store.iterdir())) == instances


def test_one_proof_serves_several_contexts(grouped):
    contexts, instances = counts(grouped)
    assert (contexts, instances) == (3, 2)
    shared = [n for n in grouped.certificate.nodes if n["proof_spec"] != n["spec"]]
    assert shared and all(e.assumed == dropped(n["proof_spec"], n["spec"]) != () for n in shared
                          for e in n["edges"])
    proof = shared[0]["proof_spec"]
    group = [n for n in grouped.certificate.nodes if n["proof_spec"] == proof]
    assert len(group) == 2 and group[0]["theorem"] is group[1]["theorem"]


def test_return_tag_dropped_stays_sound():
    # M4: the return block's JUMP target becomes symbolic in k.
    r = verify_dropping_every_constant("tests/data/lockstep_return_loop")
    assert r.verified, r.message
    # Measured: k gets sat (a model outside the context), the group falls back to c.
    split = [n for n in r.diagnostics[6]["instances"] if n["status"] == "split"]
    assert split and all("solver=sat" in "".join(n["reasons"]) for n in split)
    assert all(n["proof_spec"] == n["spec"] for n in r.certificate.nodes)


# ---------------------------------------------------------------- M2/M3: consumer

def _mutated(r, change):
    c = r.certificate
    k = next(i for i, n in enumerate(c.nodes) if n["proof_spec"] != n["spec"])
    node = change(dict(c.nodes[k]), c)
    return replace(c, nodes=c.nodes[:k] + (node,) + c.nodes[k + 1:])


def _edges(node, **fields):
    return tuple(replace(e, **fields) for e in node["edges"])


def _rejects(r, changed):
    prover, initial = r._prover, r._initial
    original = prover._issued_program_certificate
    prover._issued_program_certificate = changed
    try:
        return not changed.valid(prover, initial)
    finally:
        prover._issued_program_certificate = original


def _with_proof(node, proof):
    node["theorem"] = replace(node["theorem"], spec=proof)
    node["proof_spec"] = proof
    return node


MUTATIONS = {
    # theorem about an instance with another MSize / depth / a conflicting constant
    "proof_msize": lambda n, c: _with_proof(n, replace(n["proof_spec"], memory_size=n["spec"].memory_size + 32)),
    "proof_depth": lambda n, c: _with_proof(n, replace(n["proof_spec"], stack_depth=n["spec"].stack_depth + 1)),
    "proof_constant_not_in_context": lambda n, c: _with_proof(
        n, replace(n["proof_spec"], stack_constants=((0, 7),))),
    "theorem_not_about_proof_spec": lambda n, c: dict(n, proof_spec=n["spec"]),
    "assumed_missing": lambda n, c: dict(n, edges=_edges(n, assumed=())),
    "assumed_wrong_value": lambda n, c: dict(n, edges=_edges(n, assumed=tuple((i, v + 1) for i, v in
                                                                              n["edges"][0].assumed))),
    "edge_missing": lambda n, c: dict(n, edges=n["edges"][1:]),
    "exits_differ_within_group": lambda n, c: dict(n, expected=(), edges=()),
    "edge_source_is_proof_spec": lambda n, c: dict(n, edges=_edges(n, source=n["proof_spec"])),
    # M3: a non-frozen instance among the H2 targets
    "target_not_frozen": lambda n, c: dict(n, edges=tuple(
        replace(e, targets=e.targets + (S(e.target_pc, 1, 0, 0, ((0, 7),)),),
                target_version=digest(e.targets + (S(e.target_pc, 1, 0, 0, ((0, 7),)),)))
        for e in n["edges"])),
    "no_proof_spec": lambda n, c: {key: v for key, v in n.items() if key != "proof_spec"},
}


@pytest.mark.parametrize("name", sorted(MUTATIONS))
def test_consumer_rejects(grouped, name):
    assert grouped.certificate.valid(grouped._prover, grouped._initial)
    assert _rejects(grouped, _mutated(grouped, MUTATIONS[name]))


def test_consumer_rejects_assumptions_on_the_entry_edge(grouped):
    c = grouped.certificate
    entry = replace(c.entry, edges=(replace(c.entry.edges[0], assumed=((0, 0),)),) + c.entry.edges[1:])
    assert _rejects(grouped, replace(c, entry=entry))


# ---------------------------------------------------------------- M1: H2 per context, in-process

@pytest.fixture(scope="module")
def return_site():
    """muti_block pc=769 (PUSH 0 SWAP1 POP JUMP 774) carries the caller's
    return tag 263 in slot 3; every frozen context of 774 requires it."""
    stem = "tests/data/muti_block"
    evm, x86, initial, verifier = build_inputs(stem, ON)
    setup = verifier._setup(evm, x86, initial, BlockProgramResult(), monotonic(), [])
    ordered, defects = discover(verifier, setup, lambda: None)
    assert not defects
    groups = proof_groups(ordered, setup.evm, True)
    assert len(groups) < len(ordered)  # the real π merges contexts here (47 -> 46)
    load_worker(stem, ON, ordered)
    k = next(s for s in groups if s.pc == 769)
    c, = groups[k]
    assert k.stack_constants == () and dropped(k, c) == ((0, 0), (3, 263))
    return k, c


def _h2(k, contexts):
    return prove_instance(k, 300, time.time() + 900, contexts)


def test_h2_closes_with_the_dropped_equalities(return_site):
    k, c = return_site
    n = _h2(k, (c,))
    assert n["proved"] and not n["reasons"], n["reasons"]
    assert n["edges"] and all(e.source == c and e.assumed == ((0, 0), (3, 263)) and e.obligation.proved
                              and e.target_pc == 774 for e in n["edges"])


def test_h2_without_the_dropped_equalities_is_not_closed(return_site):
    k, _ = return_site
    n = _h2(k, (k,))  # E_c = true
    assert n["proved"] and any("not closed into pc=774" in r for r in n["reasons"]), n["reasons"]


def test_h2_with_a_wrong_equality_is_not_closed(return_site):
    k, c = return_site
    wrong = replace(c, stack_constants=((0, 0), (3, 264)))
    n = _h2(k, (wrong,))
    assert n["proved"] and any("not closed into pc=774" in r for r in n["reasons"]), n["reasons"]


def test_h2_budget_exhaustion_is_an_open_edge_not_a_worker_error(return_site, monkeypatch):
    # Safe 588/11653 (R30): the node proved, H2 ran out of budget and the
    # exception escaped the worker, so the full-budget retry never ran.
    k, c = return_site

    def exhausted(*args, **kwargs):
        raise block_parallel.ProofBudgetExceeded("proof wall budget exhausted")
    monkeypatch.setattr(block_parallel, "close_edge", exhausted)
    n = _h2(k, (c,))
    assert n["proved"] and any("budget exhausted (solver=unknown)" in r for r in n["reasons"]), n["reasons"]
    assert block_parallel.final_status(n) == "inconclusive"


def test_context_that_is_not_a_weakening_gets_no_edges(return_site):
    k, c = return_site
    n = _h2(k, (replace(c, memory_size=c.memory_size + 32),))
    assert not n["edges"] and any("not a weakening" in r for r in n["reasons"])


# ---------------------------------------------------------------- M5: stored groups

def test_stored_group_is_reused_only_for_the_same_members(tmp_path):
    k, a, b = S(5, 2, 0, 0), S(5, 2, 0, 0, ((1, 9),)), S(5, 2, 0, 0, ((1, 8),))
    node = dict(spec=k, contexts=(a, b), identity="id", proved=True)
    stored_path(tmp_path, k, (a, b)).write_bytes(block_parallel.zlib.compress(block_parallel.pickle.dumps(node)))
    assert load_stored(tmp_path, k, (a, b), "id") == node
    assert load_stored(tmp_path, k, (a,), "id") is None  # membership changed
    assert load_stored(tmp_path, k, (a, b), "other") is None
    stored_path(tmp_path, k, (a,)).write_bytes(block_parallel.zlib.compress(block_parallel.pickle.dumps(node)))  # wrong members inside
    assert load_stored(tmp_path, k, (a,), "id") is None
    # Final failures are kept too, so a restart does not redo them.
    failed = dict(spec=a, contexts=(a,), identity="id", proved=False, status="inconclusive", reasons=("x",))
    stored_path(tmp_path, a, (a,)).write_bytes(block_parallel.zlib.compress(block_parallel.pickle.dumps(failed)))
    assert load_stored(tmp_path, a, (a,), "id") == failed
    assert block_parallel.final_status(failed) == "inconclusive"
    assert block_parallel.final_status(dict(node, reasons=())) == "proved"


@pytest.mark.slow
def test_muti_block_verifies_with_fewer_proofs():
    # ~11 min with 2 workers (measured 2026-10-03: 47 contexts, 46 proofs).
    r = verify_parallel("tests/data/muti_block", ON, workers=2)
    assert r.verified, r.message
    contexts, instances = counts(r)
    assert instances < contexts == len(r.certificate.nodes)
