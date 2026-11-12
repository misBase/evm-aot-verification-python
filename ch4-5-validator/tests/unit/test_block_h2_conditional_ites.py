"""Edge-local conditional proofs survive the actual native and parallel consumers."""
from dataclasses import replace
import gzip
from pathlib import Path
import pickle
import shutil
import zlib

import pytest
from z3 import And, BitVecs, Bool, If, Not, parse_smt2_string

import verification.block_equivalence as be
import verification.block_parallel as bp
from verification.cutpoint_relation import RelationGoal


@pytest.fixture(autouse=True)
def no_cache(monkeypatch):
    monkeypatch.delenv('BLOCK_PROOF_CACHE', raising=False)
    monkeypatch.delenv('BLOCK_PAIR_WORKERS', raising=False)


def edge_parts(label, positive=True):
    x, y = BitVecs(f'h2ci_{label}_x h2ci_{label}_y', 8)
    flag = Bool(f'h2ci_{label}_flag')
    base = Not(flag) if positive else And(flag, x == 7, y == 9)
    return base, If(flag, y, x) == x


@pytest.fixture
def conditional_edge():
    base, goal = edge_parts('checked')
    record = bp.close_edge(be.BlockEquivalenceProver([], [], {}, timeout_ms=3000),
                           'H2_conditional', base, [('target', (RelationGoal('gas', goal),))])
    assert record.proved and record.required_lemmas
    assert record.lemmas[0].name == 'conditional_ites'
    assert record.lemmas[0].required_lemmas
    return record


def test_h2_keeps_checked_conditional_dependency_chain(conditional_edge):
    assert conditional_edge.proved


@pytest.mark.parametrize('answer', ['sat', 'unknown'])
def test_an_undecided_conditional_attempt_uses_the_original_full_check(monkeypatch, answer):
    base, goal = edge_parts(answer)
    monkeypatch.setattr(be, 'refute_conditional_ites', lambda f, *a, **kw: (f, answer, ()))
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    original, checked = prover._check_all, []

    def ordinary(jobs, records):
        jobs = list(jobs)
        checked.extend(jobs)
        yield from original(jobs, records)

    monkeypatch.setattr(prover, '_check_all', ordinary)
    record = bp.close_edge(prover, 'H2_fallback', base, [('target', (RelationGoal('gas', goal),))])
    assert record.proved and checked and checked[0][1].eq(And(base, Not(goal)))
    assert not any(r.name == 'conditional_ites' for r in record.lemmas)


def test_a_false_conditional_edge_is_never_proved():
    base, goal = edge_parts('false', positive=False)
    assert be.solve_query(And(base, Not(goal)), 1000) == 'sat'
    record = bp.close_edge(be.BlockEquivalenceProver([], [], {}, timeout_ms=1000),
                           'H2_false', base, [('target', (RelationGoal('gas', goal),))])
    assert not record.proved


def test_conditional_edge_evidence_is_not_shared_under_a_different_base():
    base, goal = edge_parts('sibling')
    targets = [('target', (RelationGoal('gas', goal),))]
    shared = dict(bases={goal.get_id(): And()}, done={})
    prover = be.BlockEquivalenceProver([], [], {}, timeout_ms=1000)
    assert bp.close_edge(prover, 'H2_true', base, targets, shared).proved
    assert not shared['done']
    assert not bp.close_edge(prover, 'H2_other', Not(base), targets, shared).proved


def test_real_safe_capture_closes_through_the_forwarded_edge_route():
    path = Path(__file__).with_name('data') / 'h2_22918_conditional_ite.smt2.gz'
    formula = And(*parse_smt2_string(gzip.decompress(path.read_bytes()).decode()))
    while formula.num_args() == 1:
        formula = formula.arg(0)
    base, negative = And(*formula.children()[:-1]), formula.arg(formula.num_args()-1)
    assert negative.decl().name() == 'not'
    record = bp.close_edge(be.BlockEquivalenceProver([], [], {}, timeout_ms=3000),
                           'H2_safe_capture', base, [('target', (RelationGoal('gas', negative.arg(0)),))])
    assert record.proved and record.required_lemmas
    assert any(r.name == 'conditional_ites' for r in record.lemmas)


@pytest.fixture(scope='module')
def complete_native_run(tmp_path_factory):
    directory = tmp_path_factory.mktemp('conditional-native')
    options = dict(gas_check='full', gas_budget=1_000_000_000, num_inputs=0, timeout_ms=3000,
                   node_seconds=300, first_pass_node_seconds=None, max_parameter_values=8,
                   max_depth=400, max_instances=2048, wall_seconds=900, summaries=False)
    result = bp.verify_parallel('tests/data/lockstep_counter_loop', options, workers=1, results_dir=directory)
    assert result.verified
    return directory, options


@pytest.mark.parametrize('mutation', ['valid', 'guard_one', 'guard_all', 'root_one', 'root_all',
                                      'subtree', 'wrapper_all', 'broken_guard'])
def test_native_reuse_then_parallel_consumer_checks_all_dependencies(
        complete_native_run, conditional_edge, tmp_path, mutation):
    directory, options = complete_native_run
    results = tmp_path / 'results'
    shutil.copytree(directory, results)
    for path in results.rglob('*.pkl.z'):
        node = pickle.loads(zlib.decompress(path.read_bytes()))
        if node['edges']:
            break
    else:
        pytest.fail('genuine counter-loop store has no edge')
    edge = node['edges'][0]
    # Keep the genuine edge predicate and proof; append a separately proved
    # redundant lemma to test the new chain through native serialization.
    wrapper = replace(edge.obligation, lemmas=(*edge.obligation.lemmas, conditional_edge), required_lemmas=None)
    composition = wrapper.lemmas[-1]
    root = composition.lemmas[0]
    if mutation in ('guard_one', 'guard_all', 'broken_guard'):
        i = next(i for i, r in enumerate(root.lemmas) if r.required_lemmas)
        guard = root.lemmas[i]
        assert guard.lemmas
        leaves = ((replace(guard.lemmas[0], answer='unknown'), *guard.lemmas[1:])
                  if mutation == 'broken_guard' else guard.lemmas[1:] if mutation == 'guard_one' else ())
        root = replace(root, lemmas=(*root.lemmas[:i], replace(guard, lemmas=leaves), *root.lemmas[i+1:]))
    elif mutation in ('root_one', 'root_all'):
        root = replace(root, lemmas=root.lemmas[1:] if mutation == 'root_one' else ())
    composition = replace(composition, lemmas=(root,))
    if mutation == 'subtree':
        wrapper = replace(wrapper, lemmas=wrapper.lemmas[:-1])
    elif mutation == 'wrapper_all':
        wrapper = replace(wrapper, lemmas=())
    else:
        wrapper = replace(wrapper, lemmas=(*wrapper.lemmas[:-1], composition))
    node = dict(node, edges=(replace(edge, obligation=bp.slim(wrapper)), *node['edges'][1:]))
    path.write_bytes(zlib.compress(pickle.dumps(node), 6))
    loaded = bp.load_stored(path.parent, node['spec'], node['contexts'], node['identity'])
    assert loaded is not None and loaded['edges'][0].obligation.proved == (mutation == 'valid')
    result = bp.verify_parallel('tests/data/lockstep_counter_loop', options, workers=1, results_dir=results)
    assert result.verified == (mutation == 'valid')
    if mutation == 'valid':
        assert any(n['pid'] == node['pid'] for n in result.certificate.nodes)
    else:
        assert any('parallel certificate consumer rejected' in r for r in result.reasons)
