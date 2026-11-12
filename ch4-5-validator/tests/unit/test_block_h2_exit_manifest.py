"""The local theorem pins required H2 exits through native storage and consumption."""
from dataclasses import replace
import pickle
import shutil
import zlib

import pytest

import verification.block_parallel as bp


@pytest.fixture(scope='module')
def genuine_run(tmp_path_factory):
    directory = tmp_path_factory.mktemp('h2-exit-manifest')
    options = dict(gas_check='full', gas_budget=1_000_000_000, num_inputs=0,
                   timeout_ms=3000, node_seconds=300, first_pass_node_seconds=None,
                   max_parameter_values=8, max_depth=400, max_instances=2048,
                   wall_seconds=900, summaries=False)
    result = bp.verify_parallel('tests/data/lockstep_counter_loop', options,
                                workers=1, results_dir=directory)
    assert result.verified
    assert all(n['theorem'].cutpoint_manifest is not None for n in result.certificate.nodes)
    return directory, options, tuple({s.pc for s in result.certificate.specializations})


@pytest.mark.parametrize('mutation', ['valid', 'edges', 'expected', 'both', 'one_pair',
                                     'duplicate', 'negative', 'outside', 'bool_index',
                                     'wrong_pc', 'wrong_registered_pc', 'legacy'])
def test_native_consumer_requires_the_local_exit_manifest(genuine_run, tmp_path, mutation):
    directory, options, pcs = genuine_run
    store = tmp_path / 'results'
    shutil.copytree(directory, store)
    changed = 0
    for path in store.rglob('*.pkl.z'):
        node = pickle.loads(zlib.decompress(path.read_bytes()))
        if not node['edges']:
            continue
        manifest = node['theorem'].cutpoint_manifest
        assert manifest
        i, j, pc = manifest[0]
        if mutation in ('edges', 'both'):
            node['edges'] = ()
        if mutation in ('expected', 'both'):
            node['expected'] = ()
        if mutation == 'one_pair':
            node['expected'], node['edges'] = node['expected'][1:], node['edges'][1:]
        elif mutation == 'duplicate':
            manifest = (*manifest, manifest[0])
        elif mutation == 'negative':
            manifest = ((-1, j, pc), *manifest[1:])
        elif mutation == 'outside':
            manifest = ((node['theorem'].evm_count, j, pc), *manifest[1:])
        elif mutation == 'bool_index':
            manifest = ((False, j, pc), *manifest[1:])
        elif mutation == 'wrong_pc':
            manifest = ((i, j, pc + 1), *manifest[1:])
        elif mutation == 'wrong_registered_pc':
            manifest = ((i, j, next(other for other in pcs if other != pc)), *manifest[1:])
        elif mutation == 'legacy':
            manifest = None
        node['theorem'] = replace(node['theorem'], cutpoint_manifest=manifest)
        path.write_bytes(zlib.compress(pickle.dumps(node)))
        changed += 1
    assert changed
    result = bp.verify_parallel('tests/data/lockstep_counter_loop', options,
                                workers=1, results_dir=store)
    assert result.verified == (mutation == 'valid')


def test_terminal_outcome_needs_no_h2_edges(tmp_path):
    options = dict(gas_check='full', gas_budget=1_000_000_000, num_inputs=0,
                   timeout_ms=3000, node_seconds=300, first_pass_node_seconds=None,
                   max_parameter_values=8, max_depth=400, max_instances=2048,
                   wall_seconds=900, summaries=False)
    result = bp.verify_parallel('tests/data/mstore_return', options,
                                workers=1, results_dir=tmp_path)
    assert result.verified
    terminal = [n for n in result.certificate.nodes if n['theorem'].cutpoint_manifest == ()]
    assert terminal and all(n['expected'] == () and n['edges'] == () for n in terminal)
