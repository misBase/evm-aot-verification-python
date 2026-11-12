"""Aggregate explicitly named repetitions without turning failures into times."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import statistics

from source_pin import SHA256 as _PIN_SHA, FILES as _PIN_FILES  # noqa: E402
PIN = {'sha256': _PIN_SHA, 'files': _PIN_FILES}
CONFIGS = {'V0', 'V1', 'V2', 'V3', 'V2-B1B2', 'V2-B3', 'V2-B4',
           'V2-B4a', 'V2-B4b', 'V2-B4c', 'V2-B4d'}
SINGLE_EPOCH = '2026-11-05-v2-single-cfg-coverage'
SINGLE_WORKER_SHA = 'a3285ca3401571d6de321e14aa4cea171855ae09efc697bebcb26a599cf27a5e'
SINGLE_GATE_SHA = '5254f77b97b102a4fb4662c7a30aa0048a3639eb34502358fc33c42fac2097a6'
SINGLE_MERGED_ARMS = {'V0', 'V1', 'V2-B1B2'}


def validate_single_verified(record, config):
    """Admit only the reviewed single-core wiring and its actual coverage."""
    assert record['config_epoch'] == SINGLE_EPOCH, 'unreviewed single epoch'
    hashes = record['harness_sha256']
    assert hashes['worker.py'] == SINGLE_WORKER_SHA, 'unreviewed single worker'
    assert hashes['single_cfg_merge.py'] == SINGLE_GATE_SHA, 'unreviewed single gate'
    assert record['counterexample'] is False, 'single VERIFIED has a counterexample'
    core, effective = record['single_core'], record['effective']
    mode, terminal = core['case_execution_mode'], core['terminal_paths']
    merged = config in SINGLE_MERGED_ARMS
    assert core['merged_helper_installed'] is merged, 'single merge arm mismatch'
    assert effective['case_execution_mode'] == mode
    assert type(terminal) is bool and effective['terminal_paths'] is terminal
    if merged:
        assert terminal is False, 'merged arm used terminal-path comparison'
    calls = core['core_calls']
    assert type(calls) is list
    if mode == 'linear':
        assert core['coverage_applicable'] is False and core['coverage_complete'] is None
        assert calls == [] and core['cfg_merge_actual'] is None
        assert effective['cfg_merge_actual'] is None and effective['core_coverage_complete'] is None
        return
    assert mode == 'cfg', 'unknown single-core execution mode'
    assert core['coverage_applicable'] is True and core['coverage_complete'] is True
    assert core['coverage_status'] == 'complete' and calls, 'missing complete core calls'
    assert core['cfg_merge_actual'] is merged and effective['cfg_merge_actual'] is merged
    assert effective['core_coverage_complete'] is True
    for call in calls:
        assert call['coverage_complete'] is True
        assert type(call['terminal_states']) is int and call['terminal_states'] > 0
        assert call['enable_merge'] is merged, 'wrong actual CFG merge option'
        assert call['merge_state'] is (not terminal), 'wrong actual terminal merge option'
        assert call['helper'] == ('terminal_paths' if terminal else 'merged_state')


def summarize(samples):
    grouped = defaultdict(list)
    hosts = defaultdict(set)
    for sample in samples:
        grouped[tuple(sample[k] for k in ('family', 'target', 'config'))].append(sample)
        if sample['host'] is not None:
            hosts[sample['family']].add(sample['host'])
    assert all(len(values) == 1 for values in hosts.values()), 'mixed machines within a dataset'
    groups = []
    for key, rows in sorted(grouped.items()):
        assert len({row['repeat'] for row in rows}) == len(rows), ('duplicate repetition', key)
        assert len({row['host'] for row in rows}) == 1, ('mixed machines', key)
        identities = {row['identity'] for row in rows if row.get('identity') is not None}
        assert len(identities) <= 1, ('changed source, input or configuration', key)
        rows.sort(key=lambda row: row['repeat'])
        first = next((row for row in rows if row['repeat'] == 1), None)
        assert first is not None, ('missing first repetition', key)
        excluded = bool(first.get('input_missing_pair') or first.get('alias_of') is not None
                        or first.get('raw_status') == 'INPUT_MISSING_PAIR'
                        or (first['result'] in ('N/A', 'UNSUPPORTED')
                            and first.get('raw_status') == 'UNSUPPORTED'))
        elapsed = first.get('elapsed_seconds')
        if elapsed is None:
            elapsed = first['wall_seconds']
        required = (1 if excluded or key[0] == 'fn' else 2 if key[0] == 'whole' else
                    1 if elapsed is not None and elapsed > 300 else 3)
        assert len(rows) <= required, ('unexpected extra samples', key, len(rows), required)
        assert {row['repeat'] for row in rows} <= set(range(1, required + 1)), ('unexpected repeat label', key)
        statuses = Counter(row['result'] for row in rows)
        complete = len(rows) == required
        comparable = (complete and not excluded and len(statuses) == 1
                      and first['result'] in ('VERIFIED', 'BOUNDED')
                      and (key[0] != 'single' or first['result'] == 'VERIFIED')
                      and all(not row['cpu_lower_bound'] and row['cpu_seconds'] is not None
                              and row['wall_seconds'] is not None for row in rows))
        groups.append(dict(family=key[0], target=key[1], config=key[2], host=first['host'],
            sample_count=len(rows), required_samples=required, repetitions_complete=complete,
            statuses=dict(statuses), counterexample_count=sum(row['counterexample'] for row in rows),
            excluded_from_independent_samples=excluded,
            median_cpu_seconds=statistics.median(row['cpu_seconds'] for row in rows) if comparable else None,
            median_wall_seconds=statistics.median(row['wall_seconds'] for row in rows) if comparable else None,
            observed_cpu_seconds=[row['cpu_seconds'] for row in rows],
            resource_cpu_seconds=sum(row['cpu_seconds'] for row in rows if row['cpu_seconds'] is not None),
            resource_cpu_missing_count=sum(row['cpu_seconds'] is None for row in rows),
            median_scope='completed samples only when all prescribed repetitions agree and are complete',
            samples=rows))
    return groups


def load_run(directory, repeat):
    rows = []
    for path in sorted(directory.glob('*.json')):
        if path.name.endswith(('.worker.json', '.reach.json', '.process.json')):
            continue
        parts = path.stem.split('__')
        if len(parts) != 3 or parts[0] not in ('single', 'prog', 'fn', 'whole') or parts[2] not in CONFIGS:
            continue
        record = json.loads(path.read_bytes())
        status = record['result']
        if record.get('source_before') is not None:
            assert record['source_before'] == PIN, ('wrong source', path)
        if parts[0] == 'single' and status == 'VERIFIED':
            try:
                validate_single_verified(record, parts[2])
            except (AssertionError, KeyError, TypeError) as error:
                raise AssertionError(f'unqualified single VERIFIED: {path}: {error}') from error
        if status in ('VERIFIED', 'BOUNDED'):
            assert record.get('source_after') == PIN and record['returncode'] == 0
            assert record['process_group_gone'] is True and record.get('verified') is True
            assert record.get('monitor_error') is None
            assert bool(record.get('truncated')) == (status == 'BOUNDED'), ('coverage/status mismatch', path)
            if parts[2] == 'V3':
                assert record['cli_returncode'] == 0 and record['lockstep_status'] == 'verified'
                assert record['closure']['entry_certificates'] == 1
        cpu = (sum(record[key] for key in ('cpu_user_seconds', 'cpu_sys_seconds'))
               if all(type(record.get(key)) in (int, float) for key in
                      ('cpu_user_seconds', 'cpu_sys_seconds')) else record.get('cpu_seconds'))
        elapsed = (record['exit_observed_wall_seconds'] + record['cleanup_wall_seconds']
                   if all(type(record.get(key)) in (int, float) for key in
                          ('exit_observed_wall_seconds', 'cleanup_wall_seconds')) else None)
        rows.append(dict(family=parts[0], target=parts[1], config=parts[2], repeat=repeat,
            host=record.get('host'), result=status, counterexample=bool(record.get('counterexample')),
            cpu_seconds=cpu, wall_seconds=elapsed if elapsed is not None else record.get('wall_seconds'),
            peak_rss_mb=record.get('peak_rss_mb'), cpu_lower_bound=record.get('cpu_lower_bound', True),
            alias_of=record.get('alias_of'), input_missing_pair=record.get('input_missing_pair'),
            raw_status=record.get('raw_status'), raw_path=str(path),
            config_epoch=record.get('config_epoch'), single_core=record.get('single_core'),
            harness_sha256=record.get('harness_sha256'), effective=record.get('effective'),
            elapsed_seconds=elapsed,
            raw_sha256=sha256(path.read_bytes()).hexdigest(),
            identity=json.dumps({**{key: record.get(key) for key in ('source_before', 'harness_sha256',
                'input_pair_sha256', 'config_epoch')}, 'effective': {key: value
                for key, value in record.get('effective', {}).items()
                if key not in ('wall_seconds', 'cfg_merge_actual', 'core_coverage_complete')}}, sort_keys=True)
                if record.get('source_before') is not None else None,
            unknown_reasons=record.get('unknown_reasons'), message=record.get('message')))
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', action='append', required=True, help='REPEAT=flat result directory')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert not args.out.exists(), 'fresh summary path required'
    samples = []
    for text in args.run:
        repeat, directory = text.split('=', 1)
        assert int(repeat) >= 1
        samples.extend(load_run(Path(directory), int(repeat)))
    assert samples, 'no experiment records found'
    groups = summarize(samples)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(dict(samples=len(samples), groups=groups), ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(dict(samples=len(samples), groups=len(groups),
        repetitions_complete=sum(group['repetitions_complete'] for group in groups))))


if __name__ == '__main__':
    main()
