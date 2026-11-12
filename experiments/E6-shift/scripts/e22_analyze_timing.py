"""Audit the fixed timing cohort independently of the separate diagnostics."""
import argparse
from collections import Counter
from hashlib import sha256
import json
import math
from pathlib import Path
from statistics import median


def exact_wall(guard):
    return guard['exit_observed_wall_seconds'] + guard['cleanup_wall_seconds']


def analyze(directory, prepared_path):
    prepared = json.loads(prepared_path.read_bytes())
    summary = json.loads((directory / 'SUMMARY.json').read_bytes())
    protocol = prepared['protocol']
    assert protocol['timeout_seconds'] == 600 and protocol['memory_tree_mib'] == 6000
    assert protocol['timing_owned_observer'] is False
    assert prepared['source_pin'] == dict(sha256='d21332757dfd422a5fbf4972c17684705671b010a75dcc4532da3f500ece7709', files=113)
    assert summary['protocol'] == protocol
    timing_points = [p for p in prepared['points'] if p['phase'] == 'timing']
    points = {p['name']: p for p in timing_points}
    assert len(points) == len(timing_points) == 48
    records = {r['name']: r for r in summary['rows'] if r['name'] in points}
    assert len(records) == sum(r['name'] in points for r in summary['rows']) == 48
    receipts, groups, counts, skipped = {}, [], Counter(), []
    for k in range(1, 9):
        for enabled in (False, True):
            chosen = sorted((p for p in points.values() if p['k'] == k and p['shift_summary'] is enabled),
                            key=lambda p: p['rep'])
            assert [p['rep'] for p in chosen] == [1, 2, 3]
            first_path = directory / (chosen[0]['name'] + '.json')
            first = json.loads(first_path.read_bytes())
            required = 1 if exact_wall(first) > 300 else 3
            trials = []
            for point in chosen:
                record = records[point['name']]
                if point['rep'] > required:
                    assert record['executed'] is False and record['result'] == 'SKIPPED_PROTOCOL'
                    assert record['reason'] == 'R1_GUARD_WALL_GT300'
                    assert record['r1_sha256'] == sha256(first_path.read_bytes()).hexdigest()
                    assert record['r1_wall_exact_seconds'] == exact_wall(first)
                    assert record['r1_wall_basis'] == 'exit_observed_wall_seconds+cleanup_wall_seconds'
                    assert record['r1_wall_seconds'] == first['wall_seconds']
                    assert not (directory / (point['name'] + '.json')).exists()
                    skipped.append(point['name'])
                    continue
                assert record['executed'] is True and record['supervisor_returncode'] == 0
                path = directory / (point['name'] + '.json')
                guard = json.loads(path.read_bytes())
                assert guard['result'] == record['result']
                assert guard['timeout_s'] == 600 and guard['memory_mb'] == 6000
                assert guard['process_group_gone'] is True and guard['monitor_error'] is None
                assert guard['command'][-1] == point['name']
                cpu = guard['cpu_user_seconds'] + guard['cpu_sys_seconds']
                wall = exact_wall(guard)
                assert all(math.isfinite(v) and v >= 0 for v in (cpu, wall))
                worker = guard.get('worker_payload')
                if worker:
                    assert worker['point'] == point and worker['pins_after'] == prepared['pins']
                    assert worker['source_after'] == prepared['source_pin']
                    assert worker['observer_enabled'] is False and worker['events'] is None
                    assert worker['counterexample'] is False
                    assert worker['state_contract'] == dict(symbolic_gas=False, gas_budget=10**9,
                        host_gas_uf_enabled=False, calldata_size_bytes=512,
                        assume_calldata_offset_no_overflow=False, abstract_calldataload_words=False)
                    effective = worker['effective']
                    assert all(effective[key] == value for key, value in dict(max_depth=400,
                        query_cap_ms=300000, gas_check='off', path_pair_workers=1, enable_merge=False,
                        reachability_timeout_ms=250, x86_base_addr=4096).items())
                    config = worker['summary_config']
                    kinds = ('calldataload', 'copy_loop', 'mul', 'div', 'memgas', 'sdiv', 'smod')
                    modes = dict.fromkeys(kinds, 'fallback')
                    if enabled:
                        modes['shift'] = 'fallback'
                    assert config['builtin_modes'] == modes
                    assert config['prove_mul_hits'] is config['prove_div_hits'] is True
                    if guard['result'] == 'VERIFIED':
                        assert worker['verified'] is True and worker['actual_verified'] is True
                        assert worker['truncated'] == [] and guard['returncode'] == 0
                assert guard['result'] in ('VERIFIED', 'TO', 'OOM', 'BOUND', 'UNK', 'N/A')
                assert guard['result'] != 'VERIFIED' or worker is not None
                counts[guard['result']] += 1
                receipts[str(path)] = sha256(path.read_bytes()).hexdigest()
                trials.append(dict(repeat=point['rep'], result=guard['result'], cpu_s=cpu,
                    wall_s=wall, cpu_lower_bound=guard['cpu_lower_bound'], peak_rss_mib=guard['peak_rss_mb'],
                    raw_path=str(path), raw_sha256=receipts[str(path)]))
            completed = all(t['result'] == 'VERIFIED' and not t['cpu_lower_bound'] for t in trials)
            assert len(trials) == required
            groups.append(dict(k=k, shift_summary=enabled, required_repeats=required, trials=trials,
                completion_median_cpu_s=median(t['cpu_s'] for t in trials) if completed else None,
                completion_cpu_range_s=[min(t['cpu_s'] for t in trials), max(t['cpu_s'] for t in trials)] if completed else None,
                completion_median_wall_s=median(t['wall_s'] for t in trials) if completed else None,
                interpretation='completed-proof time only when every prescribed trial completes; failures retain resource consumption'))
    assert sum(counts.values()) + len(skipped) == 48
    return dict(experiment='E2.2', phase='timing', native_analysis_calls=0, protocol=protocol,
        source=prepared['source_pin'], executed=sum(counts.values()), skipped=len(skipped),
        outcomes=dict(counts), groups=groups, skipped_names=skipped,
        prepared_sha256=sha256(prepared_path.read_bytes()).hexdigest(),
        summary_sha256=sha256((directory / 'SUMMARY.json').read_bytes()).hexdigest(),
        guard_receipts_sha256=receipts, analysis_source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        excluded_diagnostic_attempts=[r for r in summary['rows'] if r['name'] not in points],
        limitations=['Timing phase is audited separately from the failed first diagnostic parser attempt',
            'TO resource CPU is not a completed proof time; no speedup ratio from censored trials',
            'Branch/path/formula explanations require the independent diagnostic cohort',
            'Only the shift summary changes; all operands are the declared fixed512-byte calldata domain'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--prepared', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert not args.out.exists(), 'fresh analysis output required'
    result = analyze(args.directory, args.prepared)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:result[k] for k in ('executed', 'skipped', 'outcomes')}))
