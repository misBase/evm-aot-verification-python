"""Observe frozen single-core jobs; all query/summary timers run on the main thread.

Run with worker.py's single-job argv, from the frozen snapshot, under run_one.py.
Instrumentation adds overhead, so these totals are not primary timing samples.
"""
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys
import time


def dag_nodes(expressions):
    from z3 import is_app
    seen, work = set(), list(expressions)
    while work:
        node = work.pop()
        key = node.get_id()
        if key in seen:
            continue
        seen.add(key)
        if is_app(node):
            work.extend(node.children())
    return len(seen)


def observed_check(check, args, kwargs, clock=time.process_time):
    started = clock()
    answer = check(*args, **kwargs)
    return answer, clock() - started


def summary_stats_info(stats):
    # The frozen runtime exposes addresses as a set; retain scalar JSON only.
    return {kind: dict(row, hit_entries=sorted(row['hit_entries'])) for kind, row in stats.items()}


def main():
    assert sys.argv[1] == 'single'
    here = Path(__file__).resolve().parent
    sys.path.insert(0, os.getcwd())
    sys.path.insert(1, str(here))
    output = Path(os.environ['PAPER_WORKER_OUT']).parent
    observer_path = output / 'observations.json'
    assert not observer_path.exists(), 'fresh observer output required'
    observations = dict(scope='diagnostic single-core observations, not primary timing samples',
        query_cpu_scope='only original solver.check; excludes DAG walk, serialization, statistics and I/O',
        phase_cpu_scope='inclusive: x86 execution contains nested summary proof work',
        observer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), queries=[], x86=[], mul_proofs=[])

    def flush():
        temporary = observer_path.with_suffix('.tmp')
        temporary.write_text(json.dumps(observations, indent=2) + '\n')
        temporary.replace(observer_path)

    spec = importlib.util.spec_from_file_location('paper_profile_worker', here / 'worker.py')
    worker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(worker)
    assert worker.source_pin(Path.cwd()) == dict(sha256=worker.EXPECTED_SOURCE_PIN, files=worker.EXPECTED_SOURCE_FILES)
    import tests.support.instruction_equivalence as harness
    from x86_64.program import X86Program
    from x86_64.summaries.mul import MulSummarySpec
    factory = harness._make_equivalence_solver
    paths = X86Program.to_z3_paths
    prove = MulSummarySpec._prove_hit

    def make_solver(case):
        solver = factory(case)
        original_check = solver.check

        def check(*args, **kwargs):
            overhead = time.process_time()
            assertions = tuple(solver.assertions())
            text = solver.to_smt2()
            row = dict(index=len(observations['queries']) + 1, state='checking',
                full_query_nodes=dag_nodes(assertions), mismatch_nodes=dag_nodes(assertions[-1:]),
                query_sha256=sha256(text.encode()).hexdigest(), answer=None, check_cpu_s=None)
            query_file = output / f"query-{row['index']:03d}.smt2"
            query_file.write_text(text)
            row['query_file'] = query_file.name
            observations['queries'].append(row)
            flush()
            row['observer_precheck_cpu_s'] = time.process_time() - overhead
            wall = time.monotonic()
            answer, cpu = observed_check(original_check, args, kwargs)
            check_wall = time.monotonic() - wall
            row.update(state='finished', answer=str(answer), check_cpu_s=cpu, check_wall_s=check_wall,
                       reason_unknown=solver.reason_unknown() if str(answer) == 'unknown' else None)
            statistics = solver.statistics()
            row['rlimit_count'] = (statistics.get_key_value('rlimit count')
                                   if 'rlimit count' in statistics.keys() else None)
            flush()
            return answer

        solver.check = check
        return solver

    def to_paths(program, *args, **kwargs):
        started = time.process_time()
        result = paths(program, *args, **kwargs)
        elapsed = time.process_time() - started
        observations['x86'].append(dict(cpu_s=elapsed,
            terminal_global_states=len(result.global_states), terminal_observations=len(result.observations),
            coverage_complete=result.coverage.complete if result.coverage is not None else None,
            summary_stats=summary_stats_info(program.last_summary_stats)))
        flush()
        return result

    def prove_hit(plugin, *args, **kwargs):
        started = time.process_time()
        before = dict(plugin.proof_stats)
        try:
            return prove(plugin, *args, **kwargs)
        finally:
            observations['mul_proofs'].append(dict(cpu_s=time.process_time() - started,
                before=before, after=dict(plugin.proof_stats)))
            flush()

    harness._make_equivalence_solver = make_solver
    X86Program.to_z3_paths = to_paths
    MulSummarySpec._prove_hit = prove_hit
    flush()
    try:
        worker.main()
    finally:
        harness._make_equivalence_solver = factory
        X86Program.to_z3_paths = paths
        MulSummarySpec._prove_hit = prove
        observations['observer_finished'] = True
        flush()


if __name__ == '__main__':
    main()
