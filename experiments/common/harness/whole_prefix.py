"""One-side whole-program candidate-terminal prefixes, never a proof/admission.

Run each side as a fresh 1800s/2000MiB job from the pinned snapshot, with the
original 18-file harness supplied by --harness-dir. Default import is stdlib-only.
No extra feasibility probes are made beyond reach.py's original initial SAT test.
"""
import argparse
from contextlib import contextmanager
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys
import time

HELPER_HASHES = {
    'reach.py': '655fc816f3c7e9ff09c9e4828bc9adf2320ea89f3e6602c2f3e87d486b5f3a59',
    'slices.py': 'e440bb47fce742db54136e8fe040536d0b83d8e1f8e3cadca005da390765824f',
}
from source_pin import SHA256 as _PIN_SHA, FILES as _PIN_FILES  # noqa: E402
MODEL_PIN = {'sha256': _PIN_SHA, 'files': _PIN_FILES}
SCOPE = 'append-only terminal candidate records and executed-block visits; not distinct feasible paths, completeness or admission'


def atomic_json(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('x') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    temporary.replace(path)


def bind_output_cache(output, checkpoint, environment):
    """Bind the guard's payload and a unique fresh cache before model imports."""
    output, checkpoint = Path(output), Path(checkpoint)
    if output.exists() or output.is_symlink():
        raise ValueError('fresh output path required')
    if output.resolve() == checkpoint.resolve():
        raise ValueError('output and progress checkpoint must be distinct')
    guard_output = environment.get('PAPER_WORKER_OUT')
    if guard_output is not None and Path(guard_output).resolve() != output.resolve():
        raise ValueError('output must match PAPER_WORKER_OUT')
    cache = output.resolve().with_name(output.name + '.proof-cache.sqlite')
    if any(Path(str(cache) + suffix).exists() or Path(str(cache) + suffix).is_symlink()
           for suffix in ('', '-wal', '-shm')):
        raise ValueError('fresh per-job proof cache required')
    output.parent.mkdir(parents=True, exist_ok=True)
    environment['BLOCK_PROOF_CACHE'] = str(cache)
    return cache


def runtime_identity():
    if sys.version_info[:2] != (3, 13):  # paper runs: 3.13.7
        raise ValueError('whole-prefix requires Python 3.13.x')
    import z3
    version = z3.get_version_string()
    if version != '4.15.4':
        raise ValueError('whole-prefix requires Z3 4.15.4')
    return dict(python_executable=sys.executable, python_version=sys.version, z3_version=version)


class PrefixJournal:
    """Primitive checkpoint only; no state, AST or solver object is retained."""
    def __init__(self, path, identity, interval=1.0, clock=time.monotonic):
        self.path, self.identity = Path(path), json.loads(json.dumps(identity))
        if self.path.exists() or self.path.is_symlink():
            raise ValueError('fresh checkpoint path required')
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.interval, self.clock = interval, clock
        self.seq, self.last_write, self.count = 0, float('-inf'), 0
        self.visited = set()

    def write(self, count, *, pc=None, force=False):
        if type(count) is not int or count < self.count:
            raise ValueError('candidate terminal count decreased or is malformed')
        self.count = count
        if pc is not None:
            if type(pc) is not int:
                raise ValueError('visited PC must be an integer')
            self.visited.add(pc)
        now = self.clock()
        if not force and now - self.last_write < self.interval:
            return
        self.seq += 1
        atomic_json(self.path, dict(self.identity, seq=self.seq, observed_monotonic=now,
            observed_epoch=time.time(), pid=os.getpid(), pgid=os.getpgrp(), terminal_candidate_lower_bound=self.count,
            visited_block_pcs=sorted(self.visited), complete=False,
            requires_guard_postcheck=True, scope=SCOPE))
        self.last_write = now


@contextmanager
def observe_primary(primary, executor_type, side, journal):
    """Bind only execute's exact program-caller code AND caller-local self."""
    program_method = primary._execute_paths if side == 'evm' else primary.to_z3_paths
    caller_code = program_method.__func__.__code__
    execute, step = executor_type.execute, executor_type.execute_state
    outer, final_list = None, None
    metadata = {'execute_calls': 0, 'normal_execute_return': False}

    def sample(executor, *, state=None, force=False):
        if executor.final_states is not final_list:
            raise ValueError('outer final_states container changed')
        node = state.node if state is not None else None
        pc = (node.block.pc if side == 'evm' else node.address) if node is not None else None
        journal.write(len(final_list), pc=pc, force=force)

    def observed_execute(executor, *args, **kwargs):
        nonlocal outer, final_list
        frame = sys._getframe(1)
        selected = frame.f_code is caller_code and frame.f_locals.get('self') is primary
        del frame
        if not selected:
            return execute(executor, *args, **kwargs)
        if outer is not None or type(executor.final_states) is not list or len(executor.final_states) != 0:
            raise ValueError('expected one fresh outer executor')
        outer, final_list = executor, executor.final_states
        metadata.update(execute_calls=1, executor_identity=id(executor))
        journal.identity.update(primary_program_identity=id(primary), primary_executor_identity=id(executor))
        sample(executor, force=True)
        result = execute(executor, *args, **kwargs)
        sample(executor, force=True)
        metadata['normal_execute_return'] = True
        return result

    def observed_step(executor, *args, **kwargs):
        if executor is not outer:
            return step(executor, *args, **kwargs)
        state = args[0] if args else kwargs['global_state']
        sample(executor, state=state)
        result = step(executor, *args, **kwargs)
        sample(executor)
        return result

    executor_type.execute, executor_type.execute_state = observed_execute, observed_step
    try:
        yield metadata
        if metadata['execute_calls'] != 1:
            raise ValueError('no exact primary executor observation')
    finally:
        executor_type.execute, executor_type.execute_state = execute, step


def load_helpers(directory):
    directory = Path(directory).resolve()
    for name, digest in HELPER_HASHES.items():
        if sha256((directory / name).read_bytes()).hexdigest() != digest:
            raise ValueError('original reach/slices bytes required')
    spec = importlib.util.spec_from_file_location('_paper_prefix_reach', directory / 'reach.py')
    reach = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reach)
    slices = sys.modules['slices']
    if Path(slices.__file__).resolve() != directory / 'slices.py':
        raise ValueError('unexpected cached slices module; use a fresh worker')
    return reach, slices


def collect(args, payload, journal):
    from z3 import And, SolverFor
    from evm_ir.cfg_executor import SymbolicExecutor
    from evm_ir.json_parser import load_ir_from_json
    from evm_ir.program import EVMProgram
    from state.smt_state import SMTState
    from x86_64.cfg_state import z3_memory_cap

    profile = payload['analysis_config']
    state = SMTState.create_initial_state(symbolic_gas=profile['symbolic_gas'],
        gas_budget=profile['gas_budget'], calldata_size_max_bytes=(1 << 63) - 1)
    for name in ('host_gas_uf_enabled', 'assume_calldata_offset_no_overflow', 'abstract_calldataload_words'):
        setattr(state, name, profile[name])
    solver = SolverFor('QF_AUFBV')
    solver.set(timeout=1000)
    with z3_memory_cap(256):
        solver.add(And(*(state.assumptions or [])))
        answer = str(solver.check())
    payload['domain'] = dict(answer=answer, timeout_ms=1000,
        reason_unknown=solver.reason_unknown() if answer == 'unknown' else None)
    journal.identity['domain'] = dict(payload['domain'])
    if answer != 'sat':
        return
    evm = EVMProgram(load_ir_from_json(args.stem + '.json'))
    if args.side == 'evm':
        primary, executor = evm, SymbolicExecutor
    else:
        from verification.call_site_mapping import build_call_site_mapping
        from x86_64.cfg_executor import X86SymbolicExecutor
        from x86_64.program import X86Program
        from x86_64.summaries import X86SummaryConfig
        primary = X86Program.from_hex(Path(args.stem + '.hex').read_text().strip(),
                                      base_addr=profile['x86_base_addr'])
        executor = X86SymbolicExecutor
        summary = profile['x86_summary']
        summary_config = X86SummaryConfig.enabled(**summary['builtin_modes'],
            **{k: v for k, v in summary.items() if k != 'builtin_modes'})
        mapping = build_call_site_mapping(evm, primary)
    with observe_primary(primary, executor, args.side, journal) as observed:
        if args.side == 'evm':
            finals, coverage, _ = primary._execute_paths(state.copy(), max_depth=100000)
            terminal_count = len(finals)
        else:
            paths = primary.to_z3_paths(state.copy(), max_depth=100000,
                enable_merge=profile['x86_merge'], reachability_timeout_ms=profile['x86_reachability_timeout_ms'],
                call_site_mapping=mapping, summary_config=summary_config)
            coverage, terminal_count = paths.coverage, len(paths.observations)
    # Only a normal top-level program return may expose the real certificate.
    payload.update(primary_observation=observed, top_level_returned=True,
        metrics=dict(terminal_candidate_records=journal.count, terminal_observations=terminal_count,
            visited_block_pcs=sorted(journal.visited), coverage_complete=coverage.complete if coverage else False,
            coverage_reason=coverage.reason if coverage else 'missing coverage',
            coverage_source=coverage.source if coverage else None,
            coverage_details=dict(coverage.details) if coverage else {}))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stem')
    parser.add_argument('--side', choices=('evm', 'x86'), required=True)
    parser.add_argument('--harness-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--checkpoint', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=os.environ.get('PAPER_WORKER_OUT'))
    parser.add_argument('--max-depth', type=int, choices=(100000,), default=100000)
    parser.add_argument('--gas', choices=('off',), default='off')
    args = parser.parse_args(argv)
    if args.output is None:
        parser.error('output or PAPER_WORKER_OUT required')
    cache = bind_output_cache(args.output, args.checkpoint, os.environ)
    reach, slices = load_helpers(args.harness_dir)
    before = reach.source_receipt(Path.cwd())
    if before != MODEL_PIN:
        raise ValueError('frozen model source pin mismatch')
    stem = Path(args.stem).resolve()
    inputs = {name: slices.fixture_receipt(stem.parent / name) for name in slices.CANONICAL_HASHES}
    if stem.name not in inputs:
        raise ValueError('canonical contract stem required')
    payload = dict(kind='whole-prefix', schema='paper-whole-prefix-v1', result='N/A', verified=False,
        stem=str(stem), side=args.side, gas_check='off', max_depth=100000,
        cohort='new 12-job side-separated measurements; not one combined whole baseline',
        planned_guard_seconds=1800, planned_guard_memory_mb=2000, source_before=before,
        runtime=runtime_identity(), proof_cache=str(cache), guard_worker_output=os.environ.get('PAPER_WORKER_OUT'),
        input=inputs[stem.name], canonical_inputs=inputs, analysis_config=slices.validity_analysis_config(),
        helper_sha256=HELPER_HASHES, collector_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        top_level_returned=False, scope=SCOPE)
    journal = PrefixJournal(args.checkpoint, payload)
    journal.write(0, force=True)
    try:
        collect(args, payload, journal)
        payload['result'] = 'WHOLE-PREFIX-METRICS' if payload['top_level_returned'] else 'N/A'
    except Exception as error:
        payload.update(result='ERR', measurement_error=f'{type(error).__name__}: {error}')
    finally:
        after = reach.source_receipt(Path.cwd())
        after_inputs = {name: slices.fixture_receipt(stem.parent / name) for name in slices.CANONICAL_HASHES}
        helper_after = {name: sha256((args.harness_dir / name).read_bytes()).hexdigest() for name in HELPER_HASHES}
        payload.update(source_after=after, source_unchanged=before == after,
            input_unchanged=inputs == after_inputs, checkpoint_sha256=sha256(args.checkpoint.read_bytes()).hexdigest(),
            helper_after=helper_after, helper_unchanged=helper_after == HELPER_HASHES,
            collector_unchanged=sha256(Path(__file__).read_bytes()).hexdigest() == payload['collector_sha256'],
            last_checkpoint_seq=journal.seq, observed_terminal_candidate_lower_bound=journal.count)
        if not all(payload[k] for k in ('source_unchanged', 'input_unchanged', 'helper_unchanged', 'collector_unchanged')):
            payload['result'] = 'ERR'
        args.output.parent.mkdir(parents=True, exist_ok=True)
        atomic_json(args.output, payload)
    print(payload['result'])
    return 0 if payload['result'] != 'ERR' else 1


if __name__ == '__main__':
    raise SystemExit(main())
