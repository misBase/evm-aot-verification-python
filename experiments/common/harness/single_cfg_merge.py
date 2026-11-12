"""Fresh-job single-core CFG wiring and exact-caller coverage observation.

Default import is inert/stdlib-only. A context temporarily wraps to_z3_paths;
only direct frozen core-helper callers receive the coverage gate. Other callers
delegate unchanged. Model/source files and opcode implementations are untouched.
"""
import ast
from contextlib import contextmanager
from hashlib import sha256
import inspect
import re
import sys
from pathlib import Path

ARMS = frozenset(('V0', 'V1', 'V2-B1B2'))
HELPER_SOURCE_SHA256 = '30c3122431274895fe160c2b9894c9bfab145c8bc0be39c8cae75f77e79309f0'


def replacement(original):
    """Compile the real helper's unchanged body with one False -> True keyword."""
    path = Path(inspect.getsourcefile(original))
    if sha256(path.read_bytes()).hexdigest() != HELPER_SOURCE_SHA256:
        raise ValueError('unexpected frozen single-core helper source')
    lines, first_line = inspect.getsourcelines(original)
    tree = ast.parse(''.join(lines))
    if len(tree.body) != 1 or not isinstance(tree.body[0], ast.FunctionDef):
        raise ValueError('expected the actual single-core CFG helper')
    function = tree.body[0]
    if function.name != '_execute_x86_core_cfg':
        raise ValueError('only the single-core helper may be adapted')
    calls = [n for n in ast.walk(function) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Attribute) and n.func.attr == 'to_z3_paths']
    if len(calls) != 1:
        raise ValueError('unexpected single-core execution call count')
    options = {k.arg:k for k in calls[0].keywords}
    if (not isinstance(options['enable_merge'].value, ast.Constant)
            or options['enable_merge'].value.value is not False
            or not isinstance(options['merge_state'].value, ast.Constant)
            or options['merge_state'].value.value is not True):
        raise ValueError('unexpected original CFG/terminal merge configuration')
    options['enable_merge'].value.value = True
    ast.fix_missing_locations(tree)
    ast.increment_lineno(tree, first_line - 1)
    namespace = {}
    # Separate locals keep creation inert; function body still uses original globals.
    exec(compile(tree, str(path), 'exec'), original.__globals__, namespace)
    return namespace[function.name], tree


class CoverageError(ValueError):
    def __init__(self, status, message, evidence):
        super().__init__(message)
        self.status, self.evidence = status, evidence


def _failure_status(reason, details):
    parts = reason.split('; ') if isinstance(reason, str) else []
    depth = details.get('depth_pruned_states')
    matches = [re.fullmatch(r'depth-pruned state count: ([1-9][0-9]*)', part) for part in parts]
    return 'BOUND' if (type(depth) is int and depth > 0 and matches
                       and all(match and int(match[1]) == depth for match in matches)) else 'UNK'


@contextmanager
def observe_single_core(harness, config, *, terminal_paths, execution_mode):
    """One fresh single job: exact-caller coverage gate and optional CFG merge.

    Other to_z3_paths callers (including summary proofs) delegate unchanged.
    Linear core execution has no CFG coverage certificate and is explicitly N/A.
    """
    if execution_mode not in ('cfg', 'linear'):
        raise ValueError('unknown single-core execution mode')
    merged = config in ARMS
    if merged and terminal_paths is not False:
        raise ValueError('merged single arm must explicitly disable terminal paths')
    original_helper = harness._execute_x86_core_cfg
    default_helper = harness._execute_x86_core_cfg_global_states
    # Validate the actual frozen source even for arms whose helper is unchanged.
    source = Path(inspect.getsourcefile(original_helper))
    if sha256(source.read_bytes()).hexdigest() != HELPER_SOURCE_SHA256:
        raise ValueError('unexpected frozen single-core helper source')
    adapted = replacement(original_helper)[0] if merged else original_helper
    program = harness.X86Program
    original_paths = program.to_z3_paths
    callers = (original_helper.__code__, default_helper.__code__, adapted.__code__)
    metadata = dict(merged_helper_installed=merged, case_execution_mode=execution_mode,
        terminal_paths=terminal_paths, coverage_applicable=execution_mode == 'cfg',
        coverage_complete=None if execution_mode == 'linear' else False,
        cfg_merge_actual=None, core_calls=[],
        scope='only direct frozen single-core helper callers; linear is N/A; not a program certificate')

    def checked_paths(instance, *args, **kwargs):
        caller = sys._getframe(1).f_code
        result = original_paths(instance, *args, **kwargs)  # original delegate exactly once
        if not any(caller is code for code in callers):
            return result
        record = dict(enable_merge=kwargs.get('enable_merge', False),
            merge_state=kwargs.get('merge_state', False), max_depth=kwargs.get('max_depth', 1000),
            helper='terminal_paths' if caller is default_helper.__code__ else 'merged_state',
            coverage_complete=False, terminal_states=None)
        metadata['core_calls'].append(record)
        metadata['cfg_merge_actual'] = record['enable_merge']
        try:
            coverage = result.coverage
            details = dict(coverage.details) if coverage is not None else {}
            reason = coverage.reason if coverage is not None else 'missing coverage certificate'
            complete = coverage is not None and coverage.complete is True
            count = len(result.global_states)
            record.update(coverage_complete=complete, terminal_states=count,
                coverage_reason=reason, coverage_details=details,
                coverage_source=coverage.source if coverage is not None else None)
        except Exception as error:
            record['coverage_reason'] = f'malformed core coverage: {type(error).__name__}: {error}'
            metadata.update(coverage_complete=False, coverage_status='UNK')
            raise CoverageError('UNK', record['coverage_reason'], metadata) from error
        if not complete or count == 0:
            status = _failure_status(reason, details) if not complete else 'UNK'
            metadata.update(coverage_complete=False, coverage_status=status)
            raise CoverageError(status, f'single core coverage incomplete/nonempty not established: {reason}', metadata)
        metadata['coverage_complete'] = all(r['coverage_complete'] is True and r['terminal_states'] > 0
                                             for r in metadata['core_calls'])
        metadata['coverage_status'] = 'complete'
        return result

    harness._execute_x86_core_cfg = adapted
    program.to_z3_paths = checked_paths
    try:
        yield metadata
        if execution_mode == 'cfg' and not metadata['core_calls']:
            metadata.update(coverage_complete=False, coverage_status='UNK')
            raise CoverageError('UNK', 'no direct single-core CFG coverage observation', metadata)
    finally:
        program.to_z3_paths = original_paths
        harness._execute_x86_core_cfg = original_helper


