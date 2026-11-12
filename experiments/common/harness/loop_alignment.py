"""External paper profile: EVM header-visit cap follows each executor's actual depth.

Import is stdlib-only and never installs a patch. Detection, strategies, states,
gas, solver settings and deadlines are delegated unchanged. Optional counters
are diagnostic observations and never certificates or semantic path counts.
"""
from functools import wraps
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import sys
import weakref

POLICY = 'evm-max-iteration-equals-actual-max-depth-v1'
_STAMP = '__paper_loop_alignment_v1__'


class LoopAlignment:
    def __init__(self, executor_type, expected_source_sha256, observe):
        self.owner = executor_type
        self.original_init = executor_type.__init__
        if getattr(self.original_init, _STAMP, False):
            raise RuntimeError('loop alignment already installed')
        source = Path(self.original_init.__code__.co_filename).resolve()
        if sha256(source.read_bytes()).hexdigest() != expected_source_sha256:
            raise ValueError('unexpected EVM executor source')
        self.source, self.source_sha256 = str(source), expected_source_sha256
        self.observe, self.closed = observe, False
        self.configurations, self.records, self.observation_errors = {}, [], []
        self._active = {}
        self.original_detect = executor_type._detect_and_handle_loops if observe else None

        @wraps(self.original_init)
        def aligned_init(executor, *args, **kwargs):
            caller = sys._getframe(1).f_code
            result = self.original_init(executor, *args, **kwargs)
            depth, previous = executor.max_depth, executor.max_iteration
            if type(depth) is not int or depth <= 0:
                raise ValueError('loop alignment requires a positive integer actual max_depth')
            executor.max_iteration = depth
            key = (depth, previous)
            self.configurations[key] = self.configurations.get(key, 0) + 1
            if self.observe:
                self._register(executor, depth, previous, caller)
            return result

        setattr(aligned_init, _STAMP, True)
        self.replacement_init = aligned_init
        self.replacement_detect = None
        if observe:
            @wraps(self.original_detect)
            def observed_detect(executor, state, *args, **kwargs):
                try:
                    result = self.original_detect(executor, state, *args, **kwargs)
                except BaseException as error:
                    self._record(executor, state, error)
                    raise
                self._record(executor, state, None)
                return result
            self.replacement_detect = observed_detect
        executor_type.__init__ = aligned_init
        if observe:
            executor_type._detect_and_handle_loops = self.replacement_detect

    def _register(self, executor, depth, previous, caller):
        try:
            uid, key = len(self.records)+1, id(executor)
            pcs = [b.pc for b in executor.blocks]
            headers = sorted(executor.static_loop_headers)
            if not all(type(pc) is int for pc in [*pcs, *headers]):
                raise TypeError('diagnostic block PCs must be integers')
            row = dict(instance_uid=uid, actual_max_depth=depth, original_max_iteration=previous,
                aligned_max_iteration=executor.max_iteration,
                strategy_max_depth=getattr(executor.strategy, 'max_depth', None),
                caller_file=caller.co_filename, caller_function=caller.co_name,
                ordered_block_pcs=pcs, static_headers=headers, header_count=len(headers),
                detector_invocations=0, header_invocations=0, peak_header_visits={},
                crossed_original_cap=False, exceptions=[])
            def expired(ref):
                found = self._active.get(key)
                if found is not None and found[0] is ref:
                    self._active.pop(key)
            ref = weakref.ref(executor, expired)
            self.records.append(row)
            self._active[key] = ref, row
        except Exception as error:
            self.observation_errors.append(dict(type=type(error).__name__, message=str(error)))

    def _record(self, executor, state, error):
        try:
            found = self._active.get(id(executor))
            if found is None or found[0]() is not executor:
                raise RuntimeError('unregistered diagnostic executor')
            row = found[1]
            row['detector_invocations'] += 1
            node = state.node
            if node is not None and node.pc in executor.static_loop_headers:
                count = state.loop_time[node.pc]
                if type(count) is not int:
                    raise TypeError('header visit counter must be an integer')
                row['header_invocations'] += 1
                pc = str(node.pc)
                row['peak_header_visits'][pc] = max(row['peak_header_visits'].get(pc, 0), count)
                row['crossed_original_cap'] |= count > row['original_max_iteration']
            if error is not None:
                row['exceptions'].append(dict(type=type(error).__name__, loop_type=getattr(error, 'loop_type', None)))
        except Exception as observation_error:
            self.observation_errors.append(dict(type=type(observation_error).__name__, message=str(observation_error)))

    def snapshot(self):
        return dict(policy=POLICY, source=self.source, source_sha256=self.source_sha256,
            successful_constructions=sum(self.configurations.values()),
            configurations=[dict(actual_max_depth=d, original_max_iteration=old, aligned_max_iteration=d, count=n)
                for (d, old), n in sorted(self.configurations.items())],
            diagnostic=self.observe, records=deepcopy(self.records), observation_errors=deepcopy(self.observation_errors),
            scope='Operational per-path static-header visits; PC lists identify subsets, not semantic block digests. No solver queries, feasible/distinct path claim or historical causality.')

    def close(self):
        if self.closed:
            return
        if self.owner.__init__ is not self.replacement_init:
            raise RuntimeError('cannot restore loop alignment over another constructor patch')
        if self.observe and self.owner._detect_and_handle_loops is not self.replacement_detect:
            raise RuntimeError('cannot restore loop observation over another detector patch')
        self.owner.__init__ = self.original_init
        if self.observe:
            self.owner._detect_and_handle_loops = self.original_detect
        self.closed = True

    def __enter__(self):
        return self

    def __exit__(self, *_exception):
        self.close()


def install_loop_alignment(executor_type, *, expected_source_sha256, observe=False):
    """Install once in this process; caller supplies the actual EVM class and pin.

    Install before constructing executors. Existing objects are not retrofitted.
    Every newly constructed primary/segment/auxiliary instance uses its own D,
    including omitted/default D. Spawned processes need their own installation.
    """
    return LoopAlignment(executor_type, expected_source_sha256, observe)
