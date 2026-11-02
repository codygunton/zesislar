"""Retain optional timing spans after the caller authenticates its runtime."""

from contextlib import contextmanager
from contextvars import ContextVar
import itertools
import json
import os
from pathlib import Path
import resource
import sys
import time
import uuid


_REFERENCE = ContextVar('phase_attribution_reference', default=None)
_SEQUENCE = itertools.count()


@contextmanager
def reference(value):
    token = _REFERENCE.set(value)
    try:
        yield
    finally:
        _REFERENCE.reset(token)


PHASES = frozenset({
    'outer_runtime_loading', 'outer_runtime_validation', 'controller_runtime_loading',
    'controller_runtime_validation', 'provider_runtime_loading', 'physical_runtime_loading',
    'restart_runtime_verification', 'canonical_reservation',
    'reservation_binding_recheck', 'owned_staging', 'staging_parser',
    'staging_reuse', 'staging_outputs', 'post_request_validation',
    'controller_environment', 'guarded_batch_launch', 'guarded_batch_entry',
    'proof_environment', 'compiler_environment', 'provider_operation_check',
    'snapshot_publication', 'snapshot_forced_validation', 'MCP_transport_startup',
    'MCP_initialize', 'initial_health', 'DAG_adapter_validation', 'DAG_dispatch',
    'physical_input_validation', 'physical_Popen', 'physical_compilation',
})


def enabled(runtime):
    setting = runtime.get('phase_attribution')
    if setting is None:
        return False
    if (not isinstance(setting, dict) or set(setting) != {'enabled'}
            or type(setting['enabled']) is not bool):
        raise ValueError('The phase attribution setting is invalid.')
    return setting['enabled']


def aggregate_sample(identity):
    if identity is None:
        return {'known': False, 'reason': 'unavailable_before_entry'}
    try:
        group = Path(identity['aggregate_path'])
        info = group.stat()
        if (info.st_dev, info.st_ino) != (identity['aggregate_device'],
                                         identity['aggregate_inode']):
            return {'known': False, 'reason': 'identity_changed'}
        values = dict(line.split() for line in (group / 'cpu.stat').read_text().splitlines())
        amount = int(values['usage_usec'])
        if amount < 0:
            raise ValueError('The aggregate CPU counter is invalid.')
        return {'known': True, 'usage_usec': amount,
                'device': info.st_dev, 'inode': info.st_ino}
    except (OSError, KeyError, TypeError, ValueError):
        return {'known': False, 'reason': 'unavailable'}


def capture(aggregate=None):
    """Capture counters without reading or publishing any runtime input."""
    own = resource.getrusage(resource.RUSAGE_SELF)
    children = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {'time_ns': time.time_ns(), 'monotonic_ns': time.monotonic_ns(),
            'self_user': own.ru_utime, 'self_system': own.ru_stime,
            'child_user': children.ru_utime, 'child_system': children.ru_stime,
            'aggregate': aggregate_sample(aggregate)}


class Recorder:
    def __init__(self, runtime, output, *, runtime_reference=None, aggregate=None):
        self.enabled = enabled(runtime)
        self.reference = runtime_reference if runtime_reference is not None else _REFERENCE.get()
        self.aggregate = aggregate
        self.directory = Path(output) / 'phase-attribution'
        self.sequence = _SEQUENCE
        self.warning_written = False
        self.actor = None
        if self.enabled:
            pid = os.getpid()
            fields = (Path('/proc') / str(pid) / 'stat').read_text().rsplit(')', 1)[1].split()
            self.actor = {'pid': pid, 'startticks': int(fields[19])}

    def enter(self, phase, manager):
        if not self.enabled:
            return manager
        recorder = self

        class TimedEntry:
            async def __aenter__(self):
                with recorder.span(phase):
                    return await manager.__aenter__()

            async def __aexit__(self, *arguments):
                return await manager.__aexit__(*arguments)

        return TimedEntry()

    def snapshot(self):
        return capture(self.aggregate)

    def complete(self, phase, before, outcome='completed', *, sequence=None):
        if not self.enabled:
            return
        if phase not in PHASES:
            raise ValueError('The phase attribution name is unsupported.')
        try:
            self.retain(phase, next(self.sequence) if sequence is None else sequence,
                        before, self.snapshot(), outcome)
        except (OSError, ValueError, TypeError):
            if not self.warning_written:
                print('phase attribution: an event could not be retained.', file=sys.stderr)
                self.warning_written = True

    def retain(self, phase, sequence, before, after, outcome):
        left, right = before['aggregate'], after['aggregate']
        aggregate = {'known': False, 'reason': right.get('reason', left.get('reason', 'unavailable'))}
        if left['known'] and right['known']:
            if (left['device'], left['inode']) != (right['device'], right['inode']):
                aggregate = {'known': False, 'reason': 'identity_changed'}
            elif right['usage_usec'] < left['usage_usec']:
                aggregate = {'known': False, 'reason': 'counter_regressed'}
            else:
                aggregate = {'known': True, 'before_usec': left['usage_usec'],
                             'after_usec': right['usage_usec'],
                             'CPU_usec': right['usage_usec'] - left['usage_usec']}
        value = {
            'schema': 'entry-chain.phase-attribution.v1', 'phase': phase,
            'process_identity': self.actor, 'runtime_reference': self.reference,
            'sequence': sequence, 'outcome': outcome,
            'started_time_ns': before['time_ns'], 'ended_time_ns': after['time_ns'],
            'started_monotonic_ns': before['monotonic_ns'],
            'ended_monotonic_ns': after['monotonic_ns'],
            'wall_seconds': (after['monotonic_ns'] - before['monotonic_ns']) / 1_000_000_000,
            'self_user_CPU_seconds': after['self_user'] - before['self_user'],
            'self_system_CPU_seconds': after['self_system'] - before['self_system'],
            'waited_child_user_CPU_seconds': after['child_user'] - before['child_user'],
            'waited_child_system_CPU_seconds': after['child_system'] - before['child_system'],
            'aggregate_identity': self.aggregate, 'aggregate_CPU': aggregate,
            'interval_scope': 'inclusive; overlapping spans are not additive',
        }
        self.directory.mkdir(mode=0o700, exist_ok=True)
        if self.directory.is_symlink():
            raise ValueError('The phase attribution directory is an alias.')
        name = f"{self.actor['pid']}-{self.actor['startticks']}-{sequence}-{uuid.uuid4().hex}.json"
        with (self.directory / name).open('x') as stream:
            json.dump(value, stream, indent=2)
            stream.write('\n')

    @contextmanager
    def span(self, phase):
        if not self.enabled:
            yield
            return
        if phase not in PHASES:
            raise ValueError('The phase attribution name is unsupported.')
        sequence = next(self.sequence)
        before = self.snapshot()
        outcome = 'completed'
        try:
            yield
        except BaseException:
            outcome = 'exception'
            raise
        finally:
            # Timing must not replace a compilation or validation exception.
            self.complete(phase, before, outcome, sequence=sequence)


def for_runtime(runtime, output, *, runtime_reference=None):
    aggregate = None
    if enabled(runtime) and runtime.get('job_output'):
        try:
            receipt = Path(runtime['job_output']) / 'BATCH-IDENTITY.json'
            value = json.loads(receipt.read_text())
            group = Path(value['aggregate_path'])
            # Only the actor's actual aggregate can contribute aggregate CPU.
            current = next(line.split(':', 2)[2] for line in
                           Path('/proc/self/cgroup').read_text().splitlines()
                           if line.startswith('0::'))
            current = (Path('/sys/fs/cgroup') / current.lstrip('/')).resolve()
            if (group.name.startswith(f'zesuworkloads-aggregate{os.getuid()}p')
                    and (group == current or group in current.parents)):
                aggregate = {key: value[key] for key in
                             ['aggregate_path', 'aggregate_device', 'aggregate_inode']}
        except (OSError, ValueError, KeyError, StopIteration, TypeError):
            pass
    return Recorder(runtime, output, runtime_reference=runtime_reference, aggregate=aggregate)
