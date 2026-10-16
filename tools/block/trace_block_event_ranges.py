"""Bind each serialized MCP operation to its exact owned event files."""
from __future__ import annotations

import errno
import hashlib
import json
import os
from pathlib import Path
import re

from trace_block_mcp_chunks import PHYSICAL_BYTES, write_field

EVENT = re.compile(r"event-([0-9]{8,})\.json\Z")
PROCESS = re.compile(r"process-([1-9][0-9]*)\Z")
OBSERVATION_ERRORS = (OSError, ValueError, RuntimeError)


def noncritical(error):
    if isinstance(error, (MemoryError, RecursionError, AssertionError)):
        return False
    return not isinstance(error, OSError) or error.errno != errno.ENOMEM


def identity(pid):
    root = Path('/proc') / str(pid)
    fields = (root / 'stat').read_text().rsplit(')', 1)[1].split()
    return {'pid': pid, 'start_ticks': int(fields[19])}, int(fields[1]), (root / 'exe').resolve(strict=True)


class EventRanges:
    def __init__(self, evidence_root, writer, pet_executable):
        self.root = Path(evidence_root).resolve()
        self.events = self.root / 'events'
        self.writer = Path(writer)
        self.pet_executable = Path(pet_executable).resolve()
        self.owner = None
        self.known = {}
        self.emitted = {}
        self.complete = True
        self.failures = []
        self.directory = self.root / 'operation-ranges'
        self.directory.mkdir()

    def _failure(self, errors, phase, error):
        if not noncritical(error):
            raise error
        row = {'phase': phase, 'message': str(error)}
        errors.append(row)
        self.failures.append(row)
        self.complete = False

    def adopt_owner(self, response):
        if not isinstance(response, dict):
            return
        value = response.get('structuredContent')
        if isinstance(value, dict) and value.get('success') is True and 'server_pid' in value:
            values = value.get('server_pid'), value.get('server_start_ticks')
            if all(type(item) is int and item > 0 for item in values):
                self.owner = {'pid': values[0], 'start_ticks': values[1]}
            else:
                self._failure([], 'server-owner', ValueError('The server ownership response is invalid.'))

    def _owned_processes(self, errors, final):
        candidates = set()
        if self.owner is not None:
            try:
                current, _, _ = identity(self.owner['pid'])
                if current != self.owner:
                    raise ValueError('The owned server identity changed.')
                children = (Path('/proc') / str(current['pid']) / 'task' / str(current['pid']) / 'children').read_text()
                for item in children.split():
                    pid = int(item)
                    try:
                        child, parent, executable = identity(pid)
                    except (FileNotFoundError, ProcessLookupError):
                        continue
                    if executable == self.pet_executable and parent == self.owner['pid']:
                        candidates.add(pid)
                        self.known[pid] = child
            except (FileNotFoundError, ProcessLookupError) as error:
                if not final:
                    self._failure(errors, 'server-identity', error)
        for directory in self.events.glob('process-*'):
            match = PROCESS.fullmatch(directory.name)
            if match:
                candidates.add(int(match[1]))
        result = {}
        for pid in sorted(candidates):
            try:
                current, parent, executable = identity(pid)
                if (self.owner is None or parent != self.owner['pid']
                        or executable != self.pet_executable):
                    raise ValueError('An event process is not the owned Pet: ' + str(pid))
                previous = self.known.get(pid)
                if previous is not None and current != previous:
                    raise ValueError('An event process reused an observed PID.')
                self.known[pid] = current
                result[pid] = current
            except (FileNotFoundError, ProcessLookupError) as error:
                if final and pid in self.known:
                    result[pid] = self.known[pid]
                else:
                    self._failure(errors, 'event-process-identity', error)
            except OBSERVATION_ERRORS as error:
                self._failure(errors, 'event-process-identity', error)
        return result

    def _snapshot(self, errors, final=False):
        processes = self._owned_processes(errors, final)
        records = {}
        boundaries = []
        for pid, process in processes.items():
            directory = self.events / ('process-%d' % pid)
            opened = set()
            for fd in (Path('/proc') / str(pid) / 'fd').glob('*'):
                try:
                    opened.add(str(fd.resolve(strict=True)))
                except (FileNotFoundError, ProcessLookupError, OSError):
                    pass
            last = None
            for path in sorted(directory.glob('event-*.json')):
                try:
                    match = EVENT.fullmatch(path.name)
                    if match is None or path.is_symlink():
                        raise ValueError('An event filename or file type is invalid.')
                    if str(path.resolve()) in opened:
                        raise ValueError('An event envelope is still open: ' + str(path))
                    before = path.stat()
                    if before.st_size > PHYSICAL_BYTES:
                        raise ValueError('An event envelope exceeds 2 MiB.')
                    data = path.read_bytes()
                    after = path.stat()
                    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
                            after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns):
                        raise ValueError('An event changed during the range snapshot.')
                    if len(data) > PHYSICAL_BYTES:
                        raise ValueError('An event envelope exceeds 2 MiB.')
                    event = json.loads(data)
                    sequence = int(match[1])
                    if not isinstance(event, dict) or event.get('schema') != 2 or type(event.get('sequence')) is not int or event['sequence'] != sequence:
                        raise ValueError('An event sequence differs from its filename.')
                    reference = {'process': process, 'sequence': sequence,
                                 'path': str(path.relative_to(self.root)),
                                 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
                    records[reference['path']] = reference
                    last = {key: value for key, value in reference.items() if key != 'process'}
                except OBSERVATION_ERRORS as error:
                    self._failure(errors, 'event-snapshot', error)
            boundaries.append({'process': process, 'last_event': last})
        return {'boundaries': boundaries, 'records': records}

    def begin(self, index):
        errors = []
        try:
            state = self._snapshot(errors)
        except OBSERVATION_ERRORS as error:
            self._failure(errors, 'before-snapshot', error)
            state = {'boundaries': [], 'records': {}}
        try:
            value = {'schema': 1, 'operation_index': index,
                     'before': state['boundaries'], 'errors': errors}
            data = (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()
            if len(data) > PHYSICAL_BYTES:
                raise ValueError('The operation begin record exceeds 2 MiB.')
            with (self.directory / ('operation-%06d-BEGIN.json' % index)).open('xb') as stream:
                stream.write(data)
        except OBSERVATION_ERRORS as error:
            self._failure(errors, 'before-record', error)
        return state, errors

    def finish(self, index, before):
        previous, errors = before
        errors = list(errors)
        try:
            after = self._snapshot(errors)
        except OBSERVATION_ERRORS as error:
            self._failure(errors, 'after-snapshot', error)
            after = {'boundaries': [], 'records': {}}
        for path, reference in previous['records'].items():
            if after['records'].get(path) != reference:
                self._failure(errors, 'event-mutation', ValueError('An earlier event changed or disappeared: ' + path))
        emitted = [value for path, value in after['records'].items() if path not in previous['records']]
        emitted.sort(key=lambda row: (row['process']['pid'], row['process']['start_ticks'], row['sequence']))
        envelope = None
        try:
            envelope = write_field(self.root, 'operation-%06d/events' % index, emitted, self.writer)
            for row in emitted:
                key = (row['process']['pid'], row['process']['start_ticks'], row['sequence'])
                if key in self.emitted:
                    raise ValueError('An event belongs to more than one operation.')
                self.emitted[key] = row
        except OBSERVATION_ERRORS as error:
            self._failure(errors, 'range-record', error)
        return {'schema': 1, 'availability': 'complete' if not errors else 'incomplete',
                'before': previous['boundaries'], 'after': after['boundaries'],
                'emitted': envelope, 'emitted_count': len(emitted), 'errors': errors}

    def finalize(self):
        errors = []
        try:
            final = self._snapshot(errors, final=True)
            expected = {(row['process']['pid'], row['process']['start_ticks'], row['sequence']): row
                        for row in final['records'].values()}
            if expected != self.emitted:
                raise ValueError('The final event inventory differs from the operation union.')
        except OBSERVATION_ERRORS as error:
            self._failure(errors, 'final-event-union', error)
        return {'schema': 1, 'complete': self.complete and not errors,
                'emitted_events': len(self.emitted), 'errors': list(self.failures)}
