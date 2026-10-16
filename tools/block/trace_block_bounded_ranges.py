"""Check exact event membership in recorded SESSION operation ranges."""
from collections.abc import Mapping, Sequence
from pathlib import Path
import re

from trace_block_kernel_display import artifact, _fields, _integer, _same
from trace_block_lazy_capture import LazyCapture


def _process(value):
    _fields(value, 'pid start_ticks')
    for item in value.values():
        _integer(item, 1)
    return value['pid'], value['start_ticks']


def _event(root, value, *, boundary=False):
    _fields(value, 'path sha256 bytes sequence' if boundary else 'process path sha256 bytes sequence')
    sequence = value['sequence']
    _integer(sequence, 1)
    name = value['path']
    if not isinstance(name, str):
        raise ValueError('An operation range event has no exact path.')
    match = re.fullmatch(r'events/process-([1-9][0-9]*)/event-([0-9]{8})\.json', name)
    if match is None or int(match[2]) != sequence:
        raise ValueError('An operation range event has an inconsistent path or sequence.')
    if not boundary and _process(value['process'])[0] != int(match[1]):
        raise ValueError('An operation range event has another process directory.')
    artifact(root, {key: value[key] for key in ('path', 'sha256', 'bytes')})
    return int(match[1]), sequence


class RangeIndex:
    """Keep exact operation identities separate from recorded command outcomes."""
    def __init__(self, root, session, *, index_dir):
        self.root = Path(root).resolve(strict=True)
        self.directory = Path(index_dir).absolute()
        if self.directory.resolve().is_relative_to(self.root):
            raise ValueError('The operation range indexes must remain outside raw evidence.')
        self.directory.mkdir(parents=True, exist_ok=True)
        self.by_event = {}
        self.incomplete = []
        self.operation_indexes = []
        self.documents = []
        try:
            for index, operation in enumerate(session['operations']):
                record = operation.get('event_range')
                if record is None:
                    self.incomplete.append(index)
                    continue
                self._range(index, record)
        except BaseException:
            self.close()
            raise

    def _boundaries(self, rows):
        if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes)):
            raise ValueError('The operation range boundary is not an ordered array.')
        result = {}
        order = []
        for row in rows:
            _fields(row, 'process last_event')
            identity = _process(row['process'])
            if identity in result:
                raise ValueError('An operation range boundary repeats a process.')
            last = row['last_event']
            sequence = 0
            if last is not None:
                pid, sequence = _event(self.root, last, boundary=True)
                if pid != identity[0]:
                    raise ValueError('An operation boundary event belongs to another process.')
            result[identity] = (sequence, last)
            order.append(identity)
        if order != sorted(order):
            raise ValueError('The operation range process order is not canonical.')
        return result

    def _range(self, index, record):
        _fields(record, 'schema availability before after emitted emitted_count errors')
        _same(record, 'schema', 1)
        if record['availability'] not in ('complete', 'incomplete'):
            raise ValueError('The operation range availability is unsupported.')
        errors = record['errors']
        if not isinstance(errors, list):
            raise ValueError('The operation range errors are not an array.')
        for error in errors:
            _fields(error, 'phase message')
            if any(not isinstance(item, str) or not item for item in error.values()):
                raise ValueError('The operation range error lacks its exact text.')
        if (record['availability'] == 'complete') != (not errors):
            raise ValueError('The operation range availability contradicts its errors.')
        before, after = self._boundaries(record['before']), self._boundaries(record['after'])
        document = LazyCapture(self.root, record['emitted'], 'operation-%06d/events' % index,
                               self.directory / ('operation-%06d.sqlite' % index))
        self.documents.append(document)
        rows = document.root
        if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes)):
            raise ValueError('The emitted operation events are not an ordered array.')
        _integer(record['emitted_count'])
        if record['emitted_count'] != len(rows):
            raise ValueError('The emitted operation event count differs from its payload.')
        found = {}
        order = []
        for row in rows:
            pid, sequence = _event(self.root, row)
            identity = _process(row['process'])
            if identity not in after:
                raise ValueError('An emitted event has no after boundary.')
            start = before.get(identity, (0, None))[0]
            if not start < sequence <= after[identity][0]:
                raise ValueError('An emitted event lies outside its exact operation boundaries.')
            if row['path'] in self.by_event:
                raise ValueError('An emitted event belongs to more than one operation.')
            self.by_event[row['path']] = {'operation_index': index, 'process': dict(row['process']),
                'event': {key: row[key] for key in ('path', 'sha256', 'bytes', 'sequence')}}
            found.setdefault(identity, []).append(sequence)
            order.append((pid, identity[1], sequence))
        if order != sorted(order):
            raise ValueError('The emitted operation event order is not canonical.')
        if record['availability'] == 'complete':
            if set(before) - set(after):
                raise ValueError('A complete operation range loses a process boundary.')
            for identity, (last, reference) in after.items():
                start, old = before.get(identity, (0, None))
                if last < start or (last == start and reference != old):
                    raise ValueError('An operation range boundary changed without an emitted event.')
                if found.get(identity, []) != list(range(start + 1, last + 1)):
                    raise ValueError('A complete operation range omits emitted events.')
            self.operation_indexes.append(index)
        else:
            self.incomplete.append(index)

    def close(self):
        for document in self.documents:
            document.close()


def partition_owned_events(events, ranges, process, validate_operation):
    """Separate committed and SDK-discarded events by exact recorded membership."""
    _process(process)
    native, discarded, missing, operations = [], [], [], {}
    checked = {}
    for reference in events.references:
        binding = ranges.by_event.get(reference['path'])
        if binding is None:
            missing.append(reference)
            native.append(reference)
            continue
        if binding['process'] != process or binding['event']['sha256'] != reference['sha256']:
            raise ValueError('The operation range differs from its exact owned event.')
        index = binding['operation_index']
        if index not in checked:
            operation = validate_operation(index)
            if (type(operation.get('operation_index')) is not int or operation['operation_index'] != index
                    or type(operation.get('trial')) is not bool or type(operation.get('accepted')) is not bool):
                raise ValueError('The operation validator returned an inconsistent exact identity.')
            checked[index] = operation
        operation = checked[index]
        operations[reference['path']] = operation
        (discarded if operation['trial'] else native).append(reference)
    return {'native_references': native, 'sdk_discarded_references': discarded,
            'missing_references': missing, 'operations': operations}
