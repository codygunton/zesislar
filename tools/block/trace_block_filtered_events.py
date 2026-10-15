"""Join sealed filtered events to exact guard and capture identities."""

import hashlib
import json
from pathlib import Path
import re

from trace_block_chunks import ChunkReader, MAX_RECORD_BYTES
from trace_block_filtered import CounterProjection
from trace_block_lazy_capture import LazyCapture
from trace_block_text import chunk_string


def checkpoint_attribution(row):
    """Check one native checkpoint without assigning a PC to another state."""
    if row.get('kind') != 'checkpoint-counter' or row.get('trial') is not False:
        raise ValueError("The record is not an exact native checkpoint.")
    availability, pc = row.get('pc_availability'), row.get('literal_pc')
    if availability == 'closed-literal':
        if not isinstance(pc, str) or re.fullmatch(r'(?:0|[1-9][0-9]*|-[1-9][0-9]*)', pc) is None:
            raise ValueError("The checkpoint PC is not canonical decimal Z text.")
    elif availability == 'unavailable':
        if pc is not None:
            raise ValueError("An unavailable checkpoint PC must be null.")
    else:
        raise ValueError("The checkpoint PC availability is unsupported.")
    goals, fresh = row.get('focused_goals'), row.get('fresh_evar_counter')
    complete = (isinstance(goals, list) and bool(goals)
                and all(type(goal) is int and goal >= 0 for goal in goals)
                and len(set(goals)) == len(goals)
                and type(fresh) is int and fresh >= 0)
    state = {'availability': 'complete' if complete else 'unavailable',
             'focused_goals': goals if complete else None,
             'fresh_evar_counter': fresh if complete else None}
    return state, complete and availability == 'closed-literal'


class EventFiles:
    """Read hash-bound envelopes without assigning production rule semantics."""

    def __init__(self, evidence_root, references, process):
        if (not isinstance(process, dict) or set(process) != {'pid', 'start_ticks'}
                or any(type(value) is not int or value <= 0 for value in process.values())):
            raise ValueError("The event process identity is invalid.")
        self.root = Path(evidence_root).resolve(strict=True)
        self.process = dict(process)
        self.references = list(references)
        last = 0
        for reference in self.references:
            row = self.read(reference)
            if row['sequence'] <= last:
                raise ValueError("The filtered events are not in exact stream order.")
            last = row['sequence']

    def read(self, reference):
        if not isinstance(reference, dict) or set(reference) != {'path', 'sha256'}:
            raise ValueError("A filtered event lacks its exact file binding.")
        name = reference['path']
        expected_prefix = 'events/process-%d/' % self.process['pid']
        if not isinstance(name, str) or not name.startswith(expected_prefix):
            raise ValueError("A filtered event belongs to another process directory.")
        suffix = name[len(expected_prefix):]
        match = re.fullmatch(r'event-([0-9]{8})\.json', suffix)
        if match is None:
            raise ValueError("A filtered event path is unsupported.")
        path = self.root
        for part in Path(name).parts:
            path = path / part
            if path.is_symlink():
                raise ValueError("A filtered event path contains a symlink.")
        with path.open('rb') as stream:
            raw = stream.read(MAX_RECORD_BYTES + 1)
        if len(raw) > MAX_RECORD_BYTES:
            raise ValueError("A filtered event exceeds the serialized byte limit.")
        if hashlib.sha256(raw).hexdigest() != reference['sha256']:
            raise ValueError("A filtered event changed after sealing.")
        def unique(pairs):
            row = {}
            for key, value in pairs:
                if key in row:
                    raise ValueError("A filtered event contains a duplicate key.")
                row[key] = value
            return row
        def invalid_constant(value):
            raise ValueError("A filtered event contains an unsupported JSON constant.")
        row = json.loads(raw, object_pairs_hook=unique, parse_constant=invalid_constant)
        if (not isinstance(row, dict) or type(row.get('schema')) is not int or row['schema'] != 2
                or type(row.get('sequence')) is not int or row['sequence'] != int(match.group(1))
                or not isinstance(row.get('kind'), str)):
            raise ValueError("A filtered event has an invalid schema or identity.")
        return row

    def open_capture(self, reference, index_path):
        if reference not in self.references:
            raise ValueError("The capture event is outside the sealed input list.")
        row = self.read(reference)
        if 'capture' not in row:
            raise ValueError("The event has no logical capture.")
        logical_event = 'event-%08d/capture' % row['sequence']
        return LazyCapture(self.root, row['capture'], logical_event, index_path)

    def text_field(self, reference, field):
        if reference not in self.references:
            raise ValueError("The text event is outside the sealed input list.")
        if field not in ('message', 'refusal'):
            raise ValueError("The event text field is unsupported.")
        row = self.read(reference)
        if field not in row:
            raise ValueError("The event text field is unavailable.")
        return chunk_string(self.root, row[field], 'event-%08d/%s' % (row['sequence'], field))


class FilteredEvents(EventFiles):
    """Read one complete, externally sealed owned process stream.

    The caller must establish session ownership and the complete event set.
    This reader checks every supplied file. It cannot prove a list is complete.
    """

    def __init__(self, evidence_root, references, process, descriptors):
        super().__init__(evidence_root, references, process)
        self.counters = CounterProjection(descriptors, process)
        self.captures = []
        self.capture_references = []
        self.checkpoints = []
        instruction_complete = True
        for reference in self.references:
            row = self.read(reference)
            sequence = row['sequence']
            if row['kind'] == 'guard-counter':
                self.counters.add(row)
            elif row['kind'] == 'native-entry':
                if type(row.get('trial')) is not bool:
                    raise ValueError("A native-entry record lacks exact trial attribution.")
                if row['trial']:
                    continue
                client = row.get('rule')
                invocation = row.get('invocation')
                if not isinstance(client, str) or type(invocation) is not int or invocation <= 0:
                    raise ValueError("A native capture lacks its exact identity.")
                if (client, invocation) not in self.counters.trigger_keys:
                    raise ValueError("A native capture lacks a preceding actual guard.")
                if 'capture' not in row:
                    raise ValueError("A native entry lacks its logical capture.")
                ChunkReader(self.root).validate(row['capture'], 'event-%08d/capture' % sequence)
                self.captures.append({'process': self.process, 'client': client, 'invocation': invocation})
                self.capture_references.append(dict(reference))
            elif row['kind'] == 'checkpoint-counter':
                if type(row.get('trial')) is not bool:
                    instruction_complete = False
                    continue
                if row['trial']:
                    continue
                state, complete = checkpoint_attribution(row)
                instruction_complete &= complete and row.get('label') in ('instruction-lookup', 'requested-trigger')
                self.checkpoints.append({'reference': dict(reference), 'sequence': sequence,
                                         'label': row.get('label'), 'literal_pc': row.get('literal_pc'),
                                         'pc_availability': row.get('pc_availability'),
                                         'state_attribution': state})
        self.coverage = self.counters.coverage(self.captures)
        self.coverage['instruction_provenance_complete'] = instruction_complete
        self.coverage['required_complete'] &= instruction_complete
