"""Test process-bound event ingestion without a native proof."""

import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_filtered import bind_descriptors
from trace_block_filtered_events import FilteredEvents, checkpoint_attribution
import test_trace_block_chunks as fixtures


class FilteredEventTests(unittest.TestCase):
    setUp = fixtures.ChunkTests.setUp
    write = fixtures.ChunkTests.write
    leaf = fixtures.ChunkTests.leaf
    index = fixtures.ChunkTests.index
    envelope = fixtures.ChunkTests.envelope

    def prepare(self):
        self.process = {'pid': 17, 'start_ticks': 99}
        self.descriptors = {'ReturnRoute.normalize': {'rule': 'ReturnRoute', 'commands': {}}}
        self.guard = bind_descriptors(self.descriptors)['ReturnRoute.normalize']['typed_guard']['sha256']

    def write_event(self, sequence, **fields):
        row = dict(schema=2, sequence=sequence, **fields)
        path = self.root / ('events/process-17/event-%08d.json' % sequence)
        path.parent.mkdir(parents=True, exist_ok=True)
        raw = json.dumps(row, sort_keys=True).encode()
        path.write_bytes(raw)
        return {'path': str(path.relative_to(self.root)), 'sha256': hashlib.sha256(raw).hexdigest()}

    def counter(self, classification='actual-trigger', **fields):
        self.prepare()
        row = dict(kind='guard-counter', trial=False, invocation=1, parent_invocation=None,
                   client='ReturnRoute.normalize', rule='ReturnRoute', guard_hash=self.guard,
                   classification=classification, outcome='entry', fresh_evar_before=19, fresh_evar_after=19)
        row.update(fields)
        return self.write_event(1, **row)

    def native(self, sequence=2, invocation=1):
        self.event_name = 'event-%08d/capture' % sequence
        self.event = self.event_name
        payload = self.envelope(['{"goal":"P","defined":true}'])
        return FilteredEventTests.write_event(self, sequence, kind='native-entry', rule='ReturnRoute.normalize',
                                       invocation=invocation, trial=False, capture=payload)

    def read(self, references):
        return FilteredEvents(self.root, references, self.process, self.descriptors)

    def test_actual_capture_joins_and_loads_lazily(self):
        counter = self.counter()
        native = self.native()
        events = self.read([counter, native])
        self.assertTrue(events.coverage['required_complete'])
        with events.open_capture(native, self.root / 'capture.sqlite') as document:
            self.assertEqual(document.root, {'goal': 'P', 'defined': True})

    def test_missing_capture_is_incomplete(self):
        events = self.read([self.counter()])
        self.assertFalse(events.coverage['required_complete'])

    def test_claimed_capture_without_payload_rejects(self):
        counter = self.counter()
        native = self.write_event(2, kind='native-entry', rule='ReturnRoute.normalize',
                                  invocation=1, trial=False)
        with self.assertRaisesRegex(ValueError, 'logical capture'):
            self.read([counter, native])

    def test_unknown_guard_stays_incomplete(self):
        events = self.read([self.counter('unknown', guard_hash=None)])
        self.assertFalse(events.coverage['required_complete'])
        self.assertEqual(events.coverage['unknown_guards'], {'ReturnRoute': 1})

    def test_equal_counts_cannot_substitute_invocation(self):
        counter = self.counter()
        with self.assertRaisesRegex(ValueError, 'preceding actual guard'):
            self.read([counter, self.native(invocation=2)])

    def test_wrong_process_directory_rejects(self):
        counter = self.counter()
        with self.assertRaisesRegex(ValueError, 'another process'):
            self.read([dict(counter, path=counter['path'].replace('process-17', 'process-18'))])

    def test_changed_event_and_duplicate_stream_reject(self):
        counter = self.counter('non-trigger')
        with self.assertRaisesRegex(ValueError, 'stream order'):
            self.read([counter, counter])
        (self.root / counter['path']).write_bytes(b'{}')
        with self.assertRaisesRegex(ValueError, 'changed after sealing'):
            self.read([counter])

    def test_trial_and_duplicate_native_capture_reject(self):
        trial = self.counter(trial=True)
        with self.assertRaisesRegex(ValueError, 'native guard'):
            self.read([trial])
        counter = self.counter()
        first = self.native(2)
        second = self.native(3)
        with self.assertRaisesRegex(ValueError, 'repeats a capture'):
            self.read([counter, first, second])

    def test_checkpoint_requires_exact_trial_attribution(self):
        counter = self.counter('non-trigger')
        missing = self.write_event(2, kind='checkpoint-counter', label='instruction-lookup',
                             invocation=None, literal_pc='17', pc_availability='closed-literal')
        self.assertFalse(self.read([counter, missing]).coverage['required_complete'])
        discarded = self.write_event(3, kind='checkpoint-counter', trial=True, label='instruction-lookup',
                               invocation=1, literal_pc='18', pc_availability='closed-literal')
        self.assertEqual(self.read([counter, discarded]).checkpoints, [])

    def test_checkpoint_does_not_assign_pc_to_later_capture(self):
        counter = self.counter()
        checkpoint = self.write_event(2, kind='checkpoint-counter', trial=False, label='instruction-lookup',
                                invocation=None, literal_pc='123', pc_availability='closed-literal',
                                focused_goals=[7], fresh_evar_counter=19)
        native = self.native(3)
        events = self.read([counter, checkpoint, native])
        self.assertEqual(events.checkpoints[0]['literal_pc'], '123')
        self.assertNotIn('literal_pc', events.captures[0])

    def checkpoint_row(self, **changes):
        row = dict(kind='checkpoint-counter', trial=False, label='instruction-lookup',
                   literal_pc='2148362772', pc_availability='closed-literal',
                   focused_goals=[7], fresh_evar_counter=19)
        row.update(changes)
        return row

    def test_canonical_pc_and_explicit_unavailable(self):
        for pc in ('0', '1', '-1', '2148362772'):
            state, complete = checkpoint_attribution(self.checkpoint_row(literal_pc=pc))
            self.assertTrue(complete)
            self.assertEqual(state['availability'], 'complete')
        counter = self.counter('non-trigger')
        unavailable = self.write_event(2, **self.checkpoint_row(literal_pc=None, pc_availability='unavailable'))
        events = self.read([counter, unavailable])
        self.assertFalse(events.coverage['instruction_provenance_complete'])
        self.assertIsNone(events.checkpoints[0]['literal_pc'])
        self.assertEqual(events.checkpoints[0]['state_attribution']['availability'], 'complete')

    def test_invalid_pc_and_availability_reject(self):
        changes = ([{'literal_pc': value} for value in ('not-a-PC', '+1', '01', '-0', ' 1', '', 1, None)]
                   + [{'pc_availability': 'invented'}, {'pc_availability': 'unavailable'}])
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                checkpoint_attribution(self.checkpoint_row(**change))

    def test_missing_or_invalid_state_is_unavailable(self):
        changes = [{'focused_goals': value} for value in (None, [], [True], [7, 7], [-1], ['7'])]
        changes += [{'fresh_evar_counter': value} for value in (None, True, -1, '19')]
        for change in changes:
            state, complete = checkpoint_attribution(self.checkpoint_row(**change))
            self.assertFalse(complete)
            self.assertEqual(state, {'availability': 'unavailable', 'focused_goals': None, 'fresh_evar_counter': None})

    def test_non_native_checkpoint_cannot_establish_attribution(self):
        for change in ({'trial': True}, {'trial': None}, {'kind': 'hand-accepted'}):
            with self.assertRaises(ValueError):
                checkpoint_attribution(self.checkpoint_row(**change))

    def test_generic_label_does_not_establish_instruction_coverage(self):
        counter = self.counter('non-trigger')
        generic = self.write_event(2, **self.checkpoint_row(label='outside'))
        events = self.read([counter, generic])
        self.assertFalse(events.coverage['instruction_provenance_complete'])
        self.assertFalse(events.coverage['required_complete'])
        self.assertEqual(events.checkpoints[0]['literal_pc'], '2148362772')


if __name__ == '__main__':
    unittest.main()
