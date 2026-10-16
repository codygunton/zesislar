"""Reject event substitutions and omissions in exact operation ranges."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_bounded_ranges import RangeIndex


class RangeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.base = Path(self.directory.name)
        self.root = self.base / 'evidence'
        self.root.mkdir()
        self.process = {'pid': 10, 'start_ticks': 20}
        self.events = [self.event(number) for number in (1, 2)]

    def save(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        data = (json.dumps(value, separators=(',', ':')) + '\n').encode()
        path.write_bytes(data)
        return {'path': name, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}

    def event(self, sequence):
        ref = self.save('events/process-10/event-%08d.json' % sequence,
                        {'schema': 2, 'sequence': sequence, 'kind': 'fixture'})
        return dict(ref, process=self.process, sequence=sequence)

    def envelope(self, rows, index=0, logical=None):
        text = json.dumps(rows, separators=(',', ':'))
        payload = text.encode()
        ref = self.save('chunks/operation-%d.json' % index, {'schema': 2,
            'kind': 'capture-leaf', 'logical_event': logical or 'operation-%06d/events' % index,
            'ordinal': 0, 'encoding': 'utf-8', 'text': text, 'text_bytes': len(payload),
            'payload_sha256': hashlib.sha256(payload).hexdigest()})
        return {'encoding': 'json-chunks-v1', 'root': ref, 'logical_bytes': len(payload)}

    def range(self, rows=None, index=0):
        rows = self.events if rows is None else rows
        last = {key: self.events[-1][key] for key in ('path', 'sha256', 'bytes', 'sequence')}
        return {'schema': 1, 'availability': 'complete',
            'before': [{'process': self.process, 'last_event': None}],
            'after': [{'process': self.process, 'last_event': last}],
            'emitted': self.envelope(rows, index), 'emitted_count': len(rows), 'errors': []}

    def check(self, record, extra=None):
        operations = [{'event_range': record}] + (extra or [])
        result = RangeIndex(self.root, {'operations': operations}, index_dir=self.base / 'indexes')
        self.addCleanup(result.close)
        return result

    def test_complete_range_joins_both_exact_events(self):
        result = self.check(self.range())
        self.assertEqual(len(result.by_event), 2)
        self.assertEqual(result.operation_indexes, [0])
        self.assertEqual(result.incomplete, [])

    def test_missing_emitted_event_rejects(self):
        with self.assertRaisesRegex(ValueError, 'omits emitted'):
            self.check(self.range(self.events[1:]))

    def test_reordered_events_reject(self):
        with self.assertRaisesRegex(ValueError, 'order'):
            self.check(self.range(list(reversed(self.events))))

    def test_duplicate_operation_membership_rejects(self):
        with self.assertRaisesRegex(ValueError, 'more than one'):
            self.check(self.range(), [{'event_range': self.range(index=1)}])

    def test_substituted_event_hash_rejects(self):
        rows = copy.deepcopy(self.events)
        rows[0]['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            self.check(self.range(rows))

    def test_foreign_process_rejects(self):
        rows = copy.deepcopy(self.events)
        rows[0]['process']['pid'] = 11
        with self.assertRaisesRegex(ValueError, 'process directory'):
            self.check(self.range(rows))

    def test_inconsistent_sequence_rejects(self):
        rows = copy.deepcopy(self.events)
        rows[0]['sequence'] = 9
        with self.assertRaisesRegex(ValueError, 'sequence'):
            self.check(self.range(rows))

    def test_wrong_logical_identifier_rejects(self):
        record = self.range()
        record['emitted'] = self.envelope(self.events, logical='foreign/events')
        with self.assertRaisesRegex(ValueError, 'different logical event'):
            self.check(record)

    def test_missing_after_boundary_rejects(self):
        record = self.range()
        record['after'] = []
        with self.assertRaisesRegex(ValueError, 'after boundary'):
            self.check(record)

    def test_event_before_range_rejects(self):
        record = self.range()
        record['before'][0]['last_event'] = {key: self.events[0][key] for key in ('path', 'sha256', 'bytes', 'sequence')}
        with self.assertRaisesRegex(ValueError, 'outside'):
            self.check(record)

    def test_complete_with_error_rejects(self):
        record = self.range()
        record['errors'] = [{'phase': 'after', 'message': 'unbound process'}]
        with self.assertRaisesRegex(ValueError, 'contradicts'):
            self.check(record)

    def test_incomplete_range_preserves_available_memberships(self):
        record = self.range(self.events[1:])
        record.update(availability='incomplete', errors=[{'phase': 'after', 'message': 'missing event'}])
        result = self.check(record)
        self.assertEqual(result.incomplete, [0])
        self.assertEqual(len(result.by_event), 1)

    def test_legacy_missing_range_stays_incomplete(self):
        result = self.check(self.range(), [{}])
        self.assertEqual(result.incomplete, [1])

    def test_incorrect_count_rejects(self):
        record = self.range()
        record['emitted_count'] = 3
        with self.assertRaisesRegex(ValueError, 'count differs'):
            self.check(record)


if __name__ == '__main__':
    unittest.main()
