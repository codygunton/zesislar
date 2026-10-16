import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import trace_block_event_ranges as ranges


class EventRangeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'events/process-100').mkdir(parents=True)
        self.tracker = ranges.EventRanges(self.root, '/unused/writer', '/unused/pet')
        self.process = {'pid': 100, 'start_ticks': 200}
        self.tracker.known[100] = self.process
        self.tracker._owned_processes = lambda errors, final=False: {100: self.process}
        self.payloads = []
        def write(root, event, payload, writer):
            self.payloads.append((event, payload))
            return {'encoding': 'json-chunks-v1', 'logical_event': event}
        patch = mock.patch.object(ranges, 'write_field', write)
        patch.start()
        self.addCleanup(patch.stop)

    def event(self, sequence, **extra):
        path = self.root / ('events/process-100/event-%08d.json' % sequence)
        path.write_text(json.dumps(dict(schema=2, sequence=sequence, **extra)))
        return path

    def test_empty_start(self):
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'complete')
        self.assertEqual(result['before'], [{'process': self.process, 'last_event': None}])
        self.assertEqual(result['emitted_count'], 0)
        self.assertEqual(self.payloads[0][0], 'operation-000000/events')

    def test_prefix_and_discarded_calls(self):
        first = self.tracker.begin(0)
        self.event(1, kind='native-entry')
        prefix = self.tracker.finish(0, first)
        second = self.tracker.begin(1)
        self.event(2, kind='native-entry')
        discarded = self.tracker.finish(1, second)
        self.assertEqual(prefix['emitted_count'], 1)
        self.assertEqual(discarded['before'][0]['last_event']['sequence'], 1)
        self.assertEqual(discarded['after'][0]['last_event']['sequence'], 2)
        self.assertEqual([row['sequence'] for _, payload in self.payloads for row in payload], [1, 2])
        self.assertTrue(self.tracker.finalize()['complete'])

    def test_changed_event(self):
        self.event(1)
        before = self.tracker.begin(0)
        self.event(1, changed=True)
        result = self.tracker.finish(0, before)
        self.assertEqual(result['availability'], 'incomplete')
        self.assertEqual(result['errors'][0]['phase'], 'event-mutation')

    def test_invalid_sequence(self):
        path = self.event(1)
        path.write_text('{"schema":2,"sequence":2}')
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')

    def test_invalid_json_shape(self):
        self.event(1).write_text('[]')
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')

    def test_open_event(self):
        path = self.event(1)
        with path.open('rb') as stream:
            self.process['pid'] = __import__('os').getpid()
            destination = self.root / ('events/process-%d' % self.process['pid'])
            destination.mkdir()
            path.rename(destination / path.name)
            self.tracker._owned_processes = lambda errors, final=False: {self.process['pid']: self.process}
            result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')
        self.assertTrue(any('still open' in row['message'] for row in result['errors']))

    def test_oversized_event(self):
        self.event(1).write_bytes(b' ' * (ranges.PHYSICAL_BYTES + 1))
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')

    def test_symlink_event(self):
        original = self.root / 'original'
        original.write_text('{"schema":2,"sequence":1}')
        (self.root / 'events/process-100/event-00000001.json').symlink_to(original)
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')

    def test_range_output_failure(self):
        before = self.tracker.begin(0)
        self.event(1)
        with mock.patch.object(ranges, 'write_field', side_effect=OSError('injected output failure')):
            result = self.tracker.finish(0, before)
        self.assertEqual(result['availability'], 'incomplete')
        self.assertIsNone(result['emitted'])

    def test_begin_output_failure(self):
        with mock.patch.object(Path, 'open', side_effect=OSError('injected output failure')):
            before = self.tracker.begin(0)
        result = self.tracker.finish(0, before)
        self.assertEqual(result['availability'], 'incomplete')

    def test_unclaimed_event(self):
        self.tracker.finish(0, self.tracker.begin(0))
        self.event(1)
        self.assertFalse(self.tracker.finalize()['complete'])

    def test_critical_errors(self):
        for error in (MemoryError(), RecursionError(), AssertionError()):
            with self.subTest(error=type(error).__name__):
                with self.assertRaises(type(error)):
                    self.tracker._failure([], 'injected', error)

    def test_foreign_process(self):
        self.tracker._owned_processes = ranges.EventRanges._owned_processes.__get__(self.tracker)
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')

    def test_immutable_begin(self):
        self.tracker.begin(0)
        result = self.tracker.finish(0, self.tracker.begin(0))
        self.assertEqual(result['availability'], 'incomplete')


if __name__ == '__main__':
    unittest.main()
