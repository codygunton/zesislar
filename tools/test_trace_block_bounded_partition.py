"""Check SDK partitioning after exact range membership validation."""
from copy import deepcopy
from types import SimpleNamespace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_bounded_ranges import partition_owned_events


class PartitionTests(unittest.TestCase):
    def fixture(self):
        process = {'pid': 10, 'start_ticks': 20}
        refs = [{'path': 'event-%d' % number, 'sha256': str(number) * 64} for number in (1, 2)]
        ranges = SimpleNamespace(by_event={ref['path']: {'operation_index': number,
            'process': dict(process), 'event': dict(ref)} for number, ref in enumerate(refs)})
        return SimpleNamespace(references=refs), ranges, process

    def test_discarded_event_cannot_count_as_retained(self):
        events, ranges, process = self.fixture()
        result = partition_owned_events(events, ranges, process,
            lambda index: {'operation_index': index, 'trial': index == 0, 'accepted': True})
        self.assertEqual(result['sdk_discarded_references'], events.references[:1])
        self.assertEqual(result['native_references'], events.references[1:])

    def test_missing_range_stays_explicit(self):
        events, ranges, process = self.fixture()
        del ranges.by_event[events.references[0]['path']]
        result = partition_owned_events(events, ranges, process,
            lambda index: {'operation_index': index, 'trial': False, 'accepted': True})
        self.assertEqual(result['missing_references'], events.references[:1])

    def test_foreign_process_rejects(self):
        events, ranges, process = self.fixture()
        ranges.by_event[events.references[0]['path']]['process']['start_ticks'] = 99
        with self.assertRaisesRegex(ValueError, 'owned event'):
            partition_owned_events(events, ranges, process, lambda index: {})

    def test_substituted_hash_rejects(self):
        events, ranges, process = self.fixture()
        ranges.by_event[events.references[0]['path']]['event']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'owned event'):
            partition_owned_events(events, ranges, process, lambda index: {})

    def test_wrong_operation_identity_rejects(self):
        events, ranges, process = self.fixture()
        with self.assertRaisesRegex(ValueError, 'exact identity'):
            partition_owned_events(events, ranges, process,
                lambda index: {'operation_index': index + 1, 'trial': False, 'accepted': True})

    def test_non_boolean_trial_rejects(self):
        events, ranges, process = self.fixture()
        with self.assertRaisesRegex(ValueError, 'exact identity'):
            partition_owned_events(events, ranges, process,
                lambda index: {'operation_index': index, 'trial': 0, 'accepted': True})

    def test_non_boolean_acceptance_rejects(self):
        events, ranges, process = self.fixture()
        with self.assertRaisesRegex(ValueError, 'exact identity'):
            partition_owned_events(events, ranges, process,
                lambda index: {'operation_index': index, 'trial': False, 'accepted': 1})

    def test_refused_retained_operation_keeps_its_outcome(self):
        events, ranges, process = self.fixture()
        result = partition_owned_events(events, ranges, process,
            lambda index: {'operation_index': index, 'trial': False, 'accepted': False})
        self.assertFalse(result['operations'][events.references[0]['path']]['accepted'])
        self.assertEqual(result['native_references'], events.references)


if __name__ == '__main__':
    unittest.main()
