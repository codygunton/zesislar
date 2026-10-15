"""Reject classification substitutions against sealed schema2 bytes."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_filtered import guard_manifest
from trace_block_filtered_seal import filtered_index_rows, verify_filtered_index
import test_trace_block_filtered_events as fixtures


class FilteredSealTests(unittest.TestCase):
    setUp = fixtures.FilteredEventTests.setUp
    write = fixtures.FilteredEventTests.write
    leaf = fixtures.FilteredEventTests.leaf
    index = fixtures.FilteredEventTests.index
    envelope = fixtures.FilteredEventTests.envelope
    prepare = fixtures.FilteredEventTests.prepare
    write_event = fixtures.FilteredEventTests.write_event
    counter = fixtures.FilteredEventTests.counter
    native = fixtures.FilteredEventTests.native
    read = fixtures.FilteredEventTests.read

    def fixture(self, classification='actual-trigger'):
        references = [self.counter(classification)]
        if classification == 'actual-trigger':
            references.append(self.native())
        events = self.read(references)
        value, payload = guard_manifest(self.descriptors)
        path = self.root/'GUARDS.json'
        path.write_bytes(payload)
        request = {'entry_descriptors': self.descriptors, 'selected_rules': ['ReturnRoute'],
                   'guard_manifest': {'path': str(path), 'sha256': hashlib.sha256(payload).hexdigest()}}
        attempted, captured = filtered_index_rows(events)
        index = {'schema': 2, 'selection_policy': 'source-filtered-v1',
                 'guard_manifest': request['guard_manifest'], 'events': references,
                 'attempted_entries': attempted, 'captured_entries': captured,
                 'instruction_lookups': [], 'requested_checkpoints': []}
        trace = {'points': [{'trigger': {k: row[k] for k in ('rule', 'client', 'invocation')}} for row in captured],
                 'coverage': events.coverage, 'completion': {'trace_complete': events.coverage['required_complete']}}
        return request, index, trace

    def verify(self, request, index, trace):
        return verify_filtered_index(self.root, request, index, trace, self.process)

    def test_exact_counter_and_capture_set_passes(self):
        request, index, trace = self.fixture()
        result = self.verify(request, index, trace)
        self.assertEqual(len(result['attempted_entries']), 1)
        self.assertEqual(len(result['captured_entries']), 1)

    def test_omission_and_reduced_counts_cannot_hide_entry(self):
        request, index, trace = self.fixture()
        index['attempted_entries'] = []
        trace['coverage']['attempted_entries']['ReturnRoute'] = 0
        with self.assertRaisesRegex(ValueError, 'exact guard counters'):
            self.verify(request, index, trace)

    def test_capture_substitution_and_point_substitution_reject(self):
        for target in ('index', 'point'):
            request, index, trace = self.fixture()
            if target == 'index':
                index['captured_entries'][0]['invocation'] = 2
            else:
                trace['points'][0]['trigger']['invocation'] = 2
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.verify(request, index, trace)

    def test_equal_aggregate_counts_cannot_replace_classification(self):
        request, index, trace = self.fixture()
        index['attempted_entries'][0]['classification'] = 'non-trigger'
        with self.assertRaisesRegex(ValueError, 'exact guard counters'):
            self.verify(request, index, trace)

    def test_unknown_remains_incomplete(self):
        request, index, trace = self.fixture('unknown')
        self.verify(request, index, trace)
        trace['completion']['trace_complete'] = True
        with self.assertRaisesRegex(ValueError, 'cannot establish completeness'):
            self.verify(request, index, trace)

    def test_wrong_policy_manifest_or_checkpoint_index_reject(self):
        for target in ('policy', 'manifest', 'checkpoint'):
            request, index, trace = self.fixture()
            if target == 'policy':
                index['selection_policy'] = '039+040'
            elif target == 'manifest':
                index['guard_manifest'] = dict(request['guard_manifest'], sha256='0'*64)
            else:
                index['instruction_lookups'] = [index['events'][0]]
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.verify(request, index, trace)

    def test_selected_rules_can_derive_from_exact_sealed_switches(self):
        request,index,trace=self.fixture()
        request.pop('selected_rules')
        request['rule_set']=[{'name':'ReturnRoute','enabled':True}]
        self.verify(request,index,trace)
        request['rule_set'][0]['enabled']=False
        result=self.verify(request,index,trace)
        self.assertEqual(result['coverage']['actual_triggers'],{'ReturnRoute':1})
        self.assertIs(request['rule_set'][0]['enabled'],False)

    def test_derived_selection_must_equal_descriptors(self):
        request,index,trace=self.fixture()
        request.pop('selected_rules')
        request['rule_set']=[{'name':'Other','enabled':True}]
        with self.assertRaisesRegex(ValueError,'descriptors differ'):
            self.verify(request,index,trace)

    def test_invalid_derived_assignment_rejects(self):
        request,index,trace=self.fixture()
        request.pop('selected_rules')
        for assignments in (None,[{'name':'ReturnRoute'}],[{'name':'ReturnRoute','enabled':1}],
                            [{'name':'ReturnRoute','enabled':True}]*2):
            request['rule_set']=assignments
            with self.subTest(assignments=assignments), self.assertRaises(ValueError):
                self.verify(request,index,trace)

    def test_guard_file_change_rejects(self):
        request, index, trace = self.fixture()
        Path(request['guard_manifest']['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'source-bound descriptors'):
            self.verify(request, index, trace)


if __name__ == '__main__':
    unittest.main()
