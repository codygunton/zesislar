"""Test synthetic SESSION wiring. These fixtures are not MCP results."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent/'block'))
from trace_block_filtered import bind_descriptors, guard_manifest
from trace_block_filtered_projection import ProjectionView
from trace_block_filtered_seal import verify_filtered_index
from trace_block_seal import file_sha256
from trace_block_stream import build_stream_trace, json_document, markdown_chunks
from test_trace_block import fixture
import test_trace_block_filtered_points as fixtures


class FilteredProjectionTests(unittest.TestCase):
    setUp = fixtures.FilteredPointTests.setUp
    write = fixtures.FilteredPointTests.write
    leaf = fixtures.FilteredPointTests.leaf
    index = fixtures.FilteredPointTests.index
    envelope = fixtures.FilteredPointTests.envelope
    event_row = fixtures.FilteredPointTests.event_row

    def fixture(self, closed=True):
        self.base = self.root
        self.root = self.base/'evidence'
        self.root.mkdir()
        request, unused = fixture('return')
        descriptor = {'rule': 'ReturnRoute', 'commands': {'whole-rule': 'exact I'}, 'log_filter': ['ReturnRoute']}
        descriptors = {'ReturnRoute.normalize': descriptor}
        request.update(workspace=str(self.base), source=str(self.base/'Synthetic.v'), theorem='synthetic',
                       entry_descriptors=descriptors, selected_rules=['ReturnRoute'], observer_runtime={'fixture': True},
                       instrumentation={'entry_coverage_complete': True, 'instruction_coverage_complete': True})
        manifest, payload = guard_manifest(descriptors)
        path = self.base/'GUARDS.json'
        path.write_bytes(payload)
        request['guard_manifest'] = {'path': str(path), 'sha256': hashlib.sha256(payload).hexdigest()}
        row = {'kind': 'guard-counter', 'trial': False, 'invocation': 1, 'client': 'ReturnRoute.normalize',
               'rule': 'ReturnRoute', 'guard_hash': manifest['clients']['ReturnRoute.normalize']['sha256'],
               'classification': 'actual-trigger', 'fresh_evar_before': 7, 'fresh_evar_after': 7}
        self.event_row(1, **row)
        entry = {'rule': 'ReturnRoute.normalize', 'invocation': 1}
        self.event_row(2, **dict(entry, kind='native-entry', trial=False, capture=fixtures.capture()))
        self.event_row(3, **dict(entry, kind='hand-accepted', trial=True, clause='whole-rule', capture=fixtures.capture(True)))
        self.event_row(4, **dict(entry, kind='hand-rollback', trial=False, clause='whole-rule', exact=True, capture=fixtures.capture()))
        self.event_row(5, **dict(entry, client='ReturnRoute.normalize', kind='branch-counter', trial=False, outcome='native-local-success'))
        retained = self.root/'qed-result.json'
        retained.write_text(json.dumps({'accepted': True, 'retained_state_hash_unchanged': True,
                                       'retained_state_check': {'method': 'Pet.state_hash', 'before': 21, 'after': 21}}))
        retained_reference = {'path': str(retained), 'sha256': file_sha256(retained)}
        operation = self.root/'qed.json'
        operation.write_text(json.dumps({'structuredContent': {'success': True, 'accepted': True,
                             'state_id': 2, **retained_reference}}))
        reference = {'path': str(operation), 'sha256': file_sha256(operation)}
        start = self.root/'start.json'
        start.write_text(json.dumps({'structuredContent': {'success': True, 'state_id': 1,
                         'file': request['source'], 'theorem': request['theorem']}}))
        operations = [{'tool': 'rocq_trace_start', 'arguments': {'workspace': request['workspace'],
                       'file': request['source'], 'theorem': request['theorem']},
                       'path': str(start), 'sha256': file_sha256(start)},
                      {'tool': 'rocq_trace_run', 'arguments': {'from_state': 1, 'command': 'Qed.', 'trial': False},
                       **reference}]
        closure = {'command': 'Qed.', 'accepted': True, 'unresolved_evars': False, 'operation': reference}
        session = {'final_state_id': 2, 'ownership': {'pet': {'pid': 17, 'start_ticks': 99}, 'transport_closed_normally': True, 'owned_pet_exited': True},
                   'operations': operations if closed else [],
                   'error': None, 'source_unchanged': True, 'actual_switches': [], 'closure_check': closure if closed else None,
                   'residual_event': None, 'final_obligations': {'availability': 'complete', 'counts': {'goals':0,'stack':0,'shelf':0,'given_up':0},
                   'undefined_evars': 0, 'evidence': reference, 'method': 'kernel-accepted-Qed'}}
        if not closed:
            residual = fixtures.capture()
            residual['show_proof'] = {'availability': 'complete', 'command': 'Show Proof.',
                                      'notation': 'fun H => ?Goal', 'no_notation': 'fun H : True => ?Goal'}
            event = self.event_row(6, kind='checkpoint', rule='residual', invocation=None, trial=False, capture=residual)
            session['residual_event'] = dict(event, path=str(self.root/event['path']))
        (self.root/'SESSION.json').write_text(json.dumps(session))
        return request, session

    def view(self, request):
        return ProjectionView(request, self.root, index_dir=self.base/'indexes')

    def test_closed_projection_renders_and_verifies_exact_filtered_index(self):
        request, session = self.fixture()
        with self.view(request) as view:
            trace = build_stream_trace(request, view)
            self.assertTrue(trace['completion']['trace_complete'], trace['completion']['reasons'])
            self.assertEqual(trace['verdict']['kind'], 'proof_closure')
            self.assertEqual(trace['coverage']['actual_triggers'], {'ReturnRoute': 1})
            index = self.base/'INDEX.json'
            view.write_raw_index(index)
            verify_filtered_index(self.root, request, json.loads(index.read_text()), trace, session['ownership']['pet'])
            self.assertEqual(json.loads(''.join(json_document(trace)))['points'][0]['hand_call'][0]['command'], 'exact I')
            self.assertIn('proof_closure', ''.join(markdown_chunks(trace)))

    def test_open_projection_keeps_both_proof_printers_and_hidden_stack_limit(self):
        request, unused = self.fixture(closed=False)
        with self.view(request) as view:
            trace = build_stream_trace(request, view)
            self.assertTrue(trace['completion']['trace_complete'], trace['completion']['reasons'])
            self.assertFalse(trace['completion']['proof_closed'])
            self.assertEqual(trace['residual']['show_proof']['text_nonotation'], 'fun H : True => ?Goal')
            self.assertIsNone(trace['completion']['final_obligations']['counts']['stack'])
            self.assertEqual(trace['completion']['final_obligations']['availability'], 'unavailable')

    def test_residual_reference_substitution_rejects(self):
        request, session = self.fixture(closed=False)
        session['residual_event']['sha256'] = '0'*64
        (self.root/'SESSION.json').write_text(json.dumps(session))
        with self.assertRaisesRegex(ValueError, 'exact first residual'):
            self.view(request)

    def test_closure_requires_bound_empty_kernel_record(self):
        request, session = self.fixture()
        session['final_obligations']['undefined_evars'] = 1
        (self.root/'SESSION.json').write_text(json.dumps(session))
        with self.assertRaisesRegex(ValueError, 'empty final-obligation'):
            self.view(request)

    def test_index_cache_cannot_enter_raw_evidence(self):
        request, unused = self.fixture()
        with self.assertRaisesRegex(ValueError, 'outside the immutable'):
            ProjectionView(request, self.root, index_dir=self.root/'indexes')


if __name__ == '__main__':
    unittest.main()
