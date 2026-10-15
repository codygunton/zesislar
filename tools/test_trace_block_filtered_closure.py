"""Check synthetic accepted-Qed associations without a proof process."""

import copy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent/'block'))
from trace_block_filtered_closure import verify_kernel_closure
from trace_block_seal import file_sha256
import test_trace_block_filtered_projection as fixtures


class FilteredClosureTests(unittest.TestCase):
    setUp = fixtures.FilteredProjectionTests.setUp
    write = fixtures.FilteredProjectionTests.write
    leaf = fixtures.FilteredProjectionTests.leaf
    index = fixtures.FilteredProjectionTests.index
    envelope = fixtures.FilteredProjectionTests.envelope
    event_row = fixtures.FilteredProjectionTests.event_row
    fixture = fixtures.FilteredProjectionTests.fixture

    def replace_result(self, session, result):
        reference = session['closure_check']['operation']
        path = Path(reference['path'])
        path.write_text(json.dumps({'structuredContent': result}))
        reference['sha256'] = file_sha256(path)
        session['final_obligations']['evidence'] = dict(reference)
        session['operations'][-1].update(reference)

    def test_exact_same_session_accepted_qed_passes(self):
        request, session = self.fixture()
        self.assertEqual(verify_kernel_closure(session, request, evidence_dir=self.root), session['closure_check']['operation'])

    def test_unlisted_operation_cannot_establish_closure(self):
        request, session = self.fixture()
        session['operations'].pop()
        with self.assertRaisesRegex(ValueError, 'same-session operation'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_declined_response_cannot_establish_closure(self):
        request, session = self.fixture()
        self.replace_result(session, {'success': True, 'accepted': False, 'state_id': 1})
        with self.assertRaisesRegex(ValueError, 'accepted native Qed'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_arbitrary_hashed_bytes_cannot_establish_closure(self):
        request, session = self.fixture()
        reference = session['closure_check']['operation']
        Path(reference['path']).write_text('{"fixture":"synthetic accepted Qed"}')
        reference['sha256'] = file_sha256(reference['path'])
        session['operations'][-1].update(reference)
        session['final_obligations']['evidence'] = dict(reference)
        with self.assertRaisesRegex(ValueError, 'successful MCP response'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_wrong_command_or_trial_rejects(self):
        request, original = self.fixture()
        for changes in ({'command': 'idtac.'}, {'trial': True}, {'trial': 0}):
            session = copy.deepcopy(original)
            session['operations'][-1]['arguments'].update(changes)
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_source_state_substitution_rejects(self):
        request, session = self.fixture()
        session['operations'][-1]['arguments']['from_state'] = 99
        with self.assertRaisesRegex(ValueError, 'source-state identity'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_wrong_source_start_rejects(self):
        request, session = self.fixture()
        session['operations'][0]['arguments']['theorem'] = 'other'
        with self.assertRaisesRegex(ValueError, 'prepared source'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_duplicate_operation_reference_rejects(self):
        request, session = self.fixture()
        session['operations'].append(copy.deepcopy(session['operations'][-1]))
        with self.assertRaisesRegex(ValueError, 'same-session operation'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_final_obligation_reference_substitution_rejects(self):
        request, session = self.fixture()
        session['final_obligations']['evidence']['sha256'] = '0'*64
        # The fixture deliberately shares this object with closure.operation.
        # Restore only closure.operation to create the exact substitution.
        session['closure_check']['operation'] = {key: session['operations'][-1][key] for key in ('path','sha256')}
        with self.assertRaisesRegex(ValueError, 'Final obligations differ'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_foreign_session_evidence_rejects(self):
        request, session = self.fixture()
        reference = session['closure_check']['operation']
        foreign = self.base/'foreign-qed.json'
        foreign.write_bytes(Path(reference['path']).read_bytes())
        reference['path'] = str(foreign)
        session['operations'][-1].update(reference)
        session['final_obligations']['evidence'] = dict(reference)
        with self.assertRaisesRegex(ValueError, 'owned session directory'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_absent_operations_reject(self):
        request, session = self.fixture()
        session['operations'] = []
        with self.assertRaisesRegex(ValueError, 'one exact proof start'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_mismatched_final_state_rejects(self):
        request, session = self.fixture()
        session['final_state_id'] = 99
        with self.assertRaisesRegex(ValueError, 'final session state identity'):
            verify_kernel_closure(session, request, evidence_dir=self.root)

    def test_state_hash_metadata_must_be_exact(self):
        request, original = self.fixture()
        response=json.loads(Path(original['closure_check']['operation']['path']).read_text())['structuredContent']
        for check in ({'method':'full rollback','before':21,'after':21},
                      {'method':'Pet.state_hash','before':21,'after':22},
                      {'method':'Pet.state_hash','before':True,'after':True},
                      {'method':'Pet.state_hash','before':'21','after':'21'}, {}):
            session=copy.deepcopy(original)
            path=Path(response['path'])
            path.write_text(json.dumps({'accepted':True,'retained_state_hash_unchanged':True,'retained_state_check':check}))
            result=dict(response,sha256=file_sha256(path))
            self.replace_result(session,result)
            with self.subTest(check=check), self.assertRaisesRegex(ValueError,'public state-hash equality'):
                verify_kernel_closure(session,request,evidence_dir=self.root)

    def test_oversized_operation_metadata_rejects(self):
        request,session=self.fixture()
        reference=session['closure_check']['operation']
        path=Path(reference['path'])
        path.write_text(' '*2_097_153)
        reference['sha256']=file_sha256(path)
        session['operations'][-1].update(reference)
        session['final_obligations']['evidence']=dict(reference)
        with self.assertRaisesRegex(ValueError,'serialized record byte limit'):
            verify_kernel_closure(session,request,evidence_dir=self.root)

    def test_retained_qed_source_state_must_match(self):
        request, session = self.fixture()
        result = json.loads(Path(session['closure_check']['operation']['path']).read_text())['structuredContent']
        path = Path(result['path'])
        path.write_text(json.dumps({'accepted': True, 'retained_state_hash_unchanged': False,
                                    'retained_state_check': {'method': 'Pet.state_hash', 'before': 21, 'after': 22}}))
        result['sha256'] = file_sha256(path)
        self.replace_result(session, result)
        with self.assertRaisesRegex(ValueError, 'public state-hash equality'):
            verify_kernel_closure(session, request, evidence_dir=self.root)


if __name__ == '__main__':
    unittest.main()
