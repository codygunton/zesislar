import copy
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import check_bounded_diagnosis as checker
from trace_block_bounded_success import rule_success
import test_trace_block_bounded_success as fixtures


class BoundedTerminalTests(unittest.TestCase):
    def setUp(self):
        fixture = fixtures.RuleSuccessTests()
        fixture.setUp()
        self.fixture = fixture
        self.bundle = checker.CheckedBundle.__new__(checker.CheckedBundle)
        self.bundle.session = 'same-session'
        self.bundle.request = {'entry_descriptors': {'ReturnRoute.rule': {
            'rule': 'ReturnRoute', 'commands': {'whole-rule': 'exact_rule.'}}}}
        self.raw = {'points': [fixture.point], 'snapshots': fixture.snapshots}
        self.bundle.view = SimpleNamespace(trace=self.raw)
        self.bundle.document = copy.deepcopy(dict(self.raw,
            verdict={'status': 'unresolved', 'kind': None, 'session': 'same-session'},
            completion={'proof_closed': False}))
        self.pointer = '/points/0/hand_call/0'
        self.direct = [(['points', '0', 'hand_call', '0', 'commands', '0', 'outcome'], 'accepted')]

    def check(self, citations=None, rule='ReturnRoute'):
        return self.bundle.terminal_rule_success(self.bundle.document, self.pointer, rule,
                                                 self.direct if citations is None else citations)

    def test_direct_named_rule_success_needs_no_whole_proof_closure(self):
        certificate = self.check()
        self.assertEqual(certificate['scope'], 'named-rule')
        self.assertFalse(self.bundle.document['completion']['proof_closed'])
        self.assertEqual(self.bundle.document['verdict']['status'], 'unresolved')

    def test_missing_accepted_state_blocks_certificate(self):
        del self.raw['snapshots']['after']
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.check()

    def test_wrong_rule_identity_blocks_certificate(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.check(rule='ConjunctMatch')

    def test_unresolved_verdict_alone_is_not_success_evidence(self):
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.check([(['verdict', 'status'], 'unresolved')])

    def test_checked_point_certificate_supports_top_verdict(self):
        certificate = rule_success(self.fixture.point, self.fixture.snapshots,
            'exact_rule.', 'same-session', expected_rule='ReturnRoute')
        self.raw['points'][0]['rule_success'] = certificate
        self.bundle.document['verdict'] = {'status': 'actual-success', 'kind': 'rule_success',
            'session': 'same-session', 'rule': 'ReturnRoute',
            'evidence': '#/points/0/rule_success'}
        self.assertEqual(self.check([(['verdict'], self.bundle.document['verdict'])]), certificate)

    def test_mismatched_top_rule_is_not_success_evidence(self):
        self.raw['points'][0]['rule_success'] = rule_success(self.fixture.point,
            self.fixture.snapshots, 'exact_rule.', 'same-session', expected_rule='ReturnRoute')
        self.bundle.document['verdict'] = {'status': 'actual-success', 'kind': 'rule_success',
            'session': 'same-session', 'rule': 'ConjunctMatch',
            'evidence': '#/points/0/rule_success'}
        with self.assertRaises(checker.BoundedDiagnosisError):
            self.check([(['verdict'], self.bundle.document['verdict'])])


if __name__ == '__main__':
    unittest.main()
