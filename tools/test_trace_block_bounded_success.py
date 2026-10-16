import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from trace_block_bounded_success import rule_success


def reference(label):
    return {'path': label + '.marshal', 'sha256': ('a' if label == 'before' else 'b') * 64, 'bytes': 100}


def snapshot(label, defined=False):
    sidecar = reference(label)
    body = {'availability': 'referenced', 'complete_sidecar': sidecar,
            'node_ref': {'root_id': 'evar/10/body', 'child_path': []}} if defined else None
    return {'surface_policy': 'bounded-kernel-v1', 'complete_sidecar': sidecar,
        'fresh_evar_counter': 20, 'current_goals': [] if defined else [{'id': 10}],
        'shelf': [{'id': 20}], 'given_up': [],
        'evars': {'availability': 'complete-referenced', 'entries': [
            {'id': 10, 'status': 'defined' if defined else 'undefined', 'body': body},
            {'id': 20, 'status': 'undefined', 'body': None}]},
        'completeness': {'printed_terms': 'bounded',
                         'complete_terms': 'marshal-reload-and-membership-verified'}}


class RuleSuccessTests(unittest.TestCase):
    def setUp(self):
        self.snapshots = {'before': snapshot('before'), 'after': snapshot('after', True),
                          'rollback': snapshot('before')}
        self.operation = {'availability': 'complete', 'trial': False, 'accepted': False,
                          'session_operation': 'evidence/SESSION.json#/operations/8'}
        self.trial = {'clause': 'whole-rule', 'command': 'exact_rule.', 'outcome': 'accepted',
            'trial_id': 'invocation-1-occurrence-1', 'before': 'before', 'after_trial': 'after',
            'rollback': 'rollback', 'rollback_equal': True, 'operation': self.operation,
            'commands': [{'command': 'exact_rule.', 'before': '#/snapshots/before',
                          'after': '#/snapshots/after', 'outcome': 'accepted', 'refusal': None}]}
        self.point = dict(self.snapshots['before'], session_id='same-session',
            trigger={'kind': 'rule-entry', 'rule': 'ReturnRoute', 'client': 'ReturnRoute.rule', 'invocation': 1},
            operation=self.operation, hand_call=[self.trial])

    def check(self, **kwargs):
        return rule_success(self.point, self.snapshots, 'exact_rule.', 'same-session',
                            expected_rule=kwargs.pop('expected_rule', 'ReturnRoute'), **kwargs)

    def test_valid_rule_success_retains_earlier_obligation(self):
        value = self.check()
        self.assertEqual(value['entry_goal_evars'], [10])
        self.assertEqual(value['after_undefined_evars'], [20])
        self.assertEqual(value['trial_id'], 'invocation-1-occurrence-1')
        self.assertEqual(value['rollback'], '#/snapshots/rollback')

    def test_native_parent_rejection_does_not_claim_global_survival(self):
        value = self.check()
        self.assertFalse(value['operation']['accepted'])
        self.assertEqual(value['native_branch_survival'], 'unavailable')

    def test_missing_after_snapshot(self):
        del self.snapshots['after']
        self.assertIsNone(self.check())

    def test_missing_after_trial(self):
        del self.trial['after_trial']
        self.assertIsNone(self.check())

    def test_unavailable_accepted_capture(self):
        self.trial['after_trial_availability'] = 'unavailable: capture-error'
        self.assertIsNone(self.check())

    def test_mismatched_rule_identity(self):
        self.assertIsNone(self.check(expected_rule='ConjunctMatch'))

    def test_mismatched_command(self):
        self.trial['command'] = 'another_rule.'
        self.assertIsNone(self.check())

    def test_mismatched_final_command(self):
        self.trial['commands'][-1]['command'] = 'another_rule.'
        self.assertIsNone(self.check())

    def test_missing_defined_body(self):
        self.snapshots['after']['evars']['entries'][0]['body'] = None
        self.assertIsNone(self.check())

    def test_wrong_defined_body_root(self):
        self.snapshots['after']['evars']['entries'][0]['body']['node_ref']['root_id'] = 'evar/20/body'
        self.assertIsNone(self.check())

    def test_unresolved_artifact_alias(self):
        self.snapshots['after']['complete_sidecar'] = {'artifact': '#/artifacts/unknown'}
        self.assertIsNone(self.check())

    def test_new_undefined_evar(self):
        self.snapshots['after']['evars']['entries'].append({'id': 30, 'status': 'undefined', 'body': None})
        self.assertIsNone(self.check())

    def test_defined_target_remains_a_raw_goal(self):
        self.snapshots['after']['current_goals'] = [{'id': 10}]
        self.assertIsNotNone(self.check())

    def test_defined_target_remains_on_raw_shelf(self):
        self.snapshots['after']['shelf'].append({'id': 10})
        self.assertIsNotNone(self.check())

    def test_defined_target_remains_in_raw_given_up(self):
        self.snapshots['after']['given_up'] = [{'id': 10}]
        self.assertIsNotNone(self.check())

    def test_target_is_not_defined(self):
        self.snapshots['after']['evars']['entries'][0] = {'id': 10, 'status': 'undefined', 'body': None}
        self.assertIsNone(self.check())

    def test_duplicate_evar_identity(self):
        self.snapshots['after']['evars']['entries'].append({'id': 20, 'status': 'undefined', 'body': None})
        self.assertIsNone(self.check())

    def test_wrong_session(self):
        self.point['session_id'] = 'foreign'
        self.assertIsNone(self.check())

    def test_wrong_occurrence(self):
        self.trial['trial_id'] = 'invocation-1-occurrence-2'
        self.assertIsNone(self.check())

    def test_explicit_second_occurrence(self):
        second = copy.deepcopy(self.trial)
        second['trial_id'] = 'invocation-1-occurrence-2'
        self.point['hand_call'].append(second)
        self.assertEqual(self.check()['trial_index'], 0)
        self.assertEqual(self.check(trial_index=1)['trial_index'], 1)

    def test_boolean_occurrence_is_not_an_index(self):
        self.assertIsNone(self.check(trial_index=True))

    def test_failed_rollback(self):
        self.trial['rollback_equal'] = False
        self.assertIsNone(self.check())

    def test_changed_rollback_state(self):
        self.snapshots['rollback']['fresh_evar_counter'] += 1
        self.assertIsNone(self.check())

    def test_discarded_outer_operation(self):
        self.operation['trial'] = True
        self.assertIsNone(self.check())

    def test_wrong_enclosing_operation(self):
        self.trial['operation'] = dict(self.operation, session_operation='evidence/SESSION.json#/operations/9')
        self.assertIsNone(self.check())

    def test_refused_trial(self):
        self.trial['outcome'] = 'refused'
        self.assertIsNone(self.check())


if __name__ == '__main__':
    unittest.main()
