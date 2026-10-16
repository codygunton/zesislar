"""Keep bounded projection limits explicit before actual range integration."""
from copy import deepcopy
from types import SimpleNamespace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_bounded_projection import ProjectionView, trial_plan
from trace_block import make_parser
from trace_block_bounded_bundle import markdown


class ProjectionTests(unittest.TestCase):
    def view(self):
        view = ProjectionView.__new__(ProjectionView)
        view.request = {'block_pc': '0x800d69b0', 'scope': {},
            'rule_set': [{'name': 'ReturnRoute', 'enabled': False}],
            'entry_descriptors': {'ReturnRoute.normalize': {'rule': 'ReturnRoute'}},
            'instrumentation': {'entry_coverage_complete': True, 'instruction_coverage_complete': True},
            'stop': {'kind': 'rule', 'value': 'ReturnRoute'}}
        view.session_id = 'logical-session'
        view.session = {'error': None, 'source_unchanged': True, 'observation_complete': True,
            'ownership': {'transport_closed_normally': True, 'owned_pet_exited': True},
            'observer_status': {'status': {'complete': True}}, 'closure_check': None}
        checkpoint = {'kind': 'checkpoint-counter', 'trial': False, 'label': 'instruction-lookup',
            'literal_pc': '42', 'pc_availability': 'closed-literal',
            'focused_goals': [1], 'fresh_evar_counter': 2}
        view.native_rows = [({'path': 'event'}, checkpoint)]
        view.points = SimpleNamespace(points=[], residual={})
        view.operation_gaps = []
        view.range_index = SimpleNamespace(incomplete=[])
        return view

    def test_cli_default_selects_bounded_package(self):
        args = make_parser().parse_args(['--block', '0x800d69b0', '--rules', 'ReturnRoute=on',
                                        '--stop', 'residual', '--out', '/tmp/output'])
        self.assertEqual(args.surface_policy, 'bounded-kernel-v1')

    def test_cli_retains_explicit_filtered_compatibility(self):
        args = make_parser().parse_args(['--block', '0x800d69b0', '--rules', 'ReturnRoute=off',
            '--stop', 'residual', '--out', '/tmp/output', '--surface-policy', 'filtered-chunks-v1'])
        self.assertEqual(args.surface_policy, 'filtered-chunks-v1')

    def test_missing_operation_range_blocks_completeness(self):
        view = self.view()
        view.operation_gaps = ['event']
        header = view._header({})
        self.assertFalse(header['completion']['trace_complete'])
        self.assertEqual(header['coverage']['requested_trigger'], 'unobserved')

    def test_incomplete_range_blocks_completeness(self):
        view = self.view()
        view.range_index.incomplete = [3]
        self.assertFalse(view._header({})['completion']['trace_complete'])

    def test_unavailable_pc_blocks_provenance(self):
        view = self.view()
        view.native_rows[0][1].update(literal_pc=None, pc_availability='unavailable')
        header = view._header({})
        self.assertFalse(header['coverage']['instruction_provenance_complete'])

    def test_requested_checkpoint_alone_cannot_establish_instruction_provenance(self):
        view = self.view()
        view.native_rows[0][1]['label'] = 'requested-trigger'
        self.assertFalse(view._header({})['coverage']['instruction_provenance_complete'])

    def test_unknown_guard_remains_incomplete(self):
        view = self.view()
        view.native_rows.append(({'path': 'guard'}, {'kind': 'guard-counter',
            'rule': 'ReturnRoute', 'classification': 'unknown'}))
        header = view._header({})
        self.assertFalse(header['completion']['trace_complete'])
        self.assertEqual(header['coverage']['unknown_guards'], {'ReturnRoute': 1})

    def test_off_status_does_not_remove_actual_trigger(self):
        view = self.view()
        view.native_rows.append(({'path': 'guard'}, {'kind': 'guard-counter',
            'rule': 'ReturnRoute', 'classification': 'actual-trigger'}))
        view.points.points = [{'trigger': {'rule': 'ReturnRoute'}}]
        header = view._header({})
        self.assertEqual(header['coverage']['actual_triggers'], {'ReturnRoute': 1})
        self.assertEqual(header['coverage']['requested_trigger'], 'occurred')

    def test_missing_capture_blocks_completeness(self):
        view = self.view()
        view.native_rows.append(({'path': 'guard'}, {'kind': 'guard-counter',
            'rule': 'ReturnRoute', 'classification': 'actual-trigger'}))
        self.assertFalse(view._header({})['completion']['trace_complete'])

    def test_unsupported_classification_rejects(self):
        view = self.view()
        view.native_rows.append(({'path': 'guard'}, {'kind': 'guard-counter',
            'rule': 'ReturnRoute', 'classification': 'arbitrary'}))
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            view._header({})

    def test_ordered_trial_plan_cannot_omit_declared_commands(self):
        descriptor = {'commands': {'whole-rule': 'original', 'prefix': 'existing'},
                      'trials': [{'clause': 'whole-rule', 'command': 'original', 'exposure': 'not-exposed'}]}
        with self.assertRaisesRegex(ValueError, 'omits'):
            trial_plan(descriptor)

    def test_umbrella_command_substitution_rejects(self):
        descriptor = {'commands': {'whole-rule': 'original'},
                      'trials': [{'clause': 'whole-rule', 'command': 'idtac', 'exposure': 'not-exposed'}]}
        with self.assertRaisesRegex(ValueError, 'exact command'):
            trial_plan(descriptor)

    def test_duplicate_whole_rule_occurrences_stay_ordered(self):
        trial = {'clause': 'whole-rule', 'command': 'original', 'exposure': 'not-exposed'}
        descriptor = {'commands': {'whole-rule': 'original'}, 'trials': [trial, deepcopy(trial)]}
        self.assertEqual(len(trial_plan(descriptor)['trials']), 2)

    def test_rule_success_does_not_override_incomplete_coverage(self):
        view = self.view()
        view.rule_successes = [{'rule': 'ReturnRoute', 'evidence': '#/points/0/rule_success'}]
        view.operation_gaps = ['unbound-event']
        self.assertEqual(view._header({})['verdict']['status'], 'unresolved')

    def test_checked_rule_certificate_selects_named_success_kind(self):
        view = self.view()
        view.native_rows.append(({'path': 'guard'}, {'kind': 'guard-counter',
            'rule': 'ReturnRoute', 'classification': 'actual-trigger'}))
        view.points.points = [{'trigger': {'rule': 'ReturnRoute'}}]
        view.rule_successes = [{'rule': 'ReturnRoute', 'evidence': '#/points/0/rule_success'}]
        verdict = view._header({})['verdict']
        self.assertEqual(verdict, {'status': 'actual-success', 'kind': 'rule_success',
            'session': 'logical-session', 'rule': 'ReturnRoute',
            'evidence': '#/points/0/rule_success'})

    def test_proof_closure_stays_separate_without_rule_certificate(self):
        view = self.view()
        view.session['closure_check'] = {'accepted': True}
        view.points.residual = None
        view.rule_successes = []
        self.assertEqual(view._header({})['verdict']['kind'], 'proof_closure')

    def new_policy_view(self):
        view = self.view()
        view.request['observer_runtime'] = {'raw_policy': 'trigger-selected-raw-v2'}
        view.raw_budget = {'complete': True}
        view.selected_feedback = {'availability': 'complete'}
        return view

    def test_new_policy_missing_feedback_blocks_completeness(self):
        view = self.new_policy_view()
        view.selected_feedback = None
        header = view._header({})
        self.assertFalse(header['completion']['trace_complete'])
        self.assertIn('The selected feedback is unavailable or incomplete.', header['completion']['reasons'])

    def test_new_policy_partial_feedback_blocks_completeness(self):
        view = self.new_policy_view()
        view.selected_feedback = {'availability': 'partial'}
        self.assertFalse(view._header({})['completion']['trace_complete'])

    def test_new_policy_missing_seal_blocks_completeness(self):
        view = self.new_policy_view()
        view.raw_budget = None
        self.assertFalse(view._header({})['completion']['trace_complete'])

    def test_new_policy_exhausted_budget_blocks_completeness(self):
        view = self.new_policy_view()
        view.raw_budget = {'complete': False}
        self.assertFalse(view._header({})['completion']['trace_complete'])

    def test_new_policy_checked_feedback_and_budget(self):
        view = self.new_policy_view()
        self.assertTrue(view._header({})['completion']['trace_complete'])

    def residual_view(self):
        view = self.view()
        view.root = Path('/owned-evidence')
        reference = {'path': 'events/process-10/event-00000005.json', 'sha256': 'a' * 64}
        view.native_rows = [(reference, {'kind': 'checkpoint', 'rule': 'residual', 'trial': False, 'sequence': 5})]
        view.session['residual_event'] = {'path': str(view.root / reference['path']), 'sha256': reference['sha256']}
        view.session['residual_selection'] = {'scope': 'first-focused-leaf',
            'command': '1: ltac2:(trace_bounded_snapshot "residual").',
            'event': view.session['residual_event'], 'selector': {'kind': 'focused-index', 'value': 1},
            'selected_goal_id': 7, 'captured_current_goals': 1, 'shelf_count': 0, 'given_up_count': 0,
            'hidden_peer_goals': {'availability': 'unavailable',
                'reason': 'This selected Proofview capture does not expose hidden focus frames.'}}
        captures = {5: SimpleNamespace(proof={'availability': 'bounded-display'},
            groups={'goals': [{'id': 7}], 'shelf': [], 'given_up': []})}
        return view, captures

    def test_first_residual_keeps_its_exact_selected_goal(self):
        view, captures = self.residual_view()
        view._residual(captures)
        self.assertEqual(view.points.residual['selection']['selected_goal_id'], 7)

    def test_wrong_residual_goal_rejects(self):
        view, captures = self.residual_view()
        view.session['residual_selection']['selected_goal_id'] = 8
        with self.assertRaisesRegex(ValueError, 'actual captured leaf'):
            view._residual(captures)

    def test_residual_boolean_count_rejects(self):
        view, captures = self.residual_view()
        view.session['residual_selection']['captured_current_goals'] = True
        with self.assertRaisesRegex(ValueError, 'count or identity'):
            view._residual(captures)

    def test_residual_boolean_selector_rejects(self):
        view, captures = self.residual_view()
        view.session['residual_selection']['selector']['value'] = True
        with self.assertRaisesRegex(ValueError, 'exact integer'):
            view._residual(captures)

    def test_residual_hidden_peer_claim_rejects(self):
        view, captures = self.residual_view()
        view.session['residual_selection']['hidden_peer_goals'] = {'availability': 'complete', 'goals': []}
        with self.assertRaisesRegex(ValueError, 'explicitly unavailable'):
            view._residual(captures)

    def test_residual_missing_proof_display_rejects(self):
        view, captures = self.residual_view()
        captures[5].proof['availability'] = 'not-requested'
        with self.assertRaisesRegex(ValueError, 'partial proof display'):
            view._residual(captures)

    def test_empty_projection_is_not_a_trigger_snapshot(self):
        trace = {'completion': {'trace_complete': False, 'reasons': ['The range is incomplete.']},
                 'points': [], 'residual': None}
        rendered = ''.join(markdown(trace))
        self.assertIn('no selected trigger snapshot', rendered)
        self.assertIn('bounded displays', rendered)


if __name__ == '__main__':
    unittest.main()
