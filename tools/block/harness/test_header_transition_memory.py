"""Check measured header transitions with synthetic accounting, without proof work."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from unittest.mock import patch
import unittest

from test_effective_overrides_authority import EffectiveOverridesAuthority
import memory_policy as P
import port_native_policy

BLOCKS = ('800d6960', '800d69a4', '800d69d8', '800d69e0',
          '800d6a00', '800d6a08', '800d6a64', '800d6a6c')
PEAKS = (6368075776, 11432308736, 4549230592, 4629671936,
         4804386816, 6295449600, 4506595328, 4979212288)
CLAIMS = (9552113664, 17148463104, 6823845888, 6944507904,
          7206580224, 9443174400, 6759892992, 7468818432)


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class HeaderTransitionMemory(unittest.TestCase):
    def save(self, name, value):
        path = self.root / name
        path.write_text(json.dumps(value))
        return binding(path)

    def setUp(self):
        EffectiveOverridesAuthority.setUp(self)
        self.baseline_path = self.root / 'BASELINE.json'
        self.baseline = {'schema': 'port.v32.old-eight-closure-baseline.v1',
                         'accepted_closed_count': 8, 'all_sixteen_outcomes_complete': False,
                         'must_remain_closed': list(BLOCKS), 'rows': []}
        fixture_binding = self.save('fixture-metadata.json', {'synthetic': True})
        self.baseline.update(inventory=fixture_binding, source_transition=fixture_binding,
                             header_successors=fixture_binding)
        self.rows = []
        self.targets = []
        for block, peak in zip(BLOCKS, PEAKS):
            case = next(row for row in self.authorities[23]['cases'] if row['block'] == block)
            current = Path(case['source']['path'])
            original = self.root / (block + '-original.v')
            original.write_bytes(current.read_bytes().replace(
                b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n', b'', 1))
            state = {'goals': [], 'stack': [], 'shelf': [], 'given_up': [],
                     'kernel_groups': {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}}
            state_binding = self.save(block + '-state.json', state)
            state_binding['state_source'] = 'successful_command_returned_state'
            accounting = {'aggregate_peak_bytes': peak, 'final_memory_accounting_available': True,
                          'scope': 'Synthetic accounting fixture. No proof executed.',
                          'memory_events': {'counters': {}}}
            counts = {'active': 0, 'focus_frames': 0, 'frame_goals': 0, 'shelves': 0, 'given_up': 0}
            result = {'module': case['module'], 'statement_sha256': case['statement_sha256'],
                      'status': 'passed', 'normal_tactic_return': True,
                      'final_memory_accounting_available': True, 'CPU': accounting,
                      'aggregate_peak_bytes': peak, 'group_counts': counts, 'complete_state': state_binding}
            prior = {'block': block, 'module': case['module'], 'status': 'closed', 'accepted_closed': True,
                     'source_checks': {'caller': binding(original), 'statement_sha256': case['statement_sha256']},
                     'job_result': self.save(block + '-result.json', result),
                     'lifecycle': {'closure': self.save(block + '-closure.json', {'all_owned_actors_closed': True}),
                                   'release': self.save(block + '-release.json', {'released': True, 'bytes': 8 * P.GIB})},
                     'costs': {'CPU_receipt': self.save(block + '-accounting.json', accounting), 'peak_bytes': peak,
                               'search_origin': fixture_binding, 'search_end': fixture_binding},
                     'calls': fixture_binding}
            self.baseline['rows'].append(prior)
            self.rows.append(dict(format='completed_stock_header_transition_v1', route='stock_zesu_block',
                module=case['module'], native_source=case['source'], statement_sha256=case['statement_sha256'],
                result=prior['job_result'], closure=prior['lifecycle']['closure'], release=prior['lifecycle']['release'],
                baseline={}, authority=self.profiles[23]['authority']))
            self.targets.append(dict(module=case['module'], pc=case['pc'],
                source_sha256=case['source']['sha256'], statement_sha256=case['statement_sha256']))
        self.baseline_path.write_text(json.dumps(self.baseline))
        self.enterContext(patch.object(P, 'PORT_HEADER_BASELINE_SHA256', binding(self.baseline_path)['sha256']))
        for row in self.rows:
            row['baseline'] = binding(self.baseline_path)

    def test_all_eight_exact_claims(self):
        for row, target, claim in zip(self.rows, self.targets, CLAIMS):
            with self.subTest(module=row['module']):
                checked, reason = P.completed(row, target)
                self.assertIsNone(reason)
                self.assertEqual(checked['claim_bytes'], claim)

    def test_public_workload_and_validation_keep_fence_and_no_cpu_stop(self):
        authority = self.authorities[23]
        profile = dict(self.profiles[23], memory_booking=P.PORT_HEADER_PEAK_BOOKING)
        profile_binding = self.save('PROFILE.json', profile)
        for row, target, claim in zip(self.rows, self.targets, CLAIMS):
            case = next(case for case in authority['cases'] if case['module'] == row['module'])
            sources = [dict(case['source'], module=case['module'])] + authority['production_sources']
            config = {'prepared_workspace': '/', 'declarations_only': False, 'prerequisite_modules': [],
                      'proof_runtime': {'module_files': {value['module']: value['path'] for value in sources}}}
            job = {'key': case['block'], 'phase': 'native', 'ordered_modules': [], 'target': target}
            workload = P.workload_for_job(profile_binding, job, config)
            sized = P.apply_job(job, self.rows, workload)
            self.assertEqual(P.validate_job(sized), claim)
            self.assertEqual(sized['physical_fence_bytes'], 32 * P.GIB)
            self.assertEqual(port_native_policy.cpu_budgets(sized), (None, None))

    def test_missing_measurement_refuses_instead_of_defaulting(self):
        profile = dict(self.profiles[23], memory_booking=P.PORT_HEADER_PEAK_BOOKING)
        profile_binding = self.save('PROFILE.json', profile)
        case = self.authorities[23]['cases'][0]
        sources = [dict(case['source'], module=case['module'])] + self.authorities[23]['production_sources']
        config = {'prepared_workspace': '/', 'declarations_only': False, 'prerequisite_modules': [],
                  'proof_runtime': {'module_files': {value['module']: value['path'] for value in sources}}}
        job = {'key': case['block'], 'phase': 'native', 'ordered_modules': [], 'target': self.targets[0]}
        workload = P.workload_for_job(profile_binding, job, config)
        with self.assertRaisesRegex(ValueError, 'accepted completed measurement'):
            P.apply_job(job, [], workload)

    def test_changed_module_pc_statement_and_source_refuse(self):
        for key, wrong in [('module', 'Wrong.Module'), ('pc', 1),
                           ('statement_sha256', '0' * 64), ('source_sha256', '0' * 64)]:
            target = dict(self.targets[0], **{key: wrong})
            self.assertIsNone(P.completed(self.rows[0], target)[0])

    def test_edited_body_or_duplicate_activation_import_refuses(self):
        for suffix in [b'\n(* changed bytes *)\n', b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n']:
            row = deepcopy(self.rows[0])
            path = self.root / 'Changed.v'
            path.write_bytes(Path(row['native_source']['path']).read_bytes() + suffix)
            row['native_source'] = binding(path)
            self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_wrong_baseline_and_authority_refuse(self):
        for field in ['baseline', 'authority']:
            row = deepcopy(self.rows[0])
            row[field]['sha256'] = '0' * 64
            self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_transitive_measurement_bindings_are_retained(self):
        row = self.rows[0]
        checked, reason = P.completed(row, self.targets[0])
        self.assertIsNone(reason)
        retained = P.header_transition_bindings(checked['measurement'])
        prior = self.baseline['rows'][0]
        for expected in [row['baseline'], row['authority'], prior['source_checks']['caller'],
                         prior['costs']['CPU_receipt'], prior['costs']['search_origin'],
                         prior['costs']['search_end'], prior['calls']]:
            self.assertIn(expected, retained)

    def test_an_odd_peak_rounds_up_to_the_next_byte(self):
        row = self.rows[0]
        prior = self.baseline['rows'][0]
        result = deepcopy(P.read(row['result']))
        peak = PEAKS[0] + 1
        result['aggregate_peak_bytes'] = peak
        result['CPU']['aggregate_peak_bytes'] = peak
        prior['costs']['peak_bytes'] = peak
        prior['costs']['CPU_receipt'] = self.save('odd-accounting.json', result['CPU'])
        prior['job_result'] = self.save('odd-result.json', result)
        row['result'] = prior['job_result']
        self.baseline_path.write_text(json.dumps(self.baseline))
        row['baseline'] = binding(self.baseline_path)
        with patch.object(P, 'PORT_HEADER_BASELINE_SHA256', row['baseline']['sha256']):
            checked, reason = P.completed(row, self.targets[0])
        self.assertIsNone(reason)
        self.assertEqual(checked['claim_bytes'], CLAIMS[0] + 2)

    def test_changed_result_closure_and_release_refuse(self):
        for field in ['result', 'closure', 'release']:
            row = deepcopy(self.rows[0])
            row[field] = self.save('Unrelated.json', {})
            self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_changed_peak_oom_and_open_results_refuse(self):
        for change in [lambda value: value.update(aggregate_peak_bytes=1),
                       lambda value: value['CPU']['memory_events']['counters'].update(oom_kill=1),
                       lambda value: value.update(status='native_open')]:
            row = self.rows[0]
            original_read = P.read
            result = deepcopy(original_read(row['result']))
            change(result)
            with patch.object(P, 'read', side_effect=lambda binding: result if binding == row['result'] else original_read(binding)):
                self.assertIsNone(P.completed(row, self.targets[0])[0])

    def test_old_and_blind_authorities_cannot_select_this_booking(self):
        for authority in [P.PORT_AUTHORITY, P.PORT_AUTHORITY_23, P.PORT_HELDOUT_MEMORY_AUTHORITY]:
            profile = dict(self.profiles[23], authority=authority, memory_booking=P.PORT_HEADER_PEAK_BOOKING)
            with self.assertRaisesRegex(ValueError, 'exact approved authority'):
                P.production_port_authority(profile)


if __name__ == '__main__':
    unittest.main()
