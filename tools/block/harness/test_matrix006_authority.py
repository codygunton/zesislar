"""Check the exact matrix006 source delta without admission or proof work."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import memory_policy as P
import port_native_policy

RELEASE = Path('/home/cody/zesislar/_build/agents/worker-build-2/PORT-matrix006-authority-v1')
CHANGED = {'800d6a14', '800d6ab4'}


class Matrix006Authority(unittest.TestCase):
    def setUp(self):
        self.profile = json.loads((RELEASE / 'PROFILE-v31.json').read_text())
        self.authority = P.production_port_authority(self.profile)
        self.previous = json.loads((RELEASE / 'BASE-AUTHORITY-26fad.json').read_text())

    def job(self, case):
        return {'key': case['block'], 'phase': 'native', 'target': {
            'module': case['module'], 'pc': case['pc'],
            'source_sha256': case['source']['sha256'],
            'statement_sha256': case['statement_sha256']}}

    def workload(self, case, *, wrong_owner=None):
        sources = [dict(case['source'], module=case['module'])]
        sources += self.authority['production_sources']
        modules = {row['module']: row['path'] for row in sources}
        if wrong_owner:
            modules['ZesuSsz.Automation.All'] = str(wrong_owner)
        config = {'proof_runtime': {'module_files': modules},
                  'prepared_workspace': '/', 'declarations_only': False,
                  'prerequisite_modules': []}
        binding = {'path': str(RELEASE / 'PROFILE-v31.json'),
                   'sha256': hashlib.sha256((RELEASE / 'PROFILE-v31.json').read_bytes()).hexdigest()}
        return P.workload_for_job(binding, self.job(case), config)

    def test_inventory_and_statements_preserve_all_twenty_two_cases(self):
        self.assertEqual(len(self.authority['cases']), 22)
        extension = P.read(P.PORT_EXTENSION)
        self.assertEqual(self.authority['cases'], extension['original_cases'] + extension['additional_cases'])
        changes = []
        for old, new in zip(self.previous['cases'], self.authority['cases']):
            expected = deepcopy(old)
            if old['block'] in CHANGED:
                expected['source'] = new['source']
                changes.append(old['block'])
            self.assertEqual(new, expected)
        self.assertEqual(set(changes), CHANGED)

    def test_v31_changes_only_three_owners_and_their_source_provenance(self):
        previous = json.loads((RELEASE / 'PORT-FAMILY-AUTHORITY-22.json').read_text())
        expected = deepcopy(previous)
        expected['production_sources'] = self.authority['production_sources']
        expected['matrix006_lineage']['generic_source_freeze'] = self.authority['matrix006_lineage']['generic_source_freeze']
        self.assertEqual(self.authority, expected)
        self.assertEqual(self.authority['cases'], previous['cases'])
        self.assertEqual(self.authority['authority_extension'], previous['authority_extension'])
        self.assertEqual({row['module'] for row in self.authority['production_sources']},
                         {'ZesuSsz.Automation.All', 'ZesuSsz.Automation.Hooks', 'ZesuSsz.Automation.Finish'})

    def test_previous_v3_authority_refuses_under_the_new_exact_pin(self):
        previous_profile = json.loads((RELEASE / 'PROFILE.json').read_text())
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            P.production_port_authority(previous_profile)

    def test_all_twenty_two_actual_sources_pass_the_existing_workload_validator(self):
        for case in self.authority['cases']:
            with self.subTest(block=case['block']):
                workload = self.workload(case)
                job = P.apply_job(self.job(case), workload=workload)
                self.assertEqual(P.validate_job(job), 8 * P.GIB)
                self.assertEqual(job['physical_fence_bytes'], 32 * P.GIB)
                self.assertEqual(port_native_policy.cpu_budgets(job), (None, None))

    def test_previous_caller_hashes_refuse_for_both_changed_cases(self):
        old = {row['block']: row for row in self.previous['cases']}
        for case in self.authority['cases']:
            if case['block'] not in CHANGED:
                continue
            job = self.job(case)
            job['target']['source_sha256'] = old[case['block']]['source']['sha256']
            with self.subTest(block=case['block']), self.assertRaisesRegex(ValueError, 'source or statement differs'):
                P.production_port_case(self.profile, job)

    def test_6974_remains_unauthorized(self):
        job = self.job(self.authority['cases'][0])
        job['key'] = '800d6974'
        with self.assertRaisesRegex(ValueError, 'case is not authorized'):
            P.production_port_case(self.profile, job)

    def test_nonempty_setup_remains_unauthorized(self):
        job = self.job(self.authority['cases'][0])
        job['ordered_modules'] = ['Unapproved.Setup']
        with self.assertRaisesRegex(ValueError, 'empty setup'):
            P.production_port_case(self.profile, job)

    def test_changed_staged_automation_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            wrong = Path(temporary) / 'All.v'
            wrong.write_text('Definition unauthorized := True.\n')
            with self.assertRaisesRegex(ValueError, 'actual workload source differs'):
                self.workload(self.authority['cases'][0], wrong_owner=wrong)

    def test_byte_identical_authority_outside_approved_roots_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            outside = Path(temporary) / 'AUTHORITY.json'
            outside.write_bytes((RELEASE / 'PORT-FAMILY-AUTHORITY-22.json').read_bytes())
            profile = deepcopy(self.profile)
            profile['authority']['path'] = str(outside)
            with self.assertRaisesRegex(ValueError, 'relocation leaves'):
                P.production_port_authority(profile)

    def test_wrong_authority_hash_refuses(self):
        profile = deepcopy(self.profile)
        profile['authority']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            P.production_port_authority(profile)

    def test_policy_and_pending_supplier_state_remain_explicit(self):
        for key in ['claim_bytes', 'physical_fence_bytes', 'native_body', 'setup_order',
                    'minimal_or_private_route', 'fence_hit_retry', 'cpu_policy']:
            self.assertEqual(self.authority[key], self.previous[key])
        state = self.authority['matrix006_lineage']
        self.assertTrue(state['generic_v3_READY_pending'])
        self.assertTrue(state['B1_objects_pending'])
        self.assertFalse(state['object_adoption_authorized'])
        self.assertFalse(state['native_launch_authorized'])


if __name__ == '__main__':
    unittest.main()
