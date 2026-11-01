"""Check approved caller imports without admission, compilation, or proof work."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE), str(HERE.parents[0]), str(HERE.parents[1])]
import _historical_fixtures as historical
import memory_policy as P
import port_native_policy
from scratch_statement import source_statement

FIXTURES = HERE / 'test-fixtures/effective-overrides'
IMPORT = b'Require Import ZesuSsz.Automation.EffectiveOverrides.\n'


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class EffectiveOverridesAuthority(unittest.TestCase):
    def setUp(self):
        historical.use_policy(self)
        temporary = tempfile.TemporaryDirectory(dir=historical.root())
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.fixtures = json.loads((FIXTURES / 'MANIFEST.json').read_text())['rows']
        self.callers = {row['block']: row for row in self.fixtures}
        extension = historical.read_json(P.PORT_EFFECTIVE_EXTENSION['path'])
        for case in extension['original_cases'] + extension['additional_cases']:
            if case['block'] in self.callers:
                fixture = self.callers[case['block']]
                case['source'] = binding(FIXTURES / fixture['source'])
        extension_path = self.root / 'EXTENSION.json'
        extension_path.write_text(json.dumps(extension))
        extension_binding = binding(extension_path)
        self.enterContext(patch.object(P, 'PORT_EFFECTIVE_EXTENSION', extension_binding))
        self.authorities = {}
        self.profiles = {}
        for count, field in [(22, 'PORT_EFFECTIVE_AUTHORITY'), (23, 'PORT_EFFECTIVE_AUTHORITY_23')]:
            authority = historical.read_json(getattr(P, field)['path'])
            for case in authority['cases']:
                if case['block'] in self.callers:
                    case['source'] = binding(FIXTURES / self.callers[case['block']]['source'])
            authority['authority_extension'] = extension_binding
            path = self.root / ('AUTHORITY-' + str(count) + '.json')
            path.write_text(json.dumps(authority))
            accepted = binding(path)
            self.enterContext(patch.object(P, field, accepted))
            self.authorities[count] = authority
            self.profiles[count] = {'schema': 'scratch.admission-profile.v1',
                                    'kind': P.PORT_KIND, 'authority': accepted,
                                    'memory_route': 'measured_native'}

    def job(self, case):
        return {'key': case['block'], 'phase': 'native', 'ordered_modules': [],
                'target': {'module': case['module'], 'pc': case['pc'],
                           'source_sha256': case['source']['sha256'],
                           'statement_sha256': case['statement_sha256']}}

    def test_exact_sixteen_sources_pass_the_actual_workload_check(self):
        authority = P.production_port_authority(self.profiles[23])
        profile_path = self.root / 'PROFILE.json'
        profile_path.write_text(json.dumps(self.profiles[23]))
        for case in authority['cases']:
            if case['block'] not in self.callers:
                continue
            with self.subTest(block=case['block']):
                sources = [dict(case['source'], module=case['module'])] + authority['production_sources']
                config = {'prepared_workspace': '/', 'declarations_only': False,
                          'prerequisite_modules': [], 'proof_runtime': {
                              'module_files': {row['module']: row['path'] for row in sources}}}
                job = self.job(case)
                workload = P.workload_for_job(binding(profile_path), job, config)
                sized = P.apply_job(job, workload=workload)
                self.assertEqual(P.validate_job(sized), 8 * P.GIB)
                self.assertEqual(sized['physical_fence_bytes'], 32 * P.GIB)
                self.assertEqual(port_native_policy.cpu_budgets(sized), (None, None))

    def test_fixture_removal_reconstructs_every_original_byte_hash(self):
        for row in self.fixtures:
            with self.subTest(block=row['block']):
                path = FIXTURES / row['source']
                source = path.read_bytes()
                self.assertEqual(hashlib.sha256(source).hexdigest(), row['sha256'])
                self.assertEqual(source.count(IMPORT), 1)
                original = source.replace(IMPORT, b'', 1)
                self.assertEqual(hashlib.sha256(original).hexdigest(), row['original_sha256'])
                self.assertTrue(source.startswith(b'Require Import ZesuSsz.Automation.All.\n'))
                statement = source_statement(path, 'zesu_block.')['statement']
                self.assertEqual(hashlib.sha256(statement.encode()).hexdigest(), row['statement_sha256'])

    def test_twenty_two_and_twenty_three_keep_the_exact_inventory(self):
        for count in (22, 23):
            authority = P.production_port_authority(self.profiles[count])
            self.assertEqual(len(authority['cases']), count)
        self.assertEqual(self.authorities[23]['cases'][:22], self.authorities[22]['cases'])

    def test_data_delta_changes_only_authorized_sources_and_extension(self):
        for count in (22, 23):
            policies = HERE / 'policies'
            before = json.loads((policies / ('PORT-FAMILY-AUTHORITY-' + str(count) + '.json')).read_text())
            after = json.loads((policies / ('PORT-EFFECTIVE-OVERRIDES-AUTHORITY-' + str(count) + '.json')).read_text())
            changed = []
            for original, successor in zip(before['cases'], after['cases']):
                expected = deepcopy(original)
                if original['block'] in self.callers:
                    expected['source'] = successor['source']
                    changed.append(original['block'])
                self.assertEqual(expected, successor)
            self.assertEqual(len(changed), 15 if count == 22 else 16)
            expected = deepcopy(before)
            expected['cases'] = after['cases']
            expected['authority_extension'] = after['authority_extension']
            self.assertEqual(expected, after)

    def test_changed_statement_module_and_address_refuse(self):
        for case in self.authorities[23]['cases']:
            if case['block'] not in self.callers:
                continue
            for field, wrong in [('statement_sha256', '0' * 64), ('module', 'Unapproved.Caller'),
                                 ('pc', case['pc'] + 4)]:
                with self.subTest(block=case['block'], field=field):
                    job = self.job(case)
                    job['target'][field] = wrong
                    with self.assertRaises(ValueError):
                        P.production_port_case(self.profiles[23], job)

    def test_original_unactivated_callers_refuse_under_successor(self):
        for case in self.authorities[23]['cases']:
            if case['block'] not in self.callers:
                continue
            with self.subTest(block=case['block']):
                job = self.job(case)
                job['target']['source_sha256'] = self.callers[case['block']]['original_sha256']
                with self.assertRaisesRegex(ValueError, 'source or statement differs'):
                    P.production_port_case(self.profiles[23], job)

    def test_unauthorized_caller_and_nonempty_setup_refuse(self):
        case = self.authorities[23]['cases'][0]
        for change in [lambda job: job.update(key='Unauthorized'),
                       lambda job: job['target'].update(source_sha256='0' * 64),
                       lambda job: job.update(ordered_modules=['Unapproved.Setup'])]:
            job = self.job(case)
            change(job)
            with self.assertRaises(ValueError):
                P.production_port_case(self.profiles[23], job)

    def test_altered_other_seven_cases_refuse_exact_inventory(self):
        others = [case for case in self.authorities[23]['cases'] if case['block'] not in self.callers]
        self.assertEqual(len(others), 7)
        for other in others:
            with self.subTest(block=other['block']):
                authority = deepcopy(self.authorities[23])
                row = next(row for row in authority['cases'] if row['block'] == other['block'])
                row['statement_sha256'] = '0' * 64
                path = self.root / 'ALTERED.json'
                path.write_text(json.dumps(authority))
                altered = binding(path)
                profile = dict(self.profiles[23], authority=altered)
                # Keep the byte guard active, then test the inventory guard itself.
                with self.assertRaisesRegex(ValueError, 'not authorized'):
                    P.production_port_authority(profile)
                with patch.object(P, 'PORT_EFFECTIVE_AUTHORITY_23', altered):
                    with self.assertRaisesRegex(ValueError, 'exact released inventory'):
                        P.production_port_authority(profile)

    def test_changed_extension_refuses(self):
        authority = deepcopy(self.authorities[23])
        authority['authority_extension']['sha256'] = '0' * 64
        path = self.root / 'WRONG-EXTENSION.json'
        path.write_text(json.dumps(authority))
        altered = binding(path)
        with patch.object(P, 'PORT_EFFECTIVE_AUTHORITY_23', altered):
            with self.assertRaisesRegex(ValueError, 'exact released inventory'):
                P.production_port_authority(dict(self.profiles[23], authority=altered))

    def test_wrong_authority_hash_and_outside_relocation_refuse(self):
        profile = deepcopy(self.profiles[23])
        profile['authority']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'not authorized'):
            P.production_port_authority(profile)
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'AUTHORITY.json'
            path.write_bytes(Path(self.profiles[23]['authority']['path']).read_bytes())
            with self.assertRaisesRegex(ValueError, 'relocation leaves'):
                P.production_port_authority(dict(self.profiles[23], authority=binding(path)))

    def test_new_data_files_match_the_reviewed_hashes(self):
        expected = {
            'PORT-EFFECTIVE-OVERRIDES-AUTHORITY-22.json': '35c7e4a44203e761cb286bff7d95e83d81e08567bdb5dd0323dcd9667ffd8052',
            'PORT-EFFECTIVE-OVERRIDES-AUTHORITY-23.json': '9952675250ea9828e18a1f65741aeede06c9df7689f647da8375470862768bb1',
            'PORT-EFFECTIVE-OVERRIDES-EXTENSION.json': '2f7f180cbad4da9c40c674c3a94a9d21e6f4fc9f1605300457ebf0c2ff5a8932',
        }
        for name, sha256 in expected.items():
            self.assertEqual(binding(HERE / 'policies' / name)['sha256'], sha256)


if __name__ == '__main__':
    unittest.main()
