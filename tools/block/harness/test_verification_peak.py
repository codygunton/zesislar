"""Keep the PORT36 measurement authority narrower than a general sizing rule."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'code'))
import memory_policy
import verification_peak as measured


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class VerificationPeakTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.directory = self.root / 'historical'
        self.directory.mkdir()
        self.bank = self.root / 'bank'
        self.bank.mkdir()
        self.compiler = self.root / 'coqc'
        self.compiler.write_text('pinned compiler')
        modules = ['Controls', 'Rules', 'Subject']
        self.sources = {}
        for module in modules:
            path = self.bank / (module + '.v')
            path.write_text('(* ' + module + ' *)\n')
            self.sources[module] = binding(path)
        self.target = {'module': 'Subject', 'source_sha256': self.sources['Subject']['sha256'],
                       'statement_sha256': 'bound-statement'}
        self.checks = [{'problem_name': 'check' + str(i), 'proof': 'exact body'} for i in range(36)]
        checks = self.save('checks.json', self.checks)
        self.inner = {'phase': 'prerequisites', 'job_output': str(self.directory),
                      'target': {'block': self.target}, 'physical_compiler': binding(self.compiler),
                      'physical_flags': ['-Q', str(self.directory / 'workspace/default'), 'Library'],
                      'declared_outputs': [{'module': name, 'source': self.sources[name]}
                                           for name in ['Controls', 'Rules']]}
        inner = self.save('historical/RUNTIME.json', self.inner)
        self.aggregate = self.root / 'absent-aggregate'
        self.cpu = {'aggregate_peak_bytes': 9710780416, 'CPU_budget_enforced': False,
                    'final_memory_accounting_available': True,
                    'memory_peak_source': str(self.aggregate) + '/memory.peak',
                    'memory_events': {'available': True, 'counters': {}}}
        self.result = {'phase': 'prerequisites', 'success': False, 'returncode': 1,
                       'status': 'infrastructure_failed', 'CPU': self.cpu,
                       'aggregate_peak_bytes': self.cpu['aggregate_peak_bytes']}
        self.closure = {'all_owned_actors_closed': True, 'actors': [{'ended': True}],
                        'claim_key': 'exact-claim'}
        self.release = {'released': True, 'bytes': 16 * measured.GIB, 'claim_key': 'exact-claim'}
        self.packet = {'READY_granted': False, 'checks_expected': 36, 'inner_runtime': inner,
                       'outer_runtime': self.save('outer.json', {}),
                       'result': self.save('historical/RESULT.json', self.result),
                       'closure': self.save('historical/CLOSURE.json', self.closure),
                       'release': self.save('historical/RELEASE.json', self.release),
                       'calls': self.save('calls.json', []), 'CPU': self.cpu,
                       'claim_bytes_released': 16 * measured.GIB, 'aggregate_absent': True,
                       'aggregate': {'aggregate_path': str(self.aggregate)},
                       'final_binding_validation': {'final_validation': {'success': True}}}
        packet = self.save('packet.json', self.packet)
        self.addCleanup(patch.stopall)
        patch.object(measured, 'PACKET', packet).start()
        patch.object(measured, 'CHECKS', checks).start()
        self.profile = {'schema': 'scratch.admission-profile.v1', 'kind': 'focused_check',
                        'sources': [], 'memory_booking': measured.BOOKING,
                        'completed_verification_peak': packet}
        self.config = {'declarations_only': True, 'control_session': None,
                       'declaration_checks': self.checks, 'prepared_workspace': str(self.bank),
                       'proof_runtime': {'module_files': {name: name + '.v' for name in modules}},
                       'effective_compiler_version': {'compiler': binding(self.compiler)},
                       'physical_flags': ['-Q', str(self.bank / 'default'), 'Library']}
        self.job = {'phase': 'prerequisites', 'ordered_modules': [], 'target': self.target}

    def save(self, name, value):
        path = self.root / name
        path.write_text(json.dumps(value))
        return binding(path)

    def workload(self):
        profile = self.save('profile.json', self.profile)
        return memory_policy.workload_for_job(profile, self.job, self.config)

    def test_public_policy_uses_exact_15_gib_and_64_gib_fence(self):
        job = memory_policy.apply_job(self.job, workload=self.workload())
        self.assertEqual(job['claim_bytes'], 15 * measured.GIB)
        self.assertEqual(job['physical_fence_bytes'], 64 * measured.GIB)
        self.assertEqual(memory_policy.validate_job(job), 15 * measured.GIB)
        environment = memory_policy.environment('prerequisites', job['claim_bytes'], job)
        self.assertEqual(environment['ZESU_MODULE_CLAIM_BYTES'], str(15 * measured.GIB))
        self.assertEqual(environment['ZESU_MODULE_LIMIT_GIB'], '64')

    def test_other_authority_refuses(self):
        self.profile['completed_verification_peak'] = self.save('other.json', self.packet)
        with self.assertRaisesRegex(ValueError, 'released profile'):
            self.workload()

    def test_changed_authenticated_evidence_refuses(self):
        Path(measured.PACKET['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'binding changed'):
            self.workload()

    def test_changed_check_subject_rule_and_compiler_refuse(self):
        for kind in ['checks', 'subject', 'rules', 'compiler', 'flags', 'session']:
            with self.subTest(kind=kind):
                config = deepcopy(self.config)
                job = deepcopy(self.job)
                if kind == 'checks':
                    config['declaration_checks'][0]['proof'] = 'different proof'
                elif kind == 'subject':
                    job['target']['statement_sha256'] = 'other statement'
                elif kind == 'rules':
                    path = self.bank / 'Rules.v'
                    original = path.read_bytes()
                    path.write_text('different rules')
                elif kind == 'compiler':
                    config['effective_compiler_version']['compiler']['sha256'] = 'other compiler'
                elif kind == 'flags':
                    config['physical_flags'].append('-other')
                else:
                    config['control_session'] = {'body': 'different execution'}
                try:
                    with self.assertRaises(ValueError):
                        measured.workload(self.save('profile.json', self.profile), self.profile, job, config)
                finally:
                    if kind == 'rules':
                        path.write_bytes(original)

    def test_any_compile_or_dag_booking_refuses(self):
        for update in [{'ordered_modules': ['Rules']}, {'declaration_dag_booking': {'other': True}}]:
            with self.subTest(update=update):
                with self.assertRaises(ValueError):
                    measured.workload(self.save('profile.json', self.profile), self.profile,
                                      dict(self.job, **update), self.config)

    def test_changed_stored_workload_refuses_at_admission(self):
        workload = self.workload()
        workload['verification_context']['declaration_checks'][0]['proof'] = 'changed later'
        with self.assertRaises(ValueError):
            memory_policy.apply_job(self.job, workload=workload)

    def test_changed_measurement_or_incomplete_closure_refuses(self):
        original = deepcopy((self.result, self.closure, self.release, self.packet))
        for key in ['peak', 'cpu_cap', 'oom', 'closure', 'release']:
            with self.subTest(key=key):
                self.result, self.closure, self.release, self.packet = deepcopy(original)
                if key == 'peak':
                    self.result['CPU']['aggregate_peak_bytes'] += 1
                elif key == 'cpu_cap':
                    self.result['CPU']['CPU_budget_enforced'] = True
                elif key == 'oom':
                    self.result['CPU']['memory_events']['counters']['oom_kill'] = 1
                elif key == 'closure':
                    self.closure['actors'][0]['ended'] = False
                else:
                    self.release['bytes'] -= 1
                # Rebind the modified evidence to exercise semantic checks.
                self.packet['result'] = self.save('historical/RESULT.json', self.result)
                self.packet['closure'] = self.save('historical/CLOSURE.json', self.closure)
                self.packet['release'] = self.save('historical/RELEASE.json', self.release)
                ref = self.save('packet.json', self.packet)
                with patch.object(measured, 'PACKET', ref):
                    self.profile['completed_verification_peak'] = ref
                    with self.assertRaises(ValueError):
                        self.workload()

    def test_default_focused_booking_stays_8_gib(self):
        profile = self.save('default.json', {'schema': 'scratch.admission-profile.v1',
                                           'kind': 'focused_check', 'sources': []})
        job = memory_policy.apply_job(self.job, workload=memory_policy.workload_for_job(
            profile, self.job, self.config))
        self.assertEqual(job['claim_bytes'], 8 * measured.GIB)

    def test_declaration_only_refresh_skips_unscheduled_native_job(self):
        profile = self.save('profile.json', self.profile)
        self.assertIsNone(memory_policy.workload_for_job(
            profile, {'phase': 'native', 'target': self.target}, self.config))


if __name__ == '__main__':
    unittest.main()
