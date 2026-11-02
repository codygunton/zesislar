"""Check the exact public rendering repair without a proof or admission."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE/'code'), str(HERE), str(HERE.parent), str(HERE.parents[1])]
import memory_policy as P
from entry_chain import binding


class RenderingRepair(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.repair = P.rendering_repair(P.PORT_6974_RENDER_REPAIR)
        self.profile = dict(schema='scratch.admission-profile.v1', kind=P.PORT_KIND,
                            authority=P.PORT_AUTHORITY_23, memory_route='measured_native',
                            memory_booking=P.PORT_FULL_FENCE_BOOKING,
                            rendering_repair=P.PORT_6974_RENDER_REPAIR)

    def job(self, v34=False):
        variant = self.repair['variants']['v3.4' if v34 else 'v3.2']
        source_hash = variant['corrected_source']['sha256']
        if v34:
            source_hash = hashlib.sha256(P.v34_native_caller(
                self.profile['native_rules'], self.profile['normalization_policy'],
                variant['corrected_source'])).hexdigest()
        return dict(key='800d6974', phase='native', ordered_modules=[], target=dict(
            module=self.repair['module'], pc=self.repair['pc'], source_sha256=source_hash,
            statement_sha256=self.repair['corrected_statement_sha256']))

    def saved_profile(self):
        path = self.root/'PROFILE.json'
        path.write_text(json.dumps(self.profile))
        return binding(path)

    def actual_old_context(self):
        directory = Path('/home/cody/zesislar/_build/agents/worker-build-2/'
                         'PORT-v32-OLD-6974-launch-refresh-v1/prepare002/jobs/800d6974')
        reference = binding(directory/'RUNTIME.json')
        self.assertEqual(reference['sha256'],
                         'a4cb741c360449df1ccfa953a1b156e6477d8dc3febfd13baff26778d84bc881')
        runtime = json.loads(Path(reference['path']).read_text())
        workspace = directory/'workspace'
        authority, case = P.production_port_case(self.profile, self.job())
        mapping = {row['module']: row['path'] for row in authority['production_sources']}
        mapping[case['module']] = case['source']['path']
        expected = {
            'MachineSlice6960Entries': 'e47b7c7ffbb577719c9aa68c0b8c1bfe59690be82d6ede14a2f35c8b2e10c6f0',
            'MachineBranch198Entries': '81266ed48586a557c9dde2a0125d2b5c51e9dfa7d6853d260a23aad05c74f3cc',
            'PilotA201Entries': '1005c83416a689b4b4b2b736c87cfde861433e31964c00e98a78a3a7a813750b'}
        for stem, sha in expected.items():
            module = 'ZesuSsz.Generated.DecodeItem.'+stem
            source = workspace/runtime['module_files'][module]
            self.assertEqual(binding(source)['sha256'], sha)
            mapping[module] = str(source)
        return dict(proof_runtime={'module_files': mapping}, prepared_workspace='/',
                    declarations_only=False, prerequisite_modules=[])

    def test_actual_old_bank_matches_the_repair_authority(self):
        from entry_bindings import declared_binders
        context = self.actual_old_context()
        caller = self.repair['variants']['v3.2']['corrected_source']
        caller_binders = declared_binders(Path(caller['path']).read_text(), 'DesignedEntry_800d6974')
        self.assertEqual(len(caller_binders), 23)
        declarations = {'MachineSlice6960Entries': 'machineAt6974',
                        'MachineBranch198Entries': 'machineAt69a4_198',
                        'PilotA201Entries': 'machineAt697c_201'}
        for stem, declaration in declarations.items():
            path = context['proof_runtime']['module_files']['ZesuSsz.Generated.DecodeItem.'+stem]
            self.assertEqual(declared_binders(Path(path).read_text(), declaration), caller_binders)
        workload = P.workload_for_job(self.saved_profile(), self.job(), context)
        rows = {row['module']: row for row in workload['owned_sources']}
        for expected in self.repair['originating_definitions']:
            self.assertEqual(rows[expected['module']]['sha256'], expected['sha256'])
        job = P.apply_job(self.job(), workload=workload)
        self.assertEqual((job['claim_bytes'], job['physical_fence_bytes']), (32*P.GIB, 32*P.GIB))

    def test_new_bank_refuses_with_the_same_corrected_caller(self):
        context = self.actual_old_context()
        caller = self.repair['variants']['v3.2']['corrected_source']
        before = binding(caller['path'])
        original = Path('/home/cody/zesislar/_build/agents/worker-build-2/'
                        'start-render-rss-f5-v1/rerender001/RESULT.json')
        new_rows = json.loads(original.read_text())['originating_definitions']
        for row in new_rows:
            module = 'ZesuSsz.Generated.DecodeItem.'+Path(row['path']).stem
            context['proof_runtime']['module_files'][module] = row['path']
        with self.assertRaisesRegex(ValueError, 'actual workload source differs'):
            P.workload_for_job(self.saved_profile(), self.job(), context)
        self.assertEqual(binding(caller['path']), before)

    def test_v32_repair_keeps_full_booking_and_fence(self):
        job = self.job()
        authority, case = P.production_port_case(self.profile, job)
        sources = [dict(case['source'], module=case['module']),
                   *authority['production_sources'], *self.repair['originating_definitions']]
        context = dict(proof_runtime={'module_files': {row['module']: row['path'] for row in sources}},
                       prepared_workspace='/', declarations_only=False, prerequisite_modules=[])
        workload = P.workload_for_job(self.saved_profile(), job, context)
        job = P.apply_job(job, workload=workload)
        self.assertEqual(job['claim_bytes'], 32*P.GIB)
        self.assertEqual(job['physical_fence_bytes'], 32*P.GIB)

    def test_v34_repair_keeps_the_approved_public_rules_frontier(self):
        # The frozen carrier remains separate from the repaired caller.
        sources = Path('/home/cody/zesislar/_build/agents/worker-build-2/PORT-v34-complete-source-v1')
        self.profile.update(authority=P.PORT_EFFECTIVE_AUTHORITY_23,
                            memory_booking=P.PORT_V34_PEAK_BOOKING,
                            pilot_targets=P.PORT_V34_TARGETS, bank_authority=P.PORT_V34_BANKS,
                            completed_peak_authority=P.PORT_V34_COMPLETED,
                            native_rules=binding(sources/'NATIVE-RULES.v'),
                            normalization_policy=binding(sources/'NATIVE-POLICY.json'))
        job = self.job(v34=True)
        _, case = P.production_port_case(self.profile, job)
        self.assertEqual(case['source'], self.repair['variants']['v3.4']['corrected_source'])
        self.assertEqual(P.measured_fence(dict(job, workload={'kind': P.PORT_KIND,
                                                            'profile': self.saved_profile()})), 32*P.GIB)
        self.assertEqual(P.v34_target(P.PORT_V34_TARGETS, job['target'], job['key'],
                                     P.PORT_6974_RENDER_REPAIR)['statement_sha256'],
                         self.repair['corrected_statement_sha256'])

    def test_repair_refuses_another_block(self):
        authority = P.read(P.PORT_AUTHORITY_23)
        case = next(row for row in authority['cases'] if row['block']=='800d6960')
        job = dict(key=case['block'], phase='native', ordered_modules=[], target=dict(
            module=case['module'], pc=case['pc'], source_sha256=case['source']['sha256'],
            statement_sha256=case['statement_sha256']))
        with self.assertRaisesRegex(ValueError, 'another native target'):
            P.production_port_case(self.profile, job)

    def test_repair_refuses_changed_caller_or_statement(self):
        for field in ['source_sha256', 'statement_sha256']:
            job = self.job()
            job['target'][field] = '0'*64
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'source or statement differs'):
                P.production_port_case(self.profile, job)

    def test_repair_refuses_changed_authority_and_wrong_booking(self):
        path = self.root/'REPAIR.json'
        value = deepcopy(self.repair)
        value['block'] = '800d6960'
        path.write_text(json.dumps(value))
        with self.assertRaises(ValueError):
            P.rendering_repair(binding(path))
        self.profile.pop('memory_booking')
        with self.assertRaisesRegex(ValueError, 'full-fence booking'):
            P.production_port_case(self.profile, self.job())


if __name__ == '__main__':
    unittest.main()
