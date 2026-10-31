"""Exercise the authorized PORT policy without a proof or live guard rollout."""
from copy import deepcopy
from pathlib import Path
import ast
import hashlib
import inspect
import json
import os
import subprocess
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import scratch
import memory_policy as P
import native_route


def binding(path):
    return {'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}


class ProductionPortMemory(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.authority = deepcopy(P.read(P.PORT_AUTHORITY))
        self.case = self.authority['cases'][0]
        self.source = self.root/'Caller.v'
        self.source.write_bytes(Path(self.case['source']['path']).read_bytes())
        self.case['source'] = binding(self.source)
        self.authority_path = self.root/'AUTHORITY.json'
        self.authority_path.write_text(json.dumps(self.authority))
        self.accepted = binding(self.authority_path)
        authorized = patch.object(P,'PORT_AUTHORITY',self.accepted)
        authorized.start()
        self.addCleanup(authorized.stop)
        self.profile = {'schema':'scratch.admission-profile.v1','kind':P.PORT_KIND,
                        'authority':dict(self.accepted),'memory_route':'measured_native'}
        self.profile_path = self.root/'PROFILE.json'
        self.raw = {'key':self.case['block'],'phase':'native','ordered_modules':[],
                    'target':{'module':self.case['module'],
                              'pc':self.case['pc'],
                              'source_sha256':self.case['source']['sha256'],
                              'statement_sha256':self.case['statement_sha256']}}
        sources = [dict(self.case['source'],module=self.case['module'])]+self.authority['production_sources']
        self.config = {'proof_runtime':{'module_files':{row['module']:row['path'] for row in sources}},
                       'prepared_workspace':'/','declarations_only':False,'prerequisite_modules':[]}

    def profile_binding(self):
        self.profile_path.write_text(json.dumps(self.profile))
        return binding(self.profile_path)

    def workload(self):
        return P.workload_for_job(self.profile_binding(),self.raw,self.config)

    def job(self):
        return P.apply_job(self.raw,workload=self.workload())

    def test_authorized_stock_job_claim8_fence32(self):
        job = self.job()
        self.assertEqual(P.validate_job(job),8*P.GIB)
        self.assertEqual(job['physical_fence_bytes'],32*P.GIB)
        self.assertIsNone(native_route.for_profile(self.profile_binding()))
        self.assertEqual(native_route.source_body(self.profile_binding()),'zesu_block.')

    def test_measured_environment_omits_issue10_and_keeps_cpu_policy(self):
        job = self.job()
        env = P.environment('native',job['claim_bytes'],job=job)
        self.assertEqual(env['ZESU_DIAGNOSTIC_PROBE'],'0')
        self.assertEqual(env['ZESU_PROBE_ISSUE'],'')
        self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(8*P.GIB))
        self.assertEqual(env['ZESU_AGGREGATE_LIMIT'],'32G')
        self.assertEqual(env['ZESU_PROOF_CPU_LIMIT'],'unlimited')

    def test_family_evidence_is_bound(self):
        rows = P.profile_bindings(self.profile_binding())
        self.assertIn(self.profile['authority'],rows)
        self.assertIn(self.authority['completed_common_ready'],rows)
        self.assertIn(self.authority['source_packet'],rows)

    def test_prerequisite_phase_ignores_native_profile(self):
        self.assertIsNone(P.workload_for_job(self.profile_binding(),
                          {'phase':'prerequisites','ordered_modules':[]},self.config))

    def test_actual_sealed_preparation_branch_installs_no_rules(self):
        function = ast.parse(inspect.getsource(scratch.prepare)).body[0]
        branch = next(node for node in function.body if isinstance(node,ast.If)
                      and ast.unparse(node.test)=='sealed and a.admission_profile')
        namespace = dict(scratch.__dict__,sealed=True,
                         a=SimpleNamespace(admission_profile=self.profile_path,
                                           declarations_only=False,control_session=None))
        self.profile_binding()
        with patch('clone_copy.copy2',side_effect=AssertionError('No private Rules installation')):
            exec(compile(ast.fix_missing_locations(ast.Module(body=[branch],type_ignores=[])),
                         '<actual-sealed-preparation>','exec'),namespace)
        self.assertIsNone(namespace['selected'])
        self.assertEqual(native_route.source_body(self.profile_binding()),'zesu_block.')

    def test_sealed_profile_refuses_declaration_or_control_relabeling(self):
        for declaration,control in [(True,None),(False,{'module':'Fixture.Control'})]:
            with self.assertRaisesRegex(ValueError,'ordinary stock native'):
                scratch.sealed_rules_prefix(self.profile_binding(),declaration,control)

    def test_actual_sealed_binding_branch_needs_no_private_rules_module(self):
        function = ast.parse(inspect.getsource(scratch.prepare)).body[0]
        branch = next(node for node in function.body if isinstance(node,ast.If)
                      and ast.unparse(node.test)=='sealed'
                      and any(isinstance(child,ast.AugAssign) for child in node.body))
        entry = self.root/'Entries.v'
        entry.write_text('Definition entry_data := True.\n')
        self.profile_binding()
        namespace = dict(scratch.__dict__,sealed=True,PORT_KIND=P.PORT_KIND,
                         a=SimpleNamespace(admission_profile=self.profile_path),
                         additions=[],native=self.source,entry=entry,
                         workspace=self.root,modules={},overrides=[])
        exec(compile(ast.fix_missing_locations(ast.Module(body=[branch],type_ignores=[])),
                     '<actual-sealed-bindings>','exec'),namespace)
        self.assertEqual(namespace['additions'],[binding(self.source),binding(entry)])

    def test_unauthorized_block_refuses(self):
        self.raw['key'] = '800d6974'
        with self.assertRaisesRegex(ValueError,'case is not authorized'):
            self.workload()

    def test_unauthorized_module_refuses(self):
        self.raw['target']['module'] = 'Unapproved.Caller'
        with self.assertRaisesRegex(ValueError,'case is not authorized'):
            self.workload()

    def test_unauthorized_source_refuses(self):
        self.raw['target']['source_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'source or statement differs'):
            self.workload()

    def test_unauthorized_statement_refuses(self):
        self.raw['target']['statement_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'source or statement differs'):
            self.workload()

    def test_unauthorized_address_refuses(self):
        self.raw['target']['pc'] += 4
        with self.assertRaisesRegex(ValueError,'address differs'):
            self.workload()

    def test_private_job_route_refuses(self):
        self.raw['native_route'] = {'path':'private','sha256':'0'*64}
        with self.assertRaisesRegex(ValueError,'stock native search'):
            self.workload()

    def test_private_runtime_route_refuses(self):
        self.config['native_route'] = {'path':'private','sha256':'0'*64}
        with self.assertRaisesRegex(ValueError,'stock native search'):
            self.workload()

    def test_nonempty_setup_refuses(self):
        self.config['prerequisite_modules'] = ['Missing.Entry']
        with self.assertRaisesRegex(ValueError,'empty setup'):
            self.workload()

    def test_changed_staged_production_owner_refuses(self):
        different = self.root/'WrongAll.v'
        different.write_text('Definition changed := 0.\n')
        self.config['proof_runtime']['module_files']['ZesuSsz.Automation.All'] = str(different)
        with self.assertRaisesRegex(ValueError,'actual workload source differs'):
            self.workload()

    def test_nonstock_body_refuses_even_in_a_test_authority(self):
        self.source.write_text(self.source.read_text().replace('  zesu_block.','  idtac.'))
        self.case['source'] = binding(self.source)
        self.raw['target']['source_sha256'] = self.case['source']['sha256']
        self.authority_path.write_text(json.dumps(self.authority))
        self.accepted.update(binding(self.authority_path))
        self.profile['authority'] = dict(self.accepted)
        with self.assertRaisesRegex(ValueError,'native body changed'):
            self.workload()

    def test_unapproved_authority_refuses(self):
        self.profile['authority']['sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'not authorized'):
            self.workload()

    def test_diagnostic_label_cannot_replace_measured_mode(self):
        self.profile['memory_route'] = 'diagnostic'
        with self.assertRaisesRegex(ValueError,'profile is invalid'):
            self.workload()

    def test_real_guard_accepts_measured32_without_diagnostic_serialization(self):
        job = self.job()
        environment = {key:value for key,value in os.environ.items() if not key.startswith('ZESU_')}
        environment.update(P.environment('native',job['claim_bytes'],job=job),
                           ZESU_GUARD_STATE=str(self.root/'guard'),
                           ZESU_GATE_LOCK=str(self.root/'lock'),
                           ZESU_RUN_REGISTRY=str(self.root/'registry'))
        guard = Path(__file__).with_name('restart-tools')/'resource_guard.sh'
        library = guard.read_text().split('\nprune_scope_registry\n',1)[0]
        response = subprocess.run(['bash'],input=library+'\nvalidate_probe_scope || exit $?\n'
            'if diagnostic_probe; then exit 31; fi\n'
            'test "$MODULE_LIMIT_GIB" = 32\n',env=environment,capture_output=True,text=True)
        self.assertEqual(response.returncode,0,response.stderr)

    def test_old_declaration_and_unmeasured_stock_policies_stay_exact(self):
        declaration = P.apply_job({'phase':'prerequisites'})
        self.assertEqual(P.validate_job(declaration),24*P.GIB)
        self.assertEqual(declaration['physical_fence_bytes'],64*P.GIB)
        native = P.apply_job({'phase':'native','target':{}})
        self.assertEqual(P.validate_job(native),64*P.GIB)
        self.assertEqual(P.environment('native',native['claim_bytes'],job=native)['ZESU_PROBE_ISSUE'],'10')


if __name__ == '__main__':
    unittest.main()
