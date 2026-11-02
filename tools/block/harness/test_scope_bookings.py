"""Keep controller claims out of physical compiler and PET-capable sessions."""
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import scope_bookings as S
from entry_chain import binding, read_bound
import test_declaration_resources as Resources


class ScopeBookingTests(unittest.TestCase):
    def setUp(self):
        self.config = {'declarations_only': True, 'phase': 'prerequisites',
                       'declaration_checks': [], 'control_session': None, 'native_route': None}

    def test_approved_historical_peak_sizes_only_the_controller_role(self):
        selected = S.descriptor(self.config)
        self.assertEqual(selected['authority']['sha256'], S.AUTHORITY['sha256'])
        self.assertEqual(selected['client_claim_bytes'], S.GIB)
        self.assertEqual(selected['mcp_claim_bytes'], 24964177920)
        self.assertIn('not completed aggregate', selected['qualification'])

    def test_client_and_mcp_claims_keep_the_physical_fence(self):
        env = {'ZESU_MODULE_CLAIM_BYTES': str(32*S.GIB), 'ZESU_MODULE_LIMIT_GIB': '64'}
        client, selected = S.client_environment(self.config, {'phase': 'prerequisites'}, env)
        mcp, unused = S.mcp_environment(self.config, env)
        self.assertEqual(client['ZESU_MODULE_CLAIM_BYTES'], str(S.GIB))
        self.assertEqual(mcp['ZESU_MODULE_CLAIM_BYTES'], '24964177920')
        self.assertEqual(client['ZESU_MODULE_LIMIT_GIB'], '64')
        self.assertEqual(mcp['ZESU_MODULE_LIMIT_GIB'], '64')
        self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'], str(32*S.GIB))

    def test_control_native_and_verification_sessions_keep_their_job_booking(self):
        for fields in [{'phase':'native'}, {'control_session':{}},
                       {'declaration_checks':[{'check':'verification'}]}, {'declarations_only':False}]:
            with self.subTest(fields=fields):
                config = dict(self.config, **fields)
                config['canonical_admission']={'minimum_claim_bytes':8*S.GIB,'memory_job':{'phase':config['phase']}}
                env={'ZESU_CONTROLLER_ROLE':'entry-chain-client', 'ZESU_MODULE_CLAIM_BYTES':str(S.GIB)}
                with patch('memory_policy.environment', return_value={'ZESU_MODULE_CLAIM_BYTES':str(8*S.GIB)}):
                    result, selected = S.mcp_environment(config,env)
                self.assertIsNone(selected)
                self.assertNotIn('ZESU_CONTROLLER_ROLE', result)
                self.assertEqual(result['ZESU_MODULE_CLAIM_BYTES'], str(8*S.GIB))

    def test_controller_only_role_refuses_every_proof_tool(self):
        selected = S.descriptor(self.config)
        for tool in ['rocq_health', 'rocq_compile_file']:S.require_tool(selected,tool)
        for tool in ['rocq_start','rocq_check','rocq_verify','rocq_step_multi','unknown']:
            with self.subTest(tool=tool),self.assertRaisesRegex(ValueError,'proof command'):
                S.require_tool(selected,tool)
        S.require_tool(None,'rocq_start')

    def test_controller_client_refuses_kernel_and_changed_session_roles(self):
        env={'ZESU_CONTROLLER_ROLE':'entry-chain-client'}
        S.require_client(self.config,env)
        with self.assertRaisesRegex(ValueError,'kernel driver'):
            S.require_client(self.config,env,kernel_driver=True)
        with self.assertRaisesRegex(ValueError,'proof or kernel'):
            S.require_client(dict(self.config,phase='native'),env)
        with self.assertRaisesRegex(ValueError,'proof or kernel'):
            S.require_client(self.config,{'ZESU_CONTROLLER_ROLE':'entry-pilot-mcp'})
        S.require_client(dict(self.config,phase='native'),{})

    def test_physical_compiler_resets_controller_and_ambient_profiles(self):
        env={'ZESU_MODULE_CLAIM_BYTES':str(S.GIB),'ZESU_CONTROLLER_ROLE':'entry-pilot-mcp',
             'ZESU_CONTROLLER_AUTHORITY_SHA256':S.AUTHORITY['sha256'],
             'ZESU_MODULE_MEMORY_PROFILE':'unbound-profile','ZESU_MODULE_LIMIT_GIB':'32'}
        result=S.compiler_environment({}, {'path':'/unmeasured.v','sha256':'0'*64},env)
        self.assertEqual(result['ZESU_MODULE_CLAIM_BYTES'],str(16*S.GIB))
        self.assertEqual(result['ZESU_MODULE_LIMIT_GIB'],'32')
        self.assertNotIn('ZESU_CONTROLLER_ROLE',result)
        self.assertNotIn('ZESU_CONTROLLER_AUTHORITY_SHA256',result)
        self.assertNotIn('ZESU_MODULE_MEMORY_PROFILE',result)

    def resource_fixture(self, peak=900000):
        case=Resources.DeclarationResourceTests();case.setUp();self.addCleanup(case.doCleanups)
        profile=case.profile(peak=peak);f=case.f
        runtime=dict(f.runtime,ordered_modules=['Example.Control'],physical_compiler=binding(f.compiler),
                     declaration_dag={'profile':profile})
        resources=S.compiler_resources(runtime,{},f.root,f.root)
        runtime['compiler_scope_bookings']=resources
        return runtime,f,resources

    def test_authenticated_completed_module_peak_uses_exact_formula(self):
        runtime,f,resources=self.resource_fixture()
        expected=max(S.GIB,(900000*1024*3+1)//2)
        self.assertEqual(resources['weights']['Example.Control'],expected)
        env=S.compiler_environment(runtime,binding(f.source),{'ZESU_MODULE_CLAIM_BYTES':'1'})
        self.assertEqual(env['ZESU_MODULE_CLAIM_BYTES'],str(expected))

    def test_small_completed_module_keeps_one_gib_floor(self):
        runtime,f,resources=self.resource_fixture(peak=1)
        self.assertEqual(S.compiler_environment(runtime,binding(f.source),{})['ZESU_MODULE_CLAIM_BYTES'],str(S.GIB))

    def test_changed_resource_formula_or_flags_refuse(self):
        runtime,f,resources=self.resource_fixture()
        resources['weights']['Example.Control']=1
        with self.assertRaisesRegex(ValueError,'formula changed'):
            S.compiler_environment(runtime,binding(f.source),{})
        resources['physical_flags']=[]
        with self.assertRaisesRegex(ValueError,'context changed'):
            S.compiler_environment(runtime,binding(f.source),{})

    def test_unknown_verification_source_keeps_full_default(self):
        runtime,f,resources=self.resource_fixture()
        result=S.compiler_environment(runtime,{'path':str(f.root/'Verification.v'),'sha256':'0'*64},{'ZESU_MODULE_CLAIM_BYTES':'1'})
        self.assertEqual(result['ZESU_MODULE_CLAIM_BYTES'],str(16*S.GIB))

    def test_transport_audit_allows_only_the_exact_scoped_import(self):
        from transport_mapping import audit
        with tempfile.TemporaryDirectory() as name:
            path=Path(name)/'entry_chain_provider.py'
            path.write_text('from scope_bookings import descriptor\nselected=descriptor(runtime)\n')
            self.assertEqual(audit(path)['reviewed_sinks'][0]['module'],'scope_bookings')
            path.write_text('from unapproved import descriptor\nselected=descriptor(runtime)\n')
            with self.assertRaisesRegex(ValueError,'another source import'):audit(path)
            path.write_text('from scope_bookings import descriptor as unapproved_sink\nunapproved_sink(runtime)\n')
            with self.assertRaisesRegex(ValueError,'escapes'):audit(path)


if __name__=='__main__':unittest.main()
