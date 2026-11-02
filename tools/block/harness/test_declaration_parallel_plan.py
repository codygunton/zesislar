"""Check the public opt-in plan without creating a runtime or a claim."""
import argparse
from copy import deepcopy
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from declaration_parallel_plan import (arguments, attach, check_arguments,
                                       for_phase, inherit, validate)
from entry_chain import binding, save


GIB=1024**3


class PublicDagPlanTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        for name in ['A','B','C']:(self.root/(name+'.v')).write_text('(* Nonproof '+name+' fixture. *)\n')
        self.dune=self.root/'dune';self.dune.write_text('Nonexecutable Dune fixture.\n')
        graph=self.root/'GRAPH.json'
        save(graph,{'import_edges':[{'from':'Example.C','to':'Example.A'},
                                   {'from':'Example.C','to':'Example.B'}]})
        self.config={'declarations_only':True,'prepared_workspace':str(self.root),
            'effective_compiler_version':{'compiler':binding(self.dune)},'physical_flags':['-Q',str(self.root/'library'),'Library'],
            'cache_import_graph':binding(graph),
            'proof_runtime':{'module_files':{('Example.'+x):(x+'.v') for x in ['A','B','C']}},
            'jobs':[{'phase':'prerequisites','claim_bytes':64*GIB,'physical_fence_bytes':64*GIB,
                     'ordered_modules':['Example.A','Example.B','Example.C']}]}

    def attach(self,**options):
        with patch('declaration_parallel_plan.shutil.which',return_value=str(self.dune)):
            return attach(self.config,**options)

    def runtime(self,spec):
        return dict(self.config['proof_runtime'],phase='prerequisites',
            declaration_dag=spec,ordered_modules=self.config['jobs'][0]['ordered_modules'],
            physical_compiler=self.config['effective_compiler_version']['compiler'],physical_flags=self.config['physical_flags'],
            canonical_admission={'minimum_claim_bytes':64*GIB,'physical_fence_bytes':64*GIB})

    def test_serial_is_the_public_default(self):
        parser=argparse.ArgumentParser()
        arguments(parser);args=parser.parse_args([])
        self.assertFalse(args.parallel_declarations)
        self.assertEqual(args.declaration_workers,48)
        check_arguments(args,parser)
        self.assertIsNone(for_phase(self.config,'prerequisites',self.root))

    def test_public_plan_keeps_pair_and_dependent_consumer(self):
        spec=self.attach()
        self.assertEqual(spec['weights'],{name:16*GIB for name in ['Example.A','Example.B','Example.C']})
        self.assertEqual(spec['maximum_workers'],48)
        self.assertEqual(validate(self.runtime(spec),self.root),spec)

    def test_actual_READY_shape_needs_no_staged_compiler_field(self):
        self.assertNotIn('physical_compiler',self.config)
        with patch('shutil.which',return_value=str(self.dune)):
            spec=attach(self.config)
        self.assertEqual(validate(self.runtime(spec),self.root),spec)

    def test_existing_staged_identity_must_equal_the_effective_compiler(self):
        self.config['physical_compiler']=dict(binding(self.dune),sha256='0'*64)
        with self.assertRaisesRegex(ValueError,'bound effective identity'):
            self.attach()

    def test_matching_staged_identity_remains_supported(self):
        self.config['physical_compiler']=binding(self.dune)
        self.assertEqual(self.attach()['maximum_workers'],48)

    def test_ordinary_24_gib_profile_cannot_enable_parallel_execution(self):
        self.config['jobs'][0]['claim_bytes']=24*GIB
        with self.assertRaisesRegex(ValueError,'full-fence 64/64'):
            self.attach()

    def test_native_phase_never_receives_the_plan(self):
        self.attach()
        self.assertIsNone(for_phase(self.config,'native',self.root))
        self.config['declarations_only']=False
        with self.assertRaisesRegex(ValueError,'native execution'):
            for_phase(self.config,'prerequisites',self.root)

    def test_new_preparation_does_not_inherit_dispatch(self):
        spec=self.attach()
        self.config['proof_runtime']['declaration_dag']=deepcopy(spec)
        transition=inherit(self.config)
        self.assertEqual(transition['removed'],spec)
        self.assertNotIn('declaration_dag',self.config)
        self.assertNotIn('declaration_dag',self.config['proof_runtime'])

    def test_changed_source_refuses_before_dispatch(self):
        spec=self.attach()
        (self.root/'A.v').write_text('Changed nonproof source.\n')
        with self.assertRaisesRegex(ValueError,'source changed'):
            validate(self.runtime(spec),self.root)

    def test_changed_protected_set_refuses(self):
        spec=self.attach();spec['protected_modules']=['Example.A']
        with self.assertRaisesRegex(ValueError,'protected MCP barriers'):
            validate(self.runtime(spec),self.root)

    def test_native_tactic_refuses_the_public_plan(self):
        (self.root/'A.v').write_text('Proof. zesu_block. Qed.\n')
        with self.assertRaisesRegex(ValueError,'native proof'):
            self.attach()

    def test_real_stage_relocates_source_bindings(self):
        self.attach();staged=self.root/'staged';staged.mkdir()
        spec=for_phase(self.config,'prerequisites',staged)
        self.assertEqual(spec['sources'][0]['source']['path'],str(staged/'A.v'))
        self.assertEqual(self.config['declaration_dag']['sources'][0]['source']['path'],str(self.root/'A.v'))

    def test_worker_override_requires_opt_in(self):
        parser=argparse.ArgumentParser();arguments(parser)
        for values in [['--declaration-workers','1'],['--parallel-declarations','--declaration-workers','49']]:
            with self.subTest(values=values),self.assertRaises(SystemExit):
                check_arguments(parser.parse_args(values),parser)

    def test_missing_policy_refuses_before_harness_or_graph_construction(self):
        import scratch
        args=SimpleNamespace(normalization_policy=None,target_adapter=self.root/'ADAPTER.json',rules=None)
        with patch('command_scope.require'),patch('harness_commit.pin',side_effect=AssertionError('Unexpected harness work.')):
            with self.assertRaisesRegex(ValueError,'explicit database policy'):
                scratch.prepare(args)

    def test_reviewed_empty_policy_passes_cheap_preflight(self):
        import scratch
        policy=self.root/'POLICY.json'
        value={'hook_enabled':False,'database':'zesu_entry_normalize','registrations':[]}
        save(policy,value)
        self.assertEqual(scratch.checked_normalization_policy(SimpleNamespace(
            normalization_policy=policy,target_adapter=self.root/'ADAPTER.json',rules=None)),value)

    def test_malformed_policy_refuses_before_graph_construction(self):
        import scratch
        policy=self.root/'POLICY.json';save(policy,{'database':'zesu_entry_normalize'})
        with self.assertRaisesRegex(ValueError,'normalization policy is invalid'):
            scratch.checked_normalization_policy(SimpleNamespace(
                normalization_policy=policy,target_adapter=self.root/'ADAPTER.json',rules=None))


if __name__=='__main__':unittest.main()
