"""Check the guarded adapter without running a compiler or accessing a ledger."""
import subprocess
from pathlib import Path
import unittest
import uuid

import compiler_snapshot as S
from declaration_outputs import GIB
from declaration_parallel import GuardedAdapter
from entry_chain import binding
from source_context import compilation
import test_declaration_outputs as fixtures


class GuardedAdapterTests(unittest.TestCase):
    def setUp(self):
        self.case = fixtures.DeclarationOutputTests()
        self.case.configure = self.configure
        self.case.setUp()
        self.addCleanup(self.case.doCleanups)
        self.f = self.case.f
        self.output = self.f.root / 'provider'
        self.output.mkdir()
        self.launches = []

    def configure(self, f):
        wrapper = f.root / 'tools/entry_chain_coqc.sh'
        wrapper.parent.mkdir()
        wrapper.write_text('Nonexecutable wrapper fixture.\n')
        dune = f.compiler.with_name('dune')
        dune.write_text('Nonexecutable Dune fixture.\n')
        f.runtime.update(coqc_wrapper='tools/entry_chain_coqc.sh',
                         build_dir='artifacts', expected_mcp_flags=['-fixture'], job_output=str(f.root))
        f.runtime['ordered_modules'] = ['Example.Control']
        from declaration_parallel_plan import attach
        from unittest.mock import patch
        config={'declarations_only':True,'jobs':[dict(phase='prerequisites',
            claim_bytes=64*GIB,physical_fence_bytes=64*GIB,ordered_modules=['Example.Control'])],
            'prepared_workspace':str(f.root),'proof_runtime':{'module_files':f.runtime['module_files']},
            'cache_import_graph':f.runtime['cache_import_graph'],'physical_compiler':binding(f.compiler),
            'physical_flags':f.runtime['physical_flags']}
        with patch('declaration_parallel_plan.shutil.which',return_value=str(dune)):
            f.runtime['declaration_dag']=attach(config)
        f.runtime['bindings'].extend([binding(wrapper), binding(dune)])

    def physical_runner(self, command, **keywords):
        self.launches.append((command, keywords))
        f = self.f
        target, source = Path(command[-2]), Path(command[-1])
        source_binding, compiler = binding(source), binding(f.compiler)
        report = S.validate_compiler(f.runtime, f.reference, self.case.snapshot,
                                    source_binding, f.compiler, output_key=self.case.manager.key,
                                    private_output=target, private_workspace=f.root)
        report['import_selection'] = S.import_selection(f.runtime, source_binding, f.root, report)
        directory = f.root / 'compiler-invocations' / uuid.uuid4().hex
        directory.mkdir(parents=True)
        before = S.sidecar_prestate(source_binding, target, compiler, report['physical_flags'], report)
        target.write_bytes(b'Nonproof private object.')
        target.with_suffix('.vos').write_bytes(b'')
        target.with_suffix('.glob').write_text('\nFExample.Control\n')
        argv = [compiler['path'], *report['physical_flags'], '-o', str(target), str(source)]
        validation = S._publish(directory / 'PHYSICAL-VALIDATION.json', report)
        inputs = S._publish(directory / 'INPUT.json', {
            'source': source_binding, 'compiler': compiler, 'owned_workspace': str(f.root),
            'target': {'module': 'Example.Control'}, 'physical_argv': argv,
            'compiler_context': compilation(f.runtime['physical_flags'], source_binding),
            'output_context': report['output_context'],
            'sidecar_prestate': before,
            'validation': {'runtime': f.reference, 'snapshot': self.case.snapshot}})
        S._publish(directory / 'PHYSICAL-RESULT.json', {
            'input': inputs, 'input_validation': validation, 'physical_argv': argv,
            'returncode': 0, 'output_capture': {'complete': True}, 'output_validation': {'success': True},
            'compiler_outputs': S.compiler_outputs(target, before)})
        return subprocess.CompletedProcess(command, 0)

    def adapter(self, runner=None):
        return GuardedAdapter(self.f.runtime, self.f.root, self.output, self.case.manager,
                              {'ZESU_COQC_SCOPE': 'outer', 'ZESU_COQC_RESERVATION': 'outer-token'},
                              lambda: None, lambda name: self.fail('Unexpected protected compile.'),
                              runner=runner or self.physical_runner)

    def test_guarded_private_result_reaches_the_accepted_dependency_receipt(self):
        adapter = self.adapter()
        result = adapter.execute(lambda: 256 * GIB)
        self.assertEqual(list(result['receipts']), ['Example.Control'])
        self.assertEqual(len(self.case.manager.rows), 1)
        self.assertTrue((self.output / 'dependency-Example.Control.json').is_file())
        command, options = self.launches[0]
        self.assertEqual(command[:2], [self.f.runtime['declaration_dag']['dune']['path'], 'exec'])
        self.assertIn('--no-build', command)
        self.assertNotIn('ZESU_COQC_SCOPE', options['env'])
        self.assertNotIn('ZESU_COQC_RESERVATION', options['env'])
        self.assertEqual(options['env']['ZESU_MODULE_CLAIM_BYTES'], str(16*GIB))
        self.assertEqual(options['env']['ZESU_MODULE_LIMIT_GIB'], '64')
        self.assertTrue(Path(command[-2]).is_relative_to(self.f.root / '.declaration-private'))

    def test_failed_guarded_compiler_never_publishes(self):
        def refuse(command, **keywords):
            self.launches.append(command)
            return subprocess.CompletedProcess(command, 2)
        with self.assertRaises(RuntimeError):
            self.adapter(refuse).execute(lambda: 256 * GIB)
        self.assertEqual(len(self.launches), 1)
        self.assertEqual(self.case.manager.rows, [])
        self.assertFalse(self.f.source.with_suffix('.vo').exists())

    def test_changed_wrapper_refuses_before_launch(self):
        adapter = self.adapter()
        (self.f.root / self.f.runtime['coqc_wrapper']).write_text('Changed wrapper.\n')
        with self.assertRaisesRegex(ValueError, 'tool changed'):
            adapter.compile_private('Example.Control')
        self.assertEqual(self.launches, [])

    def test_protected_declaration_cannot_enter_a_worker(self):
        adapter = self.adapter()
        adapter.protected.add('Example.Control')
        with self.assertRaisesRegex(ValueError, 'protected declaration'):
            adapter.compile_private('Example.Control')
        self.assertEqual(self.launches, [])

    def test_missing_physical_result_cannot_publish_a_successful_runner(self):
        def no_record(command, **keywords):
            Path(command[-2]).write_bytes(b'Unverified object.')
            return subprocess.CompletedProcess(command, 0)
        with self.assertRaises(RuntimeError):
            self.adapter(no_record).execute(lambda: 256 * GIB)
        self.assertEqual(self.case.manager.rows, [])
        self.assertFalse(self.f.source.with_suffix('.vo').exists())


if __name__ == '__main__':
    unittest.main()
