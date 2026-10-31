"""Test the actual native transport without starting a compiler, perf, or MCP."""
import ast
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import test_telemetry as T
import dependency_batch as D
import test_dependency_batch as dependency_tests
import transport_mapping as M
import collector
import native_instruction_profile as P


def save(path, value):
    path.write_text(json.dumps(value) + '\n')
    return D.binding(path)


class AuditControls(unittest.TestCase):
    def test_actual_source014_consumers_pass_without_new_sinks(self):
        for name in ['entry_chain_provider.py', 'entry_chain_compiler.py', 'entry_chain_resources.py']:
            report = M.audit(T.HERE / 'code' / name)
            self.assertEqual(report['unmapped_fields'], [])
        report = M.audit(T.HERE / 'code/entry_chain_provider.py')
        self.assertEqual(sum(row['field'] == 'dependency_batch' for row in report['field_reads']), 2)
        self.assertEqual(M.KNOWN_SINKS, {'check_operation', 'proof_environment',
            'prerequisite_environment', 'check_proof_bindings', 'validate_runtime'})

    def test_all_original_runtime_escapes_still_refuse(self):
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / 'consumer.py'
            for source in ['profile_launcher(runtime,row,workspace,output,launcher)',
                           'validate_dependency_batch(runtime,workspace,ordered,spec)',
                           'asyncio.to_thread(run_wave,0,runtime,workspace,output,ordered,done,env)']:
                path.write_text(source)
                with self.assertRaisesRegex(ValueError, 'escapes'):
                    M.audit(path)

    def test_literal_eight_field_projection_and_disabled_feature(self):
        tree = ast.parse((T.HERE / 'code/entry_chain_provider.py').read_text())
        execute = next(node for node in tree.body if isinstance(node, ast.AsyncFunctionDef) and node.name == 'execute')
        selected = next(node.value for node in ast.walk(execute) if isinstance(node, ast.Assign)
                        and any(isinstance(target, ast.Name) and target.id == 'dependency_context' for target in node.targets))
        self.assertIsInstance(selected, ast.Dict)
        self.assertEqual([ast.literal_eval(key) for key in selected.keys],
                         ['phase', 'canonical_admission', 'native_route', 'control_session',
                          'physical_flags', 'module_files', 'build_dir', 'dependency_batch'])
        self.assertEqual(M.FIELD_MAPPING['dependency_batch'], ['recipe.backend.features.dependency_waves_disabled'])

    def test_projection_validation_keeps_the_existing_wave_validator(self):
        fixture = dependency_tests.DependencyBatchTests('test_valid_exact_plan')
        fixture.setUp()
        try:
            context = {key: fixture.runtime.get(key) for key in
                       ['phase', 'canonical_admission', 'native_route', 'control_session',
                        'physical_flags', 'module_files', 'build_dir']}
            context['dependency_batch'] = fixture.spec
            self.assertEqual(len(D.validate_projection(context, fixture.workspace,
                                                      fixture.ordered, fixture.spec)[0]['modules']), 23)
            for broken in [dict(context, arbitrary=True), dict(context, dependency_batch=None)]:
                with self.assertRaises(ValueError):
                    D.validate_projection(broken, fixture.workspace, fixture.ordered, fixture.spec)
        finally:
            fixture.doCleanups()


class SelectedTransport(T.Fixture):
    def setUp(self):
        super().setUp()
        self.workspace = self.root / 'workspace'
        self.workspace.mkdir()
        self.native = self.output / 'native'
        self.prospective = self.output / 'prospective'
        self.prospective.mkdir()
        self.base = ['mcp-python', '-B', 'mcp-server']
        self.fake = T.LauncherTests.fake_perf(self)
        self.perf = Path(self.fake['path'])
        self.library = self.root / 'libfixture.so'
        self.library.write_bytes(b'fixture dependency; never executed')
        pin = patch.object(P, 'PERF', self.fake)
        pin.start()
        self.addCleanup(pin.stop)

    def prepared(self):
        measurement = dict(command=[str(self.perf), 'stat', '--', *self.base],
            workload_command=self.base, cwd=str(self.workspace),
            perf_stat=str(self.directory / 'perf-stat.csv'), cache_removals=[])
        def libraries(path, *args):
            return dict(ordered_libraries=([dict(path=str(self.library), soname='fixture')]
                        if Path(path) == self.perf else []), unresolved_edges=[])
        with patch.object(P, 'prepare', return_value=measurement), \
             patch.object(P.shutil, 'which', return_value=str(self.perf)), \
             patch.object(collector, 'libraries', side_effect=libraries):
            return P.prepare_launch(self.job, {'block': self.case}, self.workspace,
                                    self.native, self.base, {'PATH': '/usr/bin'})

    def transport(self, plan):
        selected = save(self.prospective / 'MCP-LAUNCH.json', plan)
        vector = dict(role='mcp', cwd=dict(kind='path', value=str(self.workspace)),
                      argv=[dict(kind='path' if word.startswith('/') else 'literal', value=word)
                            for word in plan['argv']])
        report = dict(input=dict(recipe=dict(configuration=dict(execution_vectors=[vector]))),
                      native_profile_transport=selected)
        second = save(self.prospective / 'PHASE2.json', report)
        save(self.prospective / 'ACTUAL-BOUNDARY.json', dict(mcp_launch=selected, phase2=second))
        return report

    def consume(self):
        return P.checked_launcher(self.job, {'block': self.case}, self.workspace,
                                  self.native, self.base, self.prospective)

    def test_selected_vector_and_complete_executable_inputs(self):
        plan = self.prepared()
        self.assertEqual(plan['argv'], [str(self.perf), 'stat', '--interval-print', '1000', '--', *self.base])
        self.assertEqual({row['path'] for row in plan['executable_inputs']},
                         {'/usr/bin/ldd', str(self.perf), str(self.library)})
        self.transport(plan)
        with patch.object(P, 'prepare_launch', side_effect=AssertionError('No reselection')):
            self.assertEqual(self.consume(), (plan['argv'], plan['measurement']))

    def test_missing_perf_retains_exact_unprofiled_vector(self):
        with patch.object(P, 'prepare', side_effect=OSError('unavailable')):
            plan = P.prepare_launch(self.job, {'block': self.case}, self.workspace,
                                    self.native, self.base, {'PATH': '/usr/bin'})
        self.assertEqual(plan['argv'], self.base)
        self.assertEqual(plan['executable_inputs'], [])
        self.transport(plan)
        self.assertEqual(self.consume(), (self.base, None))

    def test_loader_resolution_failure_is_optional(self):
        with patch.object(P, 'profile_launcher', return_value=([str(self.perf)], {'unused': True})), \
             patch.object(P.shutil, 'which', return_value=str(self.perf)), \
             patch.object(collector, 'libraries', side_effect=ValueError('unresolved')):
            plan = P.prepare_launch(self.job, {'block': self.case}, self.workspace,
                                    self.native, self.base, {'PATH': '/usr/bin'})
        self.assertEqual(plan['argv'], self.base)
        self.assertEqual(plan['executable_inputs'], [])
        self.assertIsNone(plan['measurement'])

    def test_changed_executable_or_dependency_refuses_without_reselection(self):
        for path in [self.perf, self.library]:
            plan = self.prepared()
            self.transport(plan)
            original = path.read_bytes()
            path.write_bytes(b'changed')
            try:
                with self.assertRaises(ValueError):
                    self.consume()
            finally:
                path.write_bytes(original)

    def test_unkeyed_argv_change_refuses(self):
        plan = self.prepared()
        report = self.transport(plan)
        plan['argv'].append('--unkeyed')
        selected = save(self.prospective / 'MCP-LAUNCH.json', plan)
        report['native_profile_transport'] = selected
        second = save(self.prospective / 'PHASE2.json', report)
        save(self.prospective / 'ACTUAL-BOUNDARY.json', dict(mcp_launch=selected, phase2=second))
        with self.assertRaisesRegex(ValueError, 'typed execution vector'):
            self.consume()

    def test_foreign_launch_file_refuses(self):
        plan = self.prepared()
        self.transport(plan)
        boundary = json.loads((self.prospective / 'ACTUAL-BOUNDARY.json').read_text())
        boundary['mcp_launch'] = save(self.root / 'foreign.json', plan)
        save(self.prospective / 'ACTUAL-BOUNDARY.json', boundary)
        with self.assertRaisesRegex(ValueError, 'another selection file'):
            self.consume()

    def test_non_port_plan_retains_original_launcher(self):
        plan = P.prepare_launch(None, {}, self.workspace, self.native, self.base, {'PATH': '/usr/bin'})
        self.assertEqual(plan['argv'], self.base)
        self.assertEqual(plan['executable_inputs'], [])
        self.assertIsNone(plan['case'])

class RefreshContextControls(unittest.TestCase):
    def context(self, modules):
        return dict(jobs=[dict(phase='prerequisites', ordered_modules=modules),dict(phase='native')],
                    proof_runtime=dict(module_files={'A':'A.v','B':'B.v'}), prerequisite_modules=[])

    def test_context_uses_the_actual_list(self):
        import scratch
        context=self.context(['A','B'])
        selected=scratch.memory_workload_context(context)
        self.assertEqual(selected['prerequisite_modules'],['A','B'])
        self.assertEqual(context['prerequisite_modules'],[])

    def test_context_refuses_missing_duplicate_and_unknown_modules(self):
        import scratch
        for modules in [None,['A','A'],['unknown'],[1]]:
            with self.assertRaises(ValueError):
                scratch.memory_workload_context(self.context(modules))

    def test_context_requires_one_actual_prerequisite_job(self):
        import scratch
        for jobs in [[],[dict(phase='native')],
                     [dict(phase='prerequisites',ordered_modules=[])]*2]:
            with self.assertRaises(ValueError):
                scratch.memory_workload_context(dict(jobs=jobs,proof_runtime=dict(module_files={})))


class RefreshNamespaceControls(unittest.TestCase):
    def refresh(self, previous, current):
        import scratch
        tree=ast.parse((T.HERE/'scratch.py').read_text())
        function=next(node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name=='refresh_memory')
        selected=[]
        for node in function.body:
            target=node.targets[0] if isinstance(node,ast.Assign) else node.target if isinstance(node,ast.AugAssign) else None
            if (isinstance(target,ast.Subscript) and isinstance(target.value,ast.Name)
                    and target.value.id=='producers' and isinstance(target.slice,ast.Constant)
                    and target.slice.value=='inputs'):
                selected.append(node)
        self.assertEqual(len(selected),2)
        namespace=dict(producers={'inputs':previous},measurements={'path':'current-measurement','sha256':'m'},
                       context={'path':'current-profile','sha256':'p'},memory_inputs=current)
        exec(compile(ast.fix_missing_locations(ast.Module(body=selected,type_ignores=[])),
                     '<actual-refresh-memory-inputs>','exec'),namespace)
        return namespace['producers']['inputs']

    def test_profile_change_replaces_only_the_owned_namespace(self):
        original=[dict(id='memory-evidence:0',path='old-authority',sha256='old',kind='configuration'),
                  dict(id='source-input',path='required-source',sha256='source',kind='source')]
        result=self.refresh(original,[dict(path='new-authority',sha256='new')])
        self.assertEqual(next(row for row in result if row['id']=='memory-evidence:0')['path'],'new-authority')
        self.assertIn(original[1],result)
        self.assertEqual(original[0]['path'],'old-authority')

    def test_repeated_refresh_has_unique_current_evidence_ids(self):
        first=self.refresh([], [dict(path='authority-one',sha256='one')])
        second=self.refresh(first,[dict(path='authority-two',sha256='two')])
        third=self.refresh(second,[dict(path='authority-two',sha256='two')])
        self.assertEqual(second,third)
        self.assertEqual(len({row['id'] for row in third}),len(third))
        self.assertNotIn('authority-one',{row['path'] for row in third})


if __name__ == '__main__':
    unittest.main()
