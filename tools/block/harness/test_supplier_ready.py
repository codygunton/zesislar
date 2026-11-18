"""Exercise supplier evidence and transport without a compiler or admission."""
from copy import deepcopy
import ast
import hashlib
import inspect
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import memory_policy as policy
import scratch
import supplier_ready as supplier


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class SupplierReady(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / 'jobs/prerequisites'
        self.workspace = self.root / 'prepared'
        self.names = sorted(supplier.ROOTS)
        self.mapping, self.modules = {}, []
        for name in self.names + ['Library.Dependency']:
            path = self.workspace / (name.replace('.', '/') + '.v')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('(* fixture ' + name + ' *)\n')
            path.with_suffix('.vo').write_bytes(('object ' + name).encode())
            self.mapping[name] = str(path.relative_to(self.workspace))
            self.modules.append(dict(module=name, source=binding(path),
                                     object=binding(path.with_suffix('.vo'))))
        self.graph = self.save('GRAPH.json', {'import_edges': [
            {'from': name, 'to': 'Library.Dependency'} for name in self.names]})
        self.specification = dict(problem_name='control', problem_statement='Lemma control : True.',
                                  proof='Lemma control : True. Proof. exact I. Qed.')
        success = dict(success=True)
        self.health = dict(success=True, ok=True, toolchain=dict(coqc=dict(version='fixture compiler')))
        self.calls = [self.call('rocq_health', {}, self.health)]
        for row in self.modules[:3]:
            receipt = dict(source=row['source']['path'], source_sha256=row['source']['sha256'],
                           object=row['object']['path'], object_sha256=row['object']['sha256'],
                           result=success)
            self.save('jobs/prerequisites/native/dependency-' + row['module'] + '.json', receipt)
            self.calls.append(self.call('rocq_compile_file', {'file': row['source']['path']}, success))
        self.verified = dict(success=True, verification_method='module_m', assumptions=[])
        self.calls.append(self.call('rocq_verify', dict(self.specification, workspace=str(self.workspace),
                                                      timeout=100), self.verified))
        self.calls.append(self.call('rocq_health', {}, self.health))
        self.calls_binding = self.save('jobs/prerequisites/native/CALLS.json', self.calls)
        self.verification = self.save('jobs/prerequisites/native/CONTROL-VERIFICATION.json',
                                     [dict(specification=self.specification, result=self.verified)])
        self.job_result = self.save('jobs/prerequisites/RESULT.json', dict(
            success=True, status='passed', returncode=0))
        self.readiness = self.save('READINESS.json', dict(
            schema='entry-chain.prerequisite-readiness.v1', all_required_compiles_passed=True,
            objects=[row['object'] for row in self.modules[:3]], prerequisite_result=self.job_result))
        self.compiler = dict(text='fixture compiler', compiler=self.file('coqc', b'compiler'),
                             evidence=self.save('VERSION.json', dict(version='fixture compiler')))
        self.flags = ['-Q', str(self.workspace / 'Library'), 'Library']
        self.ready = dict(declarations_only=True, control_session=None,
                          prepared_workspace=str(self.workspace),
                          proof_runtime=dict(module_files=self.mapping),
                          jobs=[dict(phase='prerequisites', output=str(self.output),
                                     ordered_modules=self.names, claim_bytes=24 * policy.GIB)],
                          readiness=self.readiness, cache_import_graph=self.graph,
                          declaration_checks=[self.specification],
                          bindings=[row[kind] for row in self.modules for kind in ['source', 'object']],
                          expected_mcp_flags=self.flags, physical_flags=self.flags,
                          effective_compiler_version=self.compiler)
        self.ready_binding = self.save('READY-RUNTIME.json', self.ready)
        self.inner = dict(phase='prerequisites', job_output=str(self.output),
                          prepared_workspace=str(self.workspace), ordered_modules=self.names,
                          declaration_checks=[self.specification],
                          expected_mcp_flags=self.flags, physical_flags=self.flags)
        self.manifest = dict(
            ready=self.ready_binding,
            source_packet=self.save('SOURCE.json', dict(all_sources=[
                dict(row['source'], module=row['module']) for row in self.modules[:3]])),
            modules=self.modules[:3], import_graph=self.graph,
            expected_mcp_flags=self.flags, physical_flags=self.flags,
            effective_compiler_version=self.compiler, verification=self.verification,
            calls=self.calls_binding,
            result=self.save('RESULT.json', dict(success=True, status='declarations_passed',
                native_calls=0, prerequisites=self.job_result, exact_statement_checks=self.verification,
                exact_statement_check_count=1)),
            runtime=self.save('jobs/prerequisites/RUNTIME.json', self.inner),
            closure=self.save('jobs/prerequisites/CLOSURE.json', dict(all_owned_actors_closed=True,
                actors=[dict(ended=True)], claim_key='supplier')),
            release=self.save('jobs/prerequisites/RELEASE.json', dict(released=True,
                bytes=24 * policy.GIB, claim_key='supplier')))

    def save(self, relative, value):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))
        return binding(path)

    def file(self, relative, value):
        path = self.root / relative
        path.write_bytes(value)
        return binding(path)

    def call(self, name, arguments, value):
        return dict(tool=name, arguments=arguments, result=deepcopy(value),
                    raw_response=dict(structuredContent=deepcopy(value)))

    def freeze(self):
        return self.save('SUPPLIER.json', self.manifest)

    def validate(self):
        return supplier.validate(self.freeze())

    def change(self, field, **values):
        row = self.manifest[field]
        data = json.loads(Path(row['path']).read_text())
        data.update(values)
        self.manifest[field] = self.save(str(Path(row['path']).relative_to(self.root)), data)

    def config(self):
        return dict(proof_runtime=dict(module_files=deepcopy(self.mapping)),
                    prepared_workspace=str(self.workspace), expected_mcp_flags=list(self.flags),
                    physical_flags=list(self.flags), effective_compiler_version=deepcopy(self.compiler),
                    cache_import_graph=self.graph, declarations_only=False, prerequisite_modules=[])

    def test_completed_supplier_and_exact_staged_closure_pass(self):
        value = self.validate()
        self.assertEqual(len(supplier.staged(value, self.config())), 4)
        self.assertEqual(value['names'], set(self.mapping))

    def test_missing_receipt_refuses(self):
        del self.manifest['closure']
        with self.assertRaisesRegex(ValueError, 'manifest fields'):
            self.validate()

    def test_changed_manifest_refuses(self):
        row = self.freeze()
        Path(row['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'input changed'):
            supplier.validate(row)

    def test_changed_root_or_dependency_source_and_object_refuse(self):
        for index in [0, 3]:
            for kind in ['source', 'object']:
                path = Path(self.modules[index][kind]['path'])
                previous = path.read_bytes()
                path.write_bytes(previous + b'changed')
                with self.subTest(index=index, kind=kind), self.assertRaisesRegex(ValueError, 'input changed'):
                    self.validate()
                path.write_bytes(previous)

    def test_changed_graph_binding_refuses(self):
        self.manifest['import_graph'] = self.save('OTHER-GRAPH.json', dict(import_edges=[]))
        with self.assertRaisesRegex(ValueError, 'graph binding'):
            self.validate()

    def test_changed_compiler_or_flags_refuse(self):
        for field in ['expected_mcp_flags', 'physical_flags', 'effective_compiler_version']:
            previous = deepcopy(self.manifest[field])
            self.manifest[field] = [] if field.endswith('flags') else dict(text='other')
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'differs'):
                self.validate()
            self.manifest[field] = previous

    def test_changed_compiler_executable_refuses(self):
        Path(self.compiler['compiler']['path']).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'input changed'):
            self.validate()

    def test_changed_plugin_refuses_and_retains_binding(self):
        plugin = self.file('fixture.cmxs', b'plugin')
        self.ready['bindings'].append(plugin)
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        self.assertIn(plugin, self.validate()['bindings'])
        Path(plugin['path']).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'input changed'):
            self.validate()

    def test_health_version_mismatch_refuses(self):
        changed = deepcopy(self.calls)
        changed[-1] = self.call('rocq_health', {}, dict(self.health, toolchain=dict(coqc=dict(version='other'))))
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', changed)
        with self.assertRaisesRegex(ValueError, 'health compiler version'):
            self.validate()

    def test_extra_proof_or_compile_call_refuses(self):
        for call in [self.call('rocq_check', dict(body='zesu_block.'), dict(success=True)), self.calls[1]]:
            changed = self.calls[:-1] + [call, self.calls[-1]]
            self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', changed)
            with self.assertRaisesRegex(ValueError, 'another proof operation|compile call count'):
                self.validate()

    def test_incomplete_job_or_outer_result_refuses(self):
        self.change('result', success=False)
        with self.assertRaisesRegex(ValueError, 'outer result'):
            self.validate()

    def test_unfinished_verification_refuses(self):
        self.change('result', exact_statement_check_count=2)
        with self.assertRaisesRegex(ValueError, 'unfinished'):
            self.validate()

    def test_assumptions_or_fallback_verification_refuse(self):
        for result in [dict(self.verified, assumptions=['axiom']),
                       dict(self.verified, verification_method='shared_defs')]:
            previous = self.manifest['verification']
            self.manifest['verification'] = self.save('jobs/prerequisites/native/CONTROL-VERIFICATION.json',
                [dict(specification=self.specification, result=result)])
            self.change('result', exact_statement_checks=self.manifest['verification'])
            with self.assertRaisesRegex(ValueError, 'exact verification'):
                self.validate()
            self.manifest['verification'] = previous

    def test_changed_specification_refuses(self):
        changed = deepcopy(self.calls)
        changed[-2]['arguments']['proof'] += '\n'
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', changed)
        with self.assertRaisesRegex(ValueError, 'exact verification'):
            self.validate()

    def test_failed_initial_or_final_health_refuses(self):
        for index in [0, -1]:
            changed = deepcopy(self.calls)
            changed[index] = self.call('rocq_health', {}, dict(success=True, ok=False))
            self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', changed)
            with self.subTest(index=index), self.assertRaisesRegex(ValueError, 'health check'):
                self.validate()

    def test_open_actor_or_missing_release_refuses(self):
        self.change('closure', actors=[dict(ended=False)])
        with self.assertRaisesRegex(ValueError, 'closure or claim release'):
            self.validate()
        self.change('closure', actors=[dict(ended=True)])
        self.change('release', released=False)
        with self.assertRaisesRegex(ValueError, 'closure or claim release'):
            self.validate()

    def test_wrong_release_claim_refuses(self):
        self.change('release', claim_key='other')
        with self.assertRaisesRegex(ValueError, 'closure or claim release'):
            self.validate()

    def test_actual_runtime_flag_change_refuses(self):
        self.change('runtime', physical_flags=['-R', str(self.workspace / 'Library'), 'Library'])
        with self.assertRaisesRegex(ValueError, 'actual compiler flags'):
            self.validate()

    def test_staged_graph_change_refuses(self):
        value = self.validate()
        config = self.config()
        config['cache_import_graph'] = self.save('STAGED-GRAPH.json', dict(import_edges=[]))
        with self.assertRaisesRegex(ValueError, 'staged import closure'):
            supplier.staged(value, config)

    def test_staged_object_change_refuses(self):
        value = self.validate()
        Path(self.modules[0]['object']['path']).write_bytes(b'other object')
        with self.assertRaisesRegex(ValueError, 'input changed'):
            supplier.staged(value, self.config())

    def test_staged_compiler_or_flags_change_refuses(self):
        value = self.validate()
        for field in ['expected_mcp_flags', 'physical_flags', 'effective_compiler_version']:
            config = self.config()
            config[field] = [] if field.endswith('flags') else dict(text='other')
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'staged .* differs'):
                supplier.staged(value, config)

    def test_owned_workspace_relocation_passes(self):
        value = self.validate()
        relocated = self.root / 'relocated'
        for row in self.modules:
            for kind in ['source', 'object']:
                old = Path(row[kind]['path'])
                new = relocated / old.relative_to(self.workspace)
                new.parent.mkdir(parents=True, exist_ok=True)
                new.write_bytes(old.read_bytes())
        config = self.config()
        config['prepared_workspace'] = str(relocated)
        for field in ['expected_mcp_flags', 'physical_flags']:
            config[field] = [word.replace(str(self.workspace), str(relocated)) for word in self.flags]
        self.assertEqual(len(supplier.staged(value, config)), 4)

    def test_profile_retains_named_manifest_and_complete_evidence(self):
        authority = policy.read(policy.PORT_AUTHORITY)
        profile = dict(schema='scratch.admission-profile.v1', kind=policy.PORT_KIND,
                       authority=deepcopy(policy.PORT_AUTHORITY), memory_route='measured_native',
                       supplier_ready=self.freeze())
        context = self.save('PROFILE.json', profile)
        values = policy.profile_bindings(context)
        for row in [profile['supplier_ready'], self.manifest['ready'], self.manifest['verification'],
                    self.manifest['calls'], self.manifest['runtime'], self.manifest['closure'],
                    self.manifest['release'], self.graph, self.compiler['compiler'],
                    self.modules[3]['object']]:
            self.assertIn(row, values)
        selected = policy.production_port_authority(profile)
        self.assertEqual(selected['cases'], authority['cases'])
        self.assertEqual(selected['cpu_policy'], authority['cpu_policy'])
        self.assertEqual({row['sha256'] for row in selected['production_sources']},
                         {row['source']['sha256'] for row in self.modules[:3]})

    def test_all_twenty_two_workloads_keep_claim_fence_and_revalidate_supplier(self):
        profile = dict(schema='scratch.admission-profile.v1', kind=policy.PORT_KIND,
                       authority=deepcopy(policy.PORT_AUTHORITY), memory_route='measured_native',
                       supplier_ready=self.freeze())
        context = self.save('PROFILE.json', profile)
        authority = policy.production_port_authority(profile)
        for case in authority['cases']:
            config = self.config()
            config['proof_runtime']['module_files'][case['module']] = case['source']['path']
            job = dict(key=case['block'], phase='native', ordered_modules=[], target=dict(
                module=case['module'], pc=case['pc'], source_sha256=case['source']['sha256'],
                statement_sha256=case['statement_sha256']))
            workload = policy.workload_for_job(context, job, config)
            value = policy.apply_job(job, workload=workload)
            with self.subTest(case=case['block']):
                self.assertEqual(policy.validate_job(value), 8 * policy.GIB)
                self.assertEqual(value['physical_fence_bytes'], 32 * policy.GIB)

    def test_unapproved_case_still_refuses_with_supplier(self):
        profile = dict(schema='scratch.admission-profile.v1', kind=policy.PORT_KIND,
                       authority=deepcopy(policy.PORT_AUTHORITY), memory_route='measured_native',
                       supplier_ready=self.freeze())
        with self.assertRaisesRegex(ValueError, 'case is not authorized'):
            policy.production_port_case(profile, dict(key='800d6974', phase='native',
                target=dict(module='Unapproved.Caller')))

    def test_actual_prepare_and_refresh_blocks_retain_manifest(self):
        profile = dict(schema='scratch.admission-profile.v1', kind=policy.PORT_KIND,
                       authority=deepcopy(policy.PORT_AUTHORITY), memory_route='measured_native',
                       supplier_ready=self.freeze())
        context = self.save('PROFILE.json', profile)
        # Execute the real evidence-export blocks. No staging, proof, or claim runs.
        for name, selected_name in [('prepare', 'measured_inputs'), ('refresh_memory', 'memory_inputs')]:
            function = ast.parse(inspect.getsource(getattr(scratch, name))).body[0]
            start = next(index for index, node in enumerate(function.body)
                         if isinstance(node, ast.ImportFrom) and node.module == 'memory_policy'
                         and any(alias.name == 'profile_bindings' for alias in node.names))
            count = 4 if name == 'prepare' else 3
            body = function.body[start:start + count]
            from types import SimpleNamespace
            namespace = dict(scratch.__dict__, a=SimpleNamespace(admission_profile=Path(context['path'])),
                             context=context, additions=[], c={'cache_producer_files': {'inputs': []}},
                             producers={'inputs': []})
            exec(compile(ast.fix_missing_locations(ast.Module(body=body, type_ignores=[])),
                         '<actual-evidence-export>', 'exec'), namespace)
            self.assertIn(profile['supplier_ready'], namespace[selected_name])
            rows = (namespace['c']['cache_producer_files']['inputs'] if name == 'prepare'
                    else namespace['producers']['inputs'])
            self.assertTrue(any(row['path'] == profile['supplier_ready']['path'] and
                                row['sha256'] == profile['supplier_ready']['sha256'] for row in rows))


if __name__ == '__main__':
    unittest.main()
