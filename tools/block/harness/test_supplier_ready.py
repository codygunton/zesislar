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
import _historical_fixtures as historical
import supplier_ready as supplier


def binding(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


class SupplierReady(unittest.TestCase):
    def setUp(self):
        historical.use_policy(self)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.cache_root = patch('supplier_resolution_cache.CACHE_ROOT', self.root / 'resolution-cache')
        self.cache_root.start()
        self.addCleanup(self.cache_root.stop)
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

    def external_installation(self):
        # Use one real installed pair. The controls never change these files.
        external = Path('/home/cody/islaris/_opam/lib/coq/theories/Classes/SetoidTactics.v')
        name = 'Coq.Classes.SetoidTactics'
        self.assertTrue(external.is_file() and external.with_suffix('.vo').is_file())
        row = dict(module=name, source=binding(external), object=binding(external.with_suffix('.vo')))
        self.modules.append(row)
        self.mapping[name] = str(external)
        resolver = self.root / 'coqdep'
        resolver.write_text('#!/usr/bin/python3\nimport sys\nprint(sys.argv[-1] + ".vo: ' +
                            str(external.with_suffix('.vo')) + '")\n')
        resolver.chmod(0o755)
        self.ready['bindings'].extend([row['source'], row['object'], binding(resolver)])
        self.flags.extend(['-R', str(external.parents[1]), 'Coq'])
        graph = json.loads(Path(self.graph['path']).read_text())
        graph['import_edges'].append(dict(**{'from': self.names[0], 'to': name}))
        self.graph = self.save('GRAPH.json', graph)
        self.ready['cache_import_graph'] = self.graph
        self.manifest['import_graph'] = self.graph
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        self.manifest['runtime'] = self.save('jobs/prerequisites/RUNTIME.json', self.inner)
        return row

    def hooks_fallback(self, declaration='Declare ML Module "zesu-signature-gates.plugin".'):
        row = next(module for module in self.modules if module['module'] == 'ZesuSsz.Automation.Hooks')
        source = Path(row['source']['path'])
        source.write_text(source.read_text() + declaration + '\n')
        row['source'] = binding(source)
        self.ready['bindings'] = [row['source'] if old['path'] == str(source) else old
                                  for old in self.ready['bindings']]
        wrapper = self.workspace / 'tools/entry_chain_coqc.sh'
        wrapper.parent.mkdir()
        wrapper.write_text('#!/bin/sh\nexit 0\n')
        self.ready['bindings'].append(binding(wrapper))
        fallback = dict(success=True, returncode=0, method='stock-guarded-dependency-build',
            MCP_refusal='Forbidden command Declare ML Module', source=row['source'],
            argv=[str(wrapper), *self.flags, str(source)],
            stdout=self.file('jobs/prerequisites/native/HOOKS-COMPILE.stdout', b''),
            stderr=self.file('jobs/prerequisites/native/HOOKS-COMPILE.stderr', b'warning'))
        self.manifest['hooks_compile'] = self.save('jobs/prerequisites/native/HOOKS-COMPILE.json', fallback)
        self.save('jobs/prerequisites/native/dependency-' + row['module'] + '.json', dict(
            source=str(source), source_sha256=row['source']['sha256'],
            object=row['object']['path'], object_sha256=row['object']['sha256'], result=fallback))
        self.calls = [call for call in self.calls if not (call['tool'] == 'rocq_compile_file'
                     and call['arguments']['file'] == str(source))]
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', self.calls)
        self.inner.update(coqc_wrapper='tools/entry_chain_coqc.sh', bindings=self.ready['bindings'])
        self.manifest['runtime'] = self.save('jobs/prerequisites/RUNTIME.json', self.inner)
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        self.manifest['source_packet'] = self.save('SOURCE.json', dict(all_sources=[
            dict(value['source'], module=value['module']) for value in self.modules[:3]]))

    def entry_intro_fallback(self, declaration='Declare ML Module "zesu-signature-gates.plugin".'):
        name = 'ZesuSsz.Automation.EntryIntro'
        source = self.workspace / (name.replace('.', '/') + '.v')
        source.write_text(declaration + '\n')
        source.with_suffix('.vo').write_bytes(b'EntryIntro object')
        row = dict(module=name, source=binding(source), object=binding(source.with_suffix('.vo')))
        self.mapping[name] = str(source.relative_to(self.workspace))
        self.modules.append(row)
        self.names.append(name)
        self.manifest['modules'].append(row)
        self.ready['bindings'].extend([row['source'], row['object']])
        readiness = json.loads(Path(self.readiness['path']).read_text())
        readiness['objects'].append(row['object'])
        self.readiness = self.save('READINESS.json', readiness)
        self.ready['readiness'] = self.readiness
        graph = json.loads(Path(self.graph['path']).read_text())
        graph['import_edges'].append({'from': self.names[0], 'to': name})
        self.graph = self.save('GRAPH.json', graph)
        self.ready['cache_import_graph'] = self.manifest['import_graph'] = self.graph
        wrapper = self.workspace / 'tools/entry_chain_coqc.sh'
        wrapper.parent.mkdir(exist_ok=True)
        wrapper.write_text('#!/bin/sh\nexit 0\n')
        if binding(wrapper) not in self.ready['bindings']:
            self.ready['bindings'].append(binding(wrapper))
        refusal = dict(success=False, reason='validation',
                       error=supplier.ENTRYINTRO_MCP_REFUSAL, state_capture_status='no_position')
        self.calls.insert(-2, self.call('rocq_compile_file', dict(
            workspace=str(self.workspace), file=str(source), timeout=100,
            keep_vo=True, include_warnings=True), refusal))
        fallback = dict(success=True, returncode=0, method='stock-guarded-dependency-build',
            MCP_refusal=supplier.ENTRYINTRO_MCP_REFUSAL, MCP_refusal_result=refusal,
            source=row['source'], argv=[str(wrapper), *self.flags, str(source)],
            stdout=self.file('jobs/prerequisites/native/ENTRYINTRO-COMPILE.stdout', b''),
            stderr=self.file('jobs/prerequisites/native/ENTRYINTRO-COMPILE.stderr', b'warning'))
        self.manifest['entry_intro_compile'] = self.save(
            'jobs/prerequisites/native/ENTRYINTRO-COMPILE.json', fallback)
        self.save('jobs/prerequisites/native/dependency-' + name + '.json', dict(
            source=str(source), source_sha256=row['source']['sha256'],
            object=row['object']['path'], object_sha256=row['object']['sha256'], result=fallback))
        self.inner.update(coqc_wrapper='tools/entry_chain_coqc.sh', bindings=self.ready['bindings'])
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', self.calls)
        self.manifest['runtime'] = self.save('jobs/prerequisites/RUNTIME.json', self.inner)
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)

    def change_entry_fallback(self, **changes):
        fallback = json.loads(Path(self.manifest['entry_intro_compile']['path']).read_text())
        fallback.update(changes)
        self.change('entry_intro_compile', **fallback)
        path = 'jobs/prerequisites/native/dependency-ZesuSsz.Automation.EntryIntro.json'
        receipt = json.loads((self.root / path).read_text())
        receipt['result'] = fallback
        self.save(path, receipt)

    def overlapping_isla_installation(self):
        source = Path('/home/cody/islaris/_opam/lib/coq/user-contrib/isla/riscv64/arch.v')
        name = 'isla.riscv64.arch'
        row = dict(module=name, source=binding(source), object=binding(source.with_suffix('.vo')))
        self.modules.append(row)
        self.mapping[name] = str(source)
        self.compiler['compiler'] = binding(Path('/home/cody/islaris/_opam/bin/coqc'))
        self.ready['bindings'].extend([row['source'], row['object'],
            binding(Path('/home/cody/islaris/_opam/bin/coqdep'))])
        self.flags.extend(['-Q', str(source.parents[1]), 'isla',
                           '-Q', str(source.parent), 'isla.riscv64'])
        graph = json.loads(Path(self.graph['path']).read_text())
        graph['import_edges'].append({'from': self.names[0], 'to': name})
        self.graph = self.save('GRAPH.json', graph)
        self.ready['cache_import_graph'] = self.graph
        self.manifest['import_graph'] = self.graph
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        self.manifest['runtime'] = self.save('jobs/prerequisites/RUNTIME.json', self.inner)
        return row

    def test_completed_supplier_and_exact_staged_closure_pass(self):
        value = self.validate()
        self.assertEqual(len(supplier.staged(value, self.config())), 4)
        self.assertEqual(value['names'], set(self.mapping))

    def test_actual_validation_and_staging_share_only_checked_resolution(self):
        self.external_installation()
        selected = self.freeze()
        first = supplier.validate(selected)
        supplier.validate(selected)
        supplier.staged(first, self.config())
        root = self.root / 'resolution-cache' / selected['sha256']
        events = [json.loads(line) for path in root.glob('events-*.jsonl')
                  for line in path.read_text().splitlines()]
        counts = {kind: sum(row['event'] == kind for row in events)
                  for kind in ['logical_lookups', 'coqdep_invocations', 'cache_hits', 'cache_misses']}
        self.assertEqual(counts, dict(logical_lookups=3, coqdep_invocations=1,
                                     cache_hits=2, cache_misses=1))

    def test_exact_external_installation_passes_without_relocation(self):
        row = self.external_installation()
        value = self.validate()
        source = next(module for module in value['modules'] if module['module'] == row['module'])
        self.assertEqual(source['installed_mapping']['mappings'][0]['prefix'], 'Coq')
        self.assertEqual(source['installed_mapping']['mappings'][0]['root'], str(Path(row['source']['path']).parents[1]))
        self.assertIn(row['object'], value['bindings'])
        self.assertEqual(len(supplier.staged(value, self.config())), 5)

    def test_existing_guarded_hooks_fallback_passes_without_invented_mcp_call(self):
        self.hooks_fallback()
        value = self.validate()
        self.assertIn(self.manifest['hooks_compile'], value['bindings'])
        self.assertEqual(sum(call['tool'] == 'rocq_compile_file' for call in self.calls), 2)

    def test_entryintro_exact_refusal_and_guarded_receipt_pass(self):
        self.entry_intro_fallback()
        value = self.validate()
        self.assertIn(self.manifest['entry_intro_compile'], value['bindings'])
        self.assertEqual(sum(call['tool'] == 'rocq_compile_file' for call in self.calls), 4)

    def test_both_distinct_owner_receipts_pass_and_extract(self):
        self.hooks_fallback()
        hooks = deepcopy(self.manifest['hooks_compile'])
        self.entry_intro_fallback()
        self.validate()
        self.assertEqual(supplier.plugin_compile_bindings(self.output), dict(
            hooks_compile=hooks, entry_intro_compile=self.manifest['entry_intro_compile']))

    def test_entryintro_without_receipt_cannot_relabel_mcp_refusal(self):
        self.entry_intro_fallback()
        del self.manifest['entry_intro_compile']
        with self.assertRaisesRegex(ValueError, 'compile call differs'):
            self.validate()

    def test_entryintro_requires_the_actual_mcp_refusal(self):
        self.entry_intro_fallback()
        call = next(c for c in self.calls if c.get('result', {}).get('reason') == 'validation')
        call['result']['error'] = 'another error'
        call['raw_response']['structuredContent']['error'] = 'another error'
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', self.calls)
        with self.assertRaisesRegex(ValueError, 'exact MCP refusal'):
            self.validate()

    def test_entryintro_requires_the_refusal_transport(self):
        self.entry_intro_fallback()
        call = next(c for c in self.calls if c.get('result', {}).get('reason') == 'validation')
        call['arguments']['workspace'] = str(self.root / 'elsewhere')
        self.manifest['calls'] = self.save('jobs/prerequisites/native/CALLS.json', self.calls)
        with self.assertRaisesRegex(ValueError, 'refusal transport differs'):
            self.validate()

    def test_entryintro_receipt_must_bind_that_refusal_result(self):
        self.entry_intro_fallback()
        self.change_entry_fallback(MCP_refusal_result=dict(success=False, error='another error'))
        with self.assertRaisesRegex(ValueError, 'refusal receipt differs'):
            self.validate()

    def test_entryintro_requires_the_exact_plugin(self):
        self.entry_intro_fallback('Declare ML Module "another.plugin".')
        with self.assertRaisesRegex(ValueError, 'existing guarded build'):
            self.validate()

    def test_entryintro_rejects_another_compiler_vector(self):
        self.entry_intro_fallback()
        fallback = json.loads(Path(self.manifest['entry_intro_compile']['path']).read_text())
        self.change_entry_fallback(argv=fallback['argv'] + ['-unexpected'])
        with self.assertRaisesRegex(ValueError, 'existing guarded build'):
            self.validate()

    def test_entryintro_rejects_hooks_receipt_path(self):
        self.entry_intro_fallback()
        self.manifest['entry_intro_compile'] = self.save('jobs/prerequisites/native/HOOKS-COMPILE.json',
            json.loads(Path(self.manifest['entry_intro_compile']['path']).read_text()))
        with self.assertRaisesRegex(ValueError, 'leaves its exact job'):
            self.validate()

    def test_entryintro_field_cannot_apply_to_other_modules(self):
        self.manifest['entry_intro_compile'] = self.save(
            'jobs/prerequisites/native/ENTRYINTRO-COMPILE.json', {})
        with self.assertRaisesRegex(ValueError, 'not consumed'):
            self.validate()

    def test_real_overlapping_isla_roots_use_pinned_coqdep_selection(self):
        row = self.overlapping_isla_installation()
        self.assertEqual(row['source']['sha256'],
                         'afe8d96468b1c33befd2af6f7944c3ace616b11b3ad98094a6f94ab58847ca41')
        self.assertEqual(row['object']['sha256'],
                         '9d2a7a45aaeee7c54e630b9e9e19497284d49bd9964e82234a429149560bdcac')
        value = self.validate()
        selected = next(module for module in value['modules'] if module['module'] == row['module'])
        self.assertEqual(selected['installed_mapping']['canonical'], row['module'])
        self.assertEqual([mapping['prefix'] for mapping in selected['installed_mapping']['mappings']],
                         ['isla', 'isla.riscv64'])
        self.assertEqual(len(supplier.staged(value, self.config())), 5)

    def test_reordered_overlapping_flags_remain_unauthorized(self):
        self.overlapping_isla_installation()
        value = self.validate()
        config = self.config()
        config['physical_flags'] = self.flags[:-6] + self.flags[-3:] + self.flags[-6:-3]
        with self.assertRaisesRegex(ValueError, 'staged physical_flags differs'):
            supplier.staged(value, config)

    def test_missing_hooks_fallback_refuses(self):
        self.hooks_fallback()
        del self.manifest['hooks_compile']
        with self.assertRaisesRegex(ValueError, 'compile call count'):
            self.validate()

    def test_changed_plugin_declaration_refuses(self):
        self.hooks_fallback('Declare ML Module "another.plugin".')
        with self.assertRaisesRegex(ValueError, 'existing guarded build'):
            self.validate()

    def test_unrecognized_hooks_method_refuses(self):
        self.hooks_fallback()
        self.change('hooks_compile', method='unreviewed-build')
        with self.assertRaisesRegex(ValueError, 'existing guarded build'):
            self.validate()

    def test_unbound_hooks_wrapper_refuses(self):
        self.hooks_fallback()
        wrapper = str(self.workspace / 'tools/entry_chain_coqc.sh')
        self.inner['bindings'] = [row for row in self.inner['bindings'] if row['path'] != wrapper]
        self.manifest['runtime'] = self.save('jobs/prerequisites/RUNTIME.json', self.inner)
        with self.assertRaisesRegex(ValueError, 'exact tool binding'):
            self.validate()

    def test_hooks_fallback_vector_change_refuses(self):
        self.hooks_fallback()
        fallback = json.loads(Path(self.manifest['hooks_compile']['path']).read_text())
        fallback['argv'].append('-unexpected')
        self.change('hooks_compile', **fallback)
        self.save('jobs/prerequisites/native/dependency-ZesuSsz.Automation.Hooks.json', dict(
            source=fallback['source']['path'], source_sha256=fallback['source']['sha256'],
            object=str(Path(fallback['source']['path']).with_suffix('.vo')),
            object_sha256=next(row['object']['sha256'] for row in self.modules
                              if row['module'] == 'ZesuSsz.Automation.Hooks'), result=fallback))
        with self.assertRaisesRegex(ValueError, 'existing guarded build'):
            self.validate()

    def test_external_mapping_or_source_path_change_refuses(self):
        row = self.external_installation()
        self.mapping[row['module']] = str(Path(row['source']['path']).with_name('Morphisms.v'))
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        with self.assertRaisesRegex(ValueError, 'installed module mapping differs'):
            self.validate()

    def test_external_hash_change_refuses(self):
        row = self.external_installation()
        self.ready['bindings'] = [dict(value, sha256='0' * 64)
            if value['path'] == row['object']['path'] else value for value in self.ready['bindings']]
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        with self.assertRaisesRegex(ValueError, 'input changed'):
            self.validate()

    def publication_capture(self):
        row = self.external_installation()
        self.ready['bindings'] = [old for old in self.ready['bindings']
                                  if old['path'] not in {row['source']['path'], row['object']['path']}]
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        self.manifest['modules'] = self.manifest['modules'] + [row]
        self.manifest['installation_qualification'] = 'publication_time_identity_only'
        return row

    def test_publication_only_capture_is_explicit_and_passes_current_identity(self):
        row = self.publication_capture()
        value = self.validate()
        self.assertEqual(set(value['publication_only_installed']),
                         {(row['module'], 'source'), (row['module'], 'object')})
        self.assertEqual(len(supplier.staged(value, self.config())), 5)

    def test_missing_publication_qualification_refuses(self):
        self.publication_capture()
        del self.manifest['installation_qualification']
        with self.assertRaisesRegex(ValueError, 'publication-time qualification'):
            self.validate()

    def test_missing_publication_pair_refuses(self):
        row = self.publication_capture()
        self.manifest['modules'] = [old for old in self.manifest['modules'] if old['module'] != row['module']]
        with self.assertRaisesRegex(ValueError, 'exact manifest row'):
            self.validate()

    def test_publication_capture_does_not_supply_missing_owned_identity(self):
        self.publication_capture()
        source = self.modules[0]['source']['path']
        self.ready['bindings'] = [old for old in self.ready['bindings'] if old['path'] != source]
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        with self.assertRaisesRegex(ValueError, 'dependency lacks a bound source'):
            self.validate()

    def test_incorrect_publication_hash_refuses(self):
        row = self.publication_capture()
        row['object'] = dict(row['object'], sha256='0' * 64)
        with self.assertRaisesRegex(ValueError, 'input changed'):
            self.validate()

    def test_external_source_cannot_relocate_to_owned_copy(self):
        row = self.external_installation()
        value = self.validate()
        config = self.config()
        copied = self.workspace / 'ExternalCopy.v'
        copied.write_bytes(Path(row['source']['path']).read_bytes())
        copied.with_suffix('.vo').write_bytes(Path(row['object']['path']).read_bytes())
        config['proof_runtime']['module_files'][row['module']] = str(copied)
        with self.assertRaisesRegex(ValueError, 'staged installed source path differs'):
            supplier.staged(value, config)

    def test_owned_relocation_keeps_the_external_installation_exact(self):
        row = self.publication_capture()
        value = self.validate()
        relocated = self.root / 'relocated'
        for module in self.modules:
            for kind in ['source', 'object']:
                original = Path(module[kind]['path'])
                if not original.is_relative_to(self.workspace):
                    continue
                copied = relocated / original.relative_to(self.workspace)
                copied.parent.mkdir(parents=True, exist_ok=True)
                copied.write_bytes(original.read_bytes())
        config = self.config()
        config['prepared_workspace'] = str(relocated)
        for field in ['expected_mcp_flags', 'physical_flags']:
            config[field] = [word.replace(str(self.workspace), str(relocated)) for word in self.flags]
        self.assertEqual(len(supplier.staged(value, config)), 5)
        self.assertEqual(config['proof_runtime']['module_files'][row['module']], row['source']['path'])

    def test_external_resolver_identity_change_refuses(self):
        self.external_installation()
        (self.root / 'coqdep').write_bytes(b'other resolver')
        with self.assertRaisesRegex(ValueError, 'input changed'):
            self.validate()

    def test_relative_traversal_cannot_name_an_installed_source(self):
        row = self.external_installation()
        import os
        self.mapping[row['module']] = os.path.relpath(row['source']['path'], self.workspace)
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        with self.assertRaisesRegex(ValueError, 'outside the installed roots'):
            self.validate()

    def test_foreign_absolute_source_is_not_an_installation(self):
        row = self.external_installation()
        foreign = self.root / 'foreign/SetoidTactics.v'
        foreign.parent.mkdir()
        foreign.write_bytes(Path(row['source']['path']).read_bytes())
        self.mapping[row['module']] = str(foreign)
        self.manifest['ready'] = self.save('READY-RUNTIME.json', self.ready)
        with self.assertRaisesRegex(ValueError, 'outside the installed roots'):
            self.validate()

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
