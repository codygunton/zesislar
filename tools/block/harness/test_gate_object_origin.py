"""Check the narrow gate origin with private files and no compiler execution."""
from copy import deepcopy
import ast
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'code'))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from entry_chain import binding, read_bound
import gate_object_origin as G
import object_import_migration as M
import closed_object_staging as S
import scratch


class GateOriginTest(unittest.TestCase):
    def preparation_bindings(self, installation):
        """Execute the actual two assignments at the prepare/staging seam."""
        source = Path(scratch.__file__).read_text()
        tree = ast.parse(source)
        prepare = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'prepare')
        block = next(node for node in prepare.body if isinstance(node, ast.If)
                     and ast.unparse(node.test) == "closed_install['count']")
        statements = [node for node in block.body if isinstance(node, ast.Assign)]
        self.assertEqual(len(statements), 2)
        self.save('CLOSED-OBJECT-INSTALL.json', installation)
        namespace = {'closed_install': installation, 'c': {'bindings': [self.compiler]},
                     'out': self.root, 'binding': binding,
                     'combined_bindings': scratch.combined_bindings}
        exec(compile(ast.Module(body=statements, type_ignores=[]), scratch.__file__, 'exec'), namespace)
        return namespace['c']['bindings']

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / 'source'
        self.source.mkdir()
        command = ['git', '-C', str(self.source)]
        for args in [['init', '-q'], ['config', 'user.email', 'fixture@example.invalid'],
                     ['config', 'user.name', 'Fixture']]:
            subprocess.run(command + args, check=True, capture_output=True)
        (self.source / 'Tracked').write_text('unchanged source')
        subprocess.run(command + ['add', 'Tracked'], check=True, capture_output=True)
        subprocess.run(command + ['commit', '-qm', 'fixture'], check=True, capture_output=True)
        self.build = self.source / '_build/gate'
        self.build.mkdir(parents=True)
        self.gate_source = self.build / 'default/Owner.v'
        self.gate_source.parent.mkdir()
        self.gate_source.write_text('Definition value := 0.\n')
        self.obj = self.gate_source.with_suffix('.vo')
        self.obj.write_bytes(b'private object fixture')
        compiler = self.root / 'coqc'
        compiler.write_bytes(b'private compiler fixture')
        coqdep = self.root / 'coqdep'
        coqdep.write_bytes(b'private resolver fixture')
        self.compiler = binding(compiler)
        self.target = self.root / 'target'
        self.target_source = self.target / 'artifacts/default/Owner.v'
        self.target_source.parent.mkdir(parents=True)
        self.target_source.write_bytes(self.gate_source.read_bytes())
        self.module = 'Example.Owner'
        self.flags = ['-Q', str(self.target / 'artifacts/default'), 'Example']
        self.runtime = self.save('runtime.json', {
            'prepared_workspace': str(self.target),
            'proof_runtime': {'module_files': {self.module: 'artifacts/default/Owner.v'}},
            'physical_flags': self.flags})
        marker = self.build / 'dune-build-dir.json'
        marker.write_text(json.dumps({'workspace': str(self.source), 'physical_directory': str(self.build)}))
        for name in G.BUILD_RECORDS - {marker.name}:
            (self.build / name).write_text(self.compiler['path'] if name == 'trace.csexp' else 'private build record')
        (self.build / '.action-trace').mkdir()
        completed = time.time_ns()
        owner = {'pid': 99999999, 'startticks': 1}
        request = self.save('request.json', {'target': 'check-iris', 'workspace': str(self.source),
            'build': str(self.build), 'owner': owner, 'policy': {'claim_key': 'fixture', 'claim_bytes': 1}})
        result = self.save('result.json', {'target': 'check-iris', 'success': True, 'exit_code': 0, 'completed_ns': completed})
        closure = self.save('closure.json', {'all_owned_actors_closed': True, 'batch': {'actors': [], 'aggregate_paths': [str(self.root / 'absent')]}})
        release = self.save('release.json', {'released': True, 'owner': owner, 'claim_key': 'fixture', 'bytes': 1, 'closure': closure['path']})
        source_tree = G.tree(self.source)
        final = self.save('final.json', {'success': True, 'source_clean_and_unchanged': True,
            'source_boundary': {'workspace': str(self.source), 'commit': source_tree['commit']},
            'gates': [{'target': 'check-iris', 'accepted': True, 'all_owned_actors_closed': True,
                       'outer_actors_closed': True, 'kernel_aggregate_absent': True, 'claim_value': 0,
                       'receipts': {'RESULT': result, 'REQUEST': request, 'CLOSURE': closure, 'RELEASE': release}}]})
        self.value = {'schema': G.SCHEMA, 'kind': G.KIND, 'gate_final': final,
            'result': result, 'request': request, 'closure': closure, 'release': release,
            'source_workspace': str(self.source), 'source_tree': source_tree, 'build_root': str(self.build),
            'build_identity': G.file_identity(self.build),
            'build_directories': [{'path': str(self.build / '.action-trace'),
                                   'identity': G.file_identity(self.build / '.action-trace')}],
            'dune_build_directory': binding(marker),
            'build_records': [{'binding': binding(self.build / name), 'identity': G.file_identity(self.build / name)}
                              for name in sorted(G.BUILD_RECORDS)],
            'compiler': self.compiler, 'coqdep': binding(coqdep), 'resolution_runtime': self.runtime,
            'modules': [{'module': self.module, 'target_relative': 'artifacts/default/Owner.v',
                'source': binding(self.gate_source), 'object': binding(self.obj),
                'source_identity': G.file_identity(self.gate_source), 'object_identity': G.file_identity(self.obj)}]}
        self.freeze()

    def save(self, name, data):
        path = self.root / name
        path.write_text(json.dumps(data))
        return binding(path)

    def freeze(self):
        self.reference = self.save('origin.json', self.value)
        self.authority = {'kind': G.KIND, 'binding': self.reference,
            'gate_final': self.value['gate_final'],
            'module_objects': {row['module']: row['object'] for row in self.value['modules']}}

    def context(self):
        return G.context(self.authority, self.reference, read_bound)

    def selected(self, flags=None):
        config = self.context()[0]
        return G.selected_origin(self.authority, self.reference, self.module,
            self.gate_source, self.obj, self.compiler, flags or config['physical_flags'], self.build, read_bound)

    def test_exact_gate_object_has_no_ready_or_physical_receipt(self):
        accepted, _ = self.selected()
        self.assertEqual(accepted['kind'], G.LABEL)
        self.assertNotIn('ready', accepted)
        self.assertNotIn('original_receipts', accepted)

    def test_original_origin_kinds_remain_unsupported_by_gate_helper(self):
        for kind in ['accepted-ready', 'accepted-supplier', 'accepted-closed-compilations']:
            with self.subTest(kind=kind):
                authority = dict(self.authority, kind=kind)
                with self.assertRaisesRegex(ValueError, 'not authorized'):
                    G.context(authority, self.reference, read_bound)

    def test_changed_source_tree_refuses(self):
        (self.source / 'Tracked').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'source tree'):
            self.context()

    def test_missing_build_refuses(self):
        self.build.rename(self.source / '_build/moved')
        with self.assertRaises((ValueError, OSError)):
            self.context()

    def test_changed_build_record_refuses(self):
        (self.build / 'dune-build-dir.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'changed after'):
            self.context()

    def test_missing_build_record_refuses(self):
        self.value['build_records'].pop()
        self.freeze()
        with self.assertRaisesRegex(ValueError, 'complete sealed Dune'):
            self.context()

    def test_action_directory_change_refuses(self):
        (self.build / '.action-trace/changed').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'action directory changed'):
            self.context()

    def test_changed_object_refuses_even_if_the_origin_is_resealed(self):
        self.obj.write_bytes(b'changed')
        row = self.value['modules'][0]
        row.update(object=binding(self.obj), object_identity=G.file_identity(self.obj))
        self.freeze()
        with self.assertRaisesRegex(ValueError, 'changed after'):
            self.context()

    def test_identical_object_inode_replacement_refuses(self):
        raw = self.obj.read_bytes()
        self.obj.unlink()
        self.obj.write_bytes(raw)
        with self.assertRaisesRegex(ValueError, 'changed after'):
            self.context()

    def test_ctime_only_change_passes_and_is_recorded(self):
        os.chmod(self.obj, self.obj.stat().st_mode)
        config = self.context()[0]
        observations = config['gate_identity_observations'][self.module]
        self.assertEqual(len(observations), 1)
        self.assertEqual(observations[0]['path'], str(self.obj))
        self.assertTrue(observations[0]['SHA256_unchanged'])
        self.assertTrue(observations[0]['identity_except_ctime_unchanged'])
        _, receipt = self.migration()
        self.assertEqual(receipt['gate_identity_observations'], observations)
        self.assertEqual(self.reference, binding(self.root / 'origin.json'))

    def test_changed_compiler_refuses(self):
        Path(self.compiler['path']).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'compiler installation'):
            self.context()

    def test_changed_target_source_refuses(self):
        self.target_source.write_text('Definition value := 1.')
        with self.assertRaisesRegex(ValueError, 'target source'):
            self.context()

    def test_source_mapping_and_duplicate_selection_refuse(self):
        for change in ['mapping', 'duplicate']:
            before = deepcopy(self.value)
            if change == 'mapping':
                self.value['modules'][0]['target_relative'] = 'elsewhere/Owner.v'
            else:
                self.value['modules'] *= 2
            self.freeze()
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.context()
            self.value = before

    def test_gate_record_cannot_name_a_different_accepted_final(self):
        self.authority['gate_final'] = {'path': 'other', 'sha256': '0' * 64}
        with self.assertRaisesRegex(ValueError, 'accepted gate differs'):
            self.context()

    def test_changed_resolution_flags_refuse(self):
        with self.assertRaisesRegex(ValueError, 'resolution context'):
            self.selected(self.context()[0]['physical_flags'] + ['-noinit'])

    def test_gate_layout_translation_is_exact_and_binds_global_q(self):
        config = self.context()[0]
        self.assertEqual(G.normalize_flags(config['physical_flags'], self.build),
                         G.normalize_flags(self.flags, self.target))
        self.assertIn('-Q', config['physical_flags'])

    def test_relocation_reads_resolution_runtime_once_per_process_batch(self):
        with M.batch(), patch.object(M, 'read_bound', wraps=M.read_bound) as read:
            for _ in range(20):
                self.assertEqual(G.relocate(self.value,self.module,self.obj,self.target),
                                 self.target_source.with_suffix('.vo'))
            self.assertEqual(read.call_args_list,[unittest.mock.call(self.runtime)])

    def test_relocation_cache_does_not_cross_a_process_identity(self):
        with M.batch(), patch.object(M, 'read_bound', wraps=M.read_bound) as read:
            with patch.object(M.os,'getpid',return_value=101):
                G.relocate(self.value,self.module,self.obj,self.target)
            with patch.object(M.os,'getpid',return_value=202):
                G.relocate(self.value,self.module,self.obj,self.target)
            self.assertEqual(read.call_count,2)

    def test_relocation_cache_refuses_a_changed_resolution_runtime(self):
        with M.batch():
            G.relocate(self.value,self.module,self.obj,self.target)
            path=Path(self.runtime['path'])
            old=path.stat()
            payload=path.read_text().replace('Example','Changed')
            path.write_text(payload)
            os.utime(path,ns=(old.st_atime_ns,old.st_mtime_ns))
            with self.assertRaisesRegex(ValueError,'binding changed'):
                G.relocate(self.value,self.module,self.obj,self.target)

    def test_relocation_cache_keeps_a_forced_final_digest_check(self):
        from binding_cache import COUNTERS, force_hashing
        with M.batch(), patch.object(M,'read_bound',wraps=M.read_bound) as read:
            G.relocate(self.value,self.module,self.obj,self.target)
            before=COUNTERS['hashes']
            with force_hashing(True):
                G.relocate(self.value,self.module,self.obj,self.target)
            self.assertGreater(COUNTERS['hashes'],before)
            self.assertEqual(read.call_count,1)

    def test_relocation_cache_key_includes_the_exact_resolution_binding(self):
        with M.batch():
            G.relocate(self.value,self.module,self.obj,self.target)
            publication=deepcopy(self.value)
            publication['resolution_runtime']=dict(self.runtime,sha256='0'*64)
            with self.assertRaisesRegex(ValueError,'binding changed'):
                G.relocate(publication,self.module,self.obj,self.target)

    def test_only_bound_owned_dependency_paths_relocate(self):
        self.assertEqual(G.relocate(self.value, self.module, self.obj, self.target), self.target_source.with_suffix('.vo'))
        with self.assertRaises(ValueError):
            G.relocate(self.value, self.module, self.build / 'default/Other.vo', self.target)

    def migration(self):
        policy = self.save('policy.json', {'origins': [self.authority], 'inspector_build': {'path': 'bound', 'sha256': 'x'}})
        comparison = {'objects': [], 'checks': []}
        with patch.object(M, 'POLICY', Path(policy['path'])), patch.object(M, 'comparisons', return_value=([], comparison)):
            value = M.create(self.reference, self.module, self.gate_source, self.obj,
                             self.compiler, self.context()[0]['physical_flags'], self.build)
        return policy, value

    def test_migration_revalidates_every_normal_import_comparison(self):
        policy, value = self.migration()
        reference = self.save('migration.json', value)
        self.target_source.with_suffix('.vo').write_bytes(self.obj.read_bytes())
        with patch.object(M, 'POLICY', Path(policy['path'])), patch.object(M, 'comparisons', side_effect=ValueError('digest mismatch')) as compare:
            with self.assertRaisesRegex(ValueError, 'digest mismatch'):
                M.validate(reference, self.module, self.target_source, self.target_source.with_suffix('.vo'), self.compiler, self.flags, self.target)
            compare.assert_called_once()

    def test_staging_copies_only_the_bound_object_and_grants_no_compatibility(self):
        policy, value = self.migration()
        reference = self.save('migration.json', value)
        with patch.object(M, 'POLICY', Path(policy['path'])), patch.object(S.clone_copy, 'copy2', side_effect=shutil.copy2):
            result = S.stage({'object_imports': {self.module: reference}}, self.target,
                             {self.module: 'artifacts/default/Owner.v'})
        self.assertEqual(result['count'], 1)
        self.assertFalse(result['compatibility_granted'])
        self.assertEqual(binding(self.target_source.with_suffix('.vo'))['sha256'], binding(self.obj)['sha256'])
        self.assertNotEqual(self.target_source.with_suffix('.vo').stat().st_ino, self.obj.stat().st_ino)
        self.assertFalse(self.target_source.with_suffix('.vos').exists())
        bindings = self.preparation_bindings(result)
        self.assertEqual(bindings, [self.compiler, binding(self.target_source.with_suffix('.vo')),
                                   binding(self.root / 'CLOSED-OBJECT-INSTALL.json')])

    def test_preparation_preserves_real_sidecar_bindings(self):
        sidecar = self.save('sidecar.json', {'private': True})
        obj = binding(self.obj)
        result = {'count': 1, 'installed': [{'object': obj, 'sidecar': sidecar}]}
        self.assertEqual(self.preparation_bindings(result),
                         [self.compiler, obj, sidecar, binding(self.root / 'CLOSED-OBJECT-INSTALL.json')])

    def test_preparation_does_not_filter_required_object_or_malformed_sidecar(self):
        for row in [{'object': None, 'sidecar': None},
                    {'object': binding(self.obj), 'sidecar': {}}]:
            with self.subTest(row=row), self.assertRaises((TypeError, KeyError)):
                self.preparation_bindings({'count': 1, 'installed': [row]})


if __name__ == '__main__':
    unittest.main()
