"""Authenticate private-output publication with nonproof physical receipts."""
import json
import os
from pathlib import Path
import threading
import unittest
from unittest.mock import patch

import compiler_snapshot as S
from declaration_outputs import GIB, private_target, publication_lock, publish
from entry_chain import binding, save
from source_context import compilation
import test_compiler_snapshot as fixture


class DeclarationOutputTests(unittest.TestCase):
    def setUp(self):
        self.f = fixture.CompilerSnapshotTests()
        self.f.setUp()
        self.addCleanup(self.f.temp.cleanup)
        f = self.f
        (f.library / 'Dependency.v').write_text('(* Nonproof dependency. *)\n')
        graph = f.root / 'GRAPH.json'
        save(graph, {'import_edges': [{'from': 'Example.Control', 'to': 'Example.Dependency'}]})
        f.runtime.update(phase='prerequisites',
            declaration_dag={'schema': 'entry-chain.declaration-dag.v1'},
            canonical_admission={'minimum_claim_bytes': 64 * GIB, 'physical_fence_bytes': 64 * GIB},
            module_files={'Example.Control': 'Control.v', 'Example.Dependency': 'library/Dependency.v'},
            cache_import_graph=binding(graph))
        f.runtime['bindings'].append(binding(graph))
        self.snapshot = f.seal()
        self.manager = S.OutputReceipts(self.snapshot, f.reference)

    def physical(self, *, owner='Example.Control', bad_argv=False):
        f = self.f
        source, compiler = binding(f.source), binding(f.compiler)
        report = S.validate_compiler(f.runtime, f.reference, self.snapshot, source, f.compiler)
        report['import_selection'] = S.import_selection(f.runtime, source, f.root, report)
        directory = f.root / 'compiler-invocations/synthetic'
        directory.mkdir(parents=True)
        private = f.root / '.declaration-private' / ('a' * 32) / 'Control.vo'
        private.parent.mkdir(parents=True)
        before = S.sidecar_prestate(source, private, compiler, f.runtime['physical_flags'], report)
        private.write_bytes(b'Nonproof private object.')
        private.with_suffix('.vos').write_bytes(b'')
        private.with_suffix('.glob').write_text('\nF' + owner + '\n')
        argv = [compiler['path'], *f.runtime['physical_flags'], '-o', str(private), source['path']]
        if bad_argv:
            argv[-2] = str(f.source.with_suffix('.vo'))
        validation = S._publish(directory / 'PHYSICAL-VALIDATION.json', report)
        inputs = S._publish(directory / 'INPUT.json', {
            'source': source, 'compiler': compiler, 'owned_workspace': str(f.root),
            'target': {'module': 'Example.Control'},
            'physical_argv': argv, 'compiler_context': compilation(f.runtime['physical_flags'], source),
            'sidecar_prestate': before, 'validation': {'runtime': f.reference, 'snapshot': self.snapshot}})
        physical = S._publish(directory / 'PHYSICAL-RESULT.json', {
            'input': inputs, 'input_validation': validation, 'physical_argv': argv,
            'returncode': 0, 'output_capture': {'complete': True},
            'output_validation': {'success': True}, 'compiler_outputs': S.compiler_outputs(private, before)})
        return private, physical

    def accept(self, private, physical):
        return publish(self.manager, 'Example.Control', self.f.source, physical, private,
                       {'success': True, 'method': 'guarded-dune-dependency-build'}, workspace=self.f.root)

    def test_private_result_publishes_one_authenticated_canonical_pair(self):
        private, physical = self.physical()
        self.assertFalse(self.f.source.with_suffix('.vo').exists())
        receipt = self.accept(private, physical)
        value = json.loads(Path(receipt['path']).read_text())
        self.assertEqual(value['object'], binding(self.f.source.with_suffix('.vo')))
        self.assertEqual(value['object']['sha256'], binding(private)['sha256'])
        self.assertNotEqual(private.stat().st_ino, self.f.source.with_suffix('.vo').stat().st_ino)
        self.assertIn('publication', value)
        sealed = S.read(self.snapshot, self.f.reference)
        rows, _, _, _ = S.accepted_objects(sealed, self.snapshot, self.manager.key,
                                           binding(self.f.compiler), self.f.runtime['physical_flags'])
        self.assertEqual(rows, [binding(self.f.source.with_suffix('.vo'))])

    def test_real_private_producer_passes_the_reuse_consumer(self):
        from object_imports import compatibility
        private, physical = self.physical()
        receipt = self.accept(private, physical)
        result = compatibility(['Example.Control'], [{'from': 'Example.Control', 'to': 'Example.Dependency'}],
            self.f.runtime['module_files'], self.f.root, {'Example.Control': receipt},
            binding(self.f.compiler), self.f.runtime['physical_flags'])
        self.assertIn('Example.Control', result['compatible_owned_modules'])

    def test_real_private_producer_relocates_and_detects_changed_import(self):
        from clone_copy import copy2
        from object_imports import compatibility
        private, physical = self.physical()
        receipt = self.accept(private, physical)
        copied = self.f.root / 'relocated'
        (copied / 'library').mkdir(parents=True)
        for path in [self.f.source, self.f.source.with_suffix('.vo'), self.f.obj,
                     self.f.library / 'Dependency.v']:
            copy2(path, copied / path.relative_to(self.f.root))
        arguments = (['Example.Control'], [{'from': 'Example.Control', 'to': 'Example.Dependency'}],
                     self.f.runtime['module_files'], copied, {'Example.Control': receipt},
                     binding(self.f.compiler), ['-Q', str(copied / 'library'), 'Example'])
        self.assertIn('Example.Control', compatibility(*arguments)['compatible_owned_modules'])
        (copied / 'library/Dependency.vo').write_bytes(b'Changed imported object.')
        self.assertIn('Example.Control', compatibility(*arguments)['rebuild_modules'])

    def test_wrong_physical_output_refuses_before_canonical_write(self):
        private, physical = self.physical(bad_argv=True)
        with self.assertRaisesRegex(ValueError, 'physical compiler record'):
            self.accept(private, physical)
        self.assertFalse(self.f.source.with_suffix('.vo').exists())

    def test_wrong_logical_owner_refuses_before_canonical_write(self):
        private, physical = self.physical(owner='Other.Control')
        with self.assertRaisesRegex(ValueError, 'logical owner'):
            self.accept(private, physical)
        self.assertFalse(self.f.source.with_suffix('.vo').exists())

    def test_existing_canonical_output_is_never_replaced(self):
        private, physical = self.physical()
        destination = self.f.source.with_suffix('.vo')
        destination.write_bytes(b'Existing output must remain exact.')
        before = binding(destination)
        with self.assertRaisesRegex(ValueError, 'replace an existing output'):
            self.accept(private, physical)
        self.assertEqual(binding(destination), before)

    def test_private_output_cannot_enter_a_load_path(self):
        private, _ = self.physical()
        runtime = dict(self.f.runtime, physical_flags=['-Q', str(self.f.root), 'Root'])
        with self.assertRaisesRegex(ValueError, 'compiler load path'):
            private_target(runtime, binding(self.f.source), private, self.f.root)

    def test_private_outputs_require_explicit_fixed_policy(self):
        private, _ = self.physical()
        runtime = dict(self.f.runtime)
        runtime.pop('declaration_dag')
        with self.assertRaisesRegex(ValueError, 'opt-in 64/64'):
            private_target(runtime, binding(self.f.source), private, self.f.root)

    def test_changed_publication_refuses_accepted_index(self):
        private, physical = self.physical()
        receipt = self.accept(private, physical)
        value = json.loads(Path(receipt['path']).read_text())
        Path(value['publication']['path']).write_text('{}')
        sealed = S.read(self.snapshot, self.f.reference)
        with self.assertRaisesRegex(ValueError, 'hash differs'):
            S.accepted_objects(sealed, self.snapshot, self.manager.key,
                               binding(self.f.compiler), self.f.runtime['physical_flags'])

    def test_changed_private_object_refuses_before_canonical_write(self):
        private, physical = self.physical()
        private.write_bytes(b'Changed private compiler object.')
        with self.assertRaisesRegex(ValueError, 'sidecar context'):
            self.accept(private, physical)
        self.assertFalse(self.f.source.with_suffix('.vo').exists())

    def test_publication_race_cannot_overwrite_a_destination(self):
        private, physical = self.physical()
        original = os.link
        def race(source, destination, **keywords):
            Path(destination).write_bytes(b'Concurrent output remains exact.')
            return original(source, destination, **keywords)
        with patch('declaration_outputs.os.link', side_effect=race), self.assertRaises(FileExistsError):
            self.accept(private, physical)
        self.assertEqual(self.f.source.with_suffix('.vo').read_bytes(), b'Concurrent output remains exact.')
        self.assertEqual(self.manager.rows, [])

    def test_compiler_validation_waits_for_complete_publication(self):
        started, finished = threading.Event(), threading.Event()
        errors = []
        def validate():
            started.set()
            try:
                S.validate_compiler(self.f.runtime, self.f.reference, self.snapshot,
                                    binding(self.f.source), self.f.compiler)
            except BaseException as error:
                errors.append(error)
            finally:
                finished.set()
        with publication_lock(self.snapshot, exclusive=True):
            worker = threading.Thread(target=validate)
            worker.start()
            self.assertTrue(started.wait(5))
            self.assertFalse(finished.wait(0.05))
        worker.join(5)
        self.assertTrue(finished.is_set())
        self.assertEqual(errors, [])


if __name__ == '__main__':
    unittest.main()
