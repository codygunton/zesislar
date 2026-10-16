"""Check bounded package selection without a dependency build or proof run."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import trace_block_bounded_package as package
import trace_block_prepare as prepare


class BoundedPackageTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def configuration(self, dependency='RecordUpdate Ltac2'):
        (self.root / 'dune-project').write_text('(lang dune 3.8)\n(package (name old))\n')
        theory = self.root / 'ZesuSsz/dune'
        theory.parent.mkdir()
        theory.write_text('(coq.theory (name ZesuSsz) (theories ' + dependency + '))\n')

    def test_root_package_layout_is_idempotent(self):
        self.configuration()
        package.configure(self.root)
        first = ((self.root / 'dune-project').read_bytes(), (self.root / 'ZesuSsz/dune').read_bytes())
        package.configure(self.root)
        self.assertEqual(first, ((self.root / 'dune-project').read_bytes(), (self.root / 'ZesuSsz/dune').read_bytes()))
        self.assertIn('(name old)', first[0].decode())
        self.assertIn('Ltac2 P0Bounded))', first[1].decode())
        self.assertEqual(first[0].decode().count('(name p0-bounded-trace)'), 1)

    def test_existing_filtered_dependency_uses_separate_bounded_theory(self):
        self.configuration('RecordUpdate Ltac2 P0Filtered')
        package.configure(self.root)
        self.assertIn('Ltac2 P0Bounded))', (self.root / 'ZesuSsz/dune').read_text())

    def test_nested_project_rejects(self):
        self.configuration()
        nested = self.root / package.BOUNDED / 'dune-project'
        nested.parent.mkdir(parents=True)
        nested.write_text('(lang dune 3.8)')
        with self.assertRaisesRegex(ValueError, 'root Dune project'):
            package.configure(self.root)

    def test_unknown_theory_boundary_rejects(self):
        self.configuration('Other')
        with self.assertRaisesRegex(ValueError, 'unsupported boundary'):
            package.configure(self.root)

    def test_alias_inventory_preserves_each_row_and_canonicalizes_files(self):
        artifact = self.root / 'runtime.cmxs'
        artifact.write_bytes(b'pinned runtime')
        alias = self.root / 'alias.cmxs'
        alias.symlink_to(artifact)
        artifacts, aliases = package.canonical_artifacts([artifact, alias])
        self.assertEqual(len(artifacts), 1)
        self.assertEqual(len(aliases), 2)
        self.assertEqual(artifacts[0]['path'], str(artifact.resolve()))
        self.assertTrue(all(row['canonical'] == artifacts[0] for row in aliases))

    def test_broken_runtime_alias_rejects(self):
        alias = self.root / 'bad'
        alias.symlink_to(self.root / 'absent')
        with self.assertRaises(FileNotFoundError):
            package.canonical_artifacts([alias])

    def test_directory_artifact_rejects(self):
        with self.assertRaisesRegex(ValueError, 'regular file'):
            package.canonical_artifacts([self.root])

    def test_install_stage_keeps_writer_reader_and_package(self):
        self.assertEqual(package.INSTALL_TARGETS[0], 'p0-bounded-trace.install')
        self.assertIn(package.READER_TARGET, package.INSTALL_TARGETS)
        self.assertIn(package.WRITER_TARGET, package.INSTALL_TARGETS)
        self.assertIn('/Filtered/', package.WRITER_TARGET)

    def test_explicit_filtered_compatibility_remains(self):
        self.assertIs(prepare.preparation_package({}), prepare.package)
        self.assertIs(prepare.preparation_package({'capture_surface_policy': 'bounded-kernel-v1'}), package)
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            prepare.preparation_package({'capture_surface_policy': 'unknown'})

    def test_policy_changes_preparation_key(self):
        request = {'scope': {}, 'rule_set': [], 'stop': {}}
        self.assertNotEqual(prepare.request_key(request), prepare.request_key(dict(request, capture_surface_policy='bounded-kernel-v1')))

    def test_bounded_return_wrappers_preserve_original_bodies(self):
        owner = Path(__file__).resolve().parents[3]
        # Use source snippets with the actual native Hint boundary.
        source = (owner / 'unused').as_posix()
        client = 'ReturnRoute.normalize'
        original = 'exact original_body'
        observed, descriptor = prepare.around(client, original, {'kind': 'rule', 'value': 'ReturnRoute'}, 'ReturnRoute', 'LiTactic')
        output, descriptors = prepare.bounded_observation(original, observed, {client: descriptor})
        self.assertIn('ltac1:(' + original + ')', output)
        self.assertIn('trace_bounded_filtered', output)
        self.assertIn('trace_bounded_ltac1_guard', output)
        self.assertNotIn('trace_block_', output)
        row = descriptors[client]
        self.assertEqual(row['commands']['whole-rule'], original)
        self.assertEqual(row['trials'][-1]['command'], original)
        self.assertEqual(sum(item['clause'] == 'whole-rule' for item in row['trials']), 1)
        self.assertEqual(row['typed_guard']['sha256'], hashlib.sha256(row['typed_guard']['command'].encode()).hexdigest())
        reference = prepare.install_guard_manifest(self.root, descriptors, bounded=True)
        env = prepare.preparation_guard_environment(self.root, descriptors, reference, package)
        self.assertEqual(env['ZESU_TRACE_GUARD_MANIFEST'], reference['path'])

    def runtime_request(self):
        values = {}
        for name in ('plugin', 'bridge', 'writer'):
            path = self.root / name
            path.write_bytes(name.encode())
            values[name] = package.reference(path, sized=False)
        return {'workspace': str(self.root), 'observer_runtime': {
            'surface_policy': 'bounded-kernel-v1', 'plugin': values['plugin'],
            'bridge': values['bridge'], 'coqpath': str(self.root),
            'kernel_reader': {}, 'kernel_toolchain': {}}, 'chunk_writer': values['writer']}

    def test_cached_reference_schemas_reject_extra_size(self):
        for name in ('plugin', 'bridge', 'writer'):
            with self.subTest(name=name):
                request = self.runtime_request()
                item = request['chunk_writer'] if name == 'writer' else request['observer_runtime'][name]
                item['bytes'] = Path(item['path']).stat().st_size
                with self.assertRaisesRegex(ValueError, 'unsupported fields'):
                    package.validate_runtime(request)

    def test_cached_reference_paths_reject_external_artifacts(self):
        with tempfile.TemporaryDirectory() as external:
            path = Path(external) / 'artifact'
            path.write_bytes(b'external')
            for name in ('plugin', 'bridge', 'writer'):
                with self.subTest(name=name):
                    request = self.runtime_request()
                    if name == 'writer':
                        request['chunk_writer'] = package.reference(path, sized=False)
                    else:
                        request['observer_runtime'][name] = package.reference(path, sized=False)
                    with self.assertRaisesRegex(ValueError, 'leaves its workspace'):
                        package.validate_runtime(request)

    def test_existing_observer_source_rejects(self):
        with self.assertRaisesRegex(ValueError, 'already contains'):
            prepare.bounded_observation('trace_block_filtered', 'trace_block_filtered', {})


if __name__ == '__main__':
    unittest.main()
