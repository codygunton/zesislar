"""Reject alias substitutions without exposing runtime paths in TRACE."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_bounded_aliases import AliasProjection, AliasDocument, verify_aliases, write_alias_map, verify_alias_files
from trace_block_stream import json_document


class AliasTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.base = Path(self.directory.name)
        self.root = self.base / 'evidence'
        self.root.mkdir()
        self.source = self.fixture(self.root, 10)

    def fixture(self, root, process):
        refs = []
        for name, data in [('state.marshal', b'complete term'), ('context.json', b'{"context":true}')]:
            path = root / ('kernel/process-%d' % process) / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            refs.append({'path': path.relative_to(root).as_posix(), 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
        return {'session': {'id': 'logical-session'}, 'points': [{'goal': 'bounded goal',
            'complete_sidecar': refs[0], 'context_ref': refs[1]}], 'snapshots': {'entry': {'complete_sidecar': refs[0]}},
            'identity': {'prefix': {'path': '_build/original-prefix.txt', 'sha256': 'a' * 64}}}

    def projected(self):
        projection = AliasProjection(self.source, self.root)
        stable = json.loads(''.join(json_document(projection.stable)))
        mapping = deepcopy(projection.mapping)
        return stable, mapping

    def test_aliases_hide_paths_and_reuse_exact_targets(self):
        stable, mapping = self.projected()
        text = json.dumps(stable)
        self.assertNotIn('process-10', text)
        self.assertNotIn('state.marshal', text)
        self.assertEqual(len(mapping['aliases']), 2)
        self.assertEqual(sorted(row['occurrences'] for row in mapping['aliases']), [1, 2])
        self.assertEqual(verify_aliases(stable, mapping, self.source, self.root)['verified_aliases'], 2)

    def test_synthetic_process_path_change_preserves_body_bytes(self):
        first = ''.join(json_document(AliasProjection(self.source, self.root).stable))
        other = self.base / 'other'
        other.mkdir()
        second = ''.join(json_document(AliasProjection(self.fixture(other, 99), other).stable))
        self.assertEqual(first, second)

    def test_missing_alias_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'].pop()
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_duplicate_name_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][1]['name'] = mapping['aliases'][0]['name']
        with self.assertRaisesRegex(ValueError, 'repeats a logical name'):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_duplicate_target_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][1]['reference'] = mapping['aliases'][0]['reference']
        with self.assertRaisesRegex(ValueError, 'repeats a physical target'):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_substituted_valid_target_rejects(self):
        stable, mapping = self.projected()
        first, second = mapping['aliases']
        first['reference'], second['reference'] = second['reference'], first['reference']
        with self.assertRaisesRegex(ValueError, 'source associations'):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_foreign_target_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][0]['reference']['path'] = '../foreign.marshal'
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_missing_target_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][0]['reference']['path'] = 'missing.marshal'
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_corrupt_target_hash_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][0]['reference']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_substituted_stable_pointer_rejects(self):
        stable, mapping = self.projected()
        stable['points'][0]['complete_sidecar'] = stable['points'][0]['context_ref']
        with self.assertRaisesRegex(ValueError, 'exact logical artifact projection'):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_missing_artifact_descriptor_rejects(self):
        stable, mapping = self.projected()
        stable['artifacts'].pop(next(iter(stable['artifacts'])))
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_substituted_printed_goal_rejects(self):
        stable, mapping = self.projected()
        stable['points'][0]['goal'] = 'different goal'
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_prefix_identity_stays_exact(self):
        stable, mapping = self.projected()
        self.assertEqual(stable['identity'], self.source['identity'])

    def test_absolute_owned_reference_becomes_logical(self):
        value = self.source['points'][0]['complete_sidecar']
        value['path'] = str(self.root / value['path'])
        stable, mapping = self.projected()
        self.assertEqual(mapping['aliases'][0]['reference']['path'], 'kernel/process-10/state.marshal')

    def test_absolute_foreign_reference_rejects(self):
        self.source['points'][0]['complete_sidecar']['path'] = str(self.base / 'outside')
        with self.assertRaisesRegex(ValueError, 'outside'):
            AliasProjection(self.source, self.root)

    def test_streaming_protocol_preserves_values(self):
        projection = AliasProjection(self.source, self.root)
        self.assertEqual(len(projection.stable['points']), 1)
        self.assertIn('goal', projection.stable['points'][0])
        with self.assertRaises(TypeError):
            json.dumps(projection.stable)

    def test_inline_artifact_round_trip(self):
        projection = AliasProjection(self.source, self.root)
        output = self.base / 'aliases'
        result = write_alias_map(output, projection.mapping, index_dir=self.base / 'write-index')
        with AliasDocument(output, result['artifact'], index_dir=self.base / 'read-index') as loaded:
            self.assertEqual(verify_aliases(projection.stable, loaded, self.source, self.root)['verified_aliases'], 2)

    def test_inline_duplicate_json_keys_reject(self):
        directory = self.base / 'aliases'
        directory.mkdir()
        payload = b'{"schema":1,"schema":1,"session":"s","aliases":[]}'
        (directory / 'ALIASES.json').write_bytes(payload)
        ref = {'path': 'ALIASES.json', 'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': len(payload)}
        with self.assertRaisesRegex(ValueError, 'repeats a field'):
            AliasDocument(directory, ref, index_dir=self.base / 'read-index')

    def test_unused_alias_rejects(self):
        stable, mapping = self.projected()
        path = self.root / 'other.marshal'
        path.write_bytes(b'other term')
        mapping['aliases'].append({'name': 'artifact-00000003', 'reference': {'path': 'other.marshal',
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest(), 'bytes': path.stat().st_size},
            'first_use': '#/unused', 'occurrences': 1})
        with self.assertRaisesRegex(ValueError, 'source associations'):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_wrong_occurrence_count_rejects(self):
        stable, mapping = self.projected()
        mapping['aliases'][0]['occurrences'] += 1
        with self.assertRaises(ValueError):
            verify_aliases(stable, mapping, self.source, self.root)

    def test_empty_projection_keeps_an_empty_alias_map(self):
        source = {'session': {'id': 's'}, 'points': [], 'snapshots': {}, 'residual': None}
        projection = AliasProjection(source, self.root)
        self.assertEqual(projection.mapping['aliases'], [])
        self.assertEqual(verify_aliases(projection.stable, projection.mapping, source, self.root)['verified_aliases'], 0)

    def test_sealed_alias_artifact_set_rejects_extra_files(self):
        projection = AliasProjection(self.source, self.root)
        directory = self.base / 'aliases'
        result = write_alias_map(directory, projection.mapping, index_dir=self.base / 'write-index')
        verify_alias_files(directory, result['files'])
        (directory / 'unbound.json').write_text('{}')
        with self.assertRaisesRegex(ValueError, 'complete seal'):
            verify_alias_files(directory, result['files'])

    def test_sealed_alias_artifact_set_rejects_duplicate_rows(self):
        projection = AliasProjection(self.source, self.root)
        directory = self.base / 'aliases'
        result = write_alias_map(directory, projection.mapping, index_dir=self.base / 'write-index')
        with self.assertRaisesRegex(ValueError, 'repeats a path'):
            verify_alias_files(directory, result['files'] * 2)

    def test_sealed_alias_artifact_set_rejects_links(self):
        projection = AliasProjection(self.source, self.root)
        directory = self.base / 'aliases'
        result = write_alias_map(directory, projection.mapping, index_dir=self.base / 'write-index')
        (directory / 'foreign').symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symlink'):
            verify_alias_files(directory, result['files'])

    def test_oversized_alias_map_requires_exact_writer(self):
        mapping = {'schema': 1, 'session': 's', 'aliases': ['x' * 2_100_000]}
        with self.assertRaisesRegex(ValueError, 'exact bound writer'):
            write_alias_map(self.base / 'aliases', mapping, index_dir=self.base / 'write-index')


if __name__ == '__main__':
    unittest.main()
