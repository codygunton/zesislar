"""Check derived unit data without changing production validation."""
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import _historical_fixtures as F


class HistoricalFixtures(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.bundle = self.root / 'bundle'
        (self.bundle / 'authentic').mkdir(parents=True)
        self.manifest = {'schema': 'harness.authentic-fixtures.v1',
                         'roots': {'/fixture-origin': 'data'}, 'files': {}, 'hashes': {}}
        for name, value in [('BUNDLE', self.bundle), ('_MANIFEST', self.manifest),
                            ('_ROOT', self.root / 'derived'), ('_DONE', {}),
                            ('_HASHES', {}), ('_BUILDING', set())]:
            self.enterContext(patch.object(F, name, value))
        self.source = '/fixture-origin/Source.v'
        self.body = b'(* Exact source fixture. No proof execution. *)\n'
        self.source_sha = self.add(self.source, self.body)

    def add(self, origin, payload, *, kind='raw'):
        sha = hashlib.sha256(payload).hexdigest()
        (self.bundle / 'authentic' / (sha + '.gz')).write_bytes(gzip.compress(payload, mtime=0))
        self.manifest['files'][origin] = {'sha256': sha, 'size': len(payload),
                                         'mode': 0o644, 'format': kind}
        self.manifest['hashes'].setdefault(sha, []).append(origin)
        return sha

    def test_source_bytes_stay_exact(self):
        self.assertEqual(F.materialize(self.source).read_bytes(), self.body)
        self.assertEqual(F._HASHES[self.source], self.source_sha)

    def test_typed_paths_relocate_without_changing_measurements(self):
        origin = '/fixture-origin/RESULT.json'
        data = {'source': {'path': self.source, 'sha256': self.source_sha},
                'peak_bytes': 1234, 'success': True, 'compiler': '/usr/bin/coqc'}
        authentic = json.dumps(data).encode()
        original_sha = self.add(origin, authentic, kind='json')
        result = F.materialize(origin)
        derived = json.loads(result.read_bytes())
        self.assertEqual(derived['source']['path'], str(F.materialize(self.source)))
        self.assertEqual(derived['source']['sha256'], self.source_sha)
        self.assertEqual(derived['peak_bytes'], 1234)
        self.assertTrue(derived['success'])
        self.assertEqual(derived['compiler'], '/usr/bin/coqc')
        self.assertNotEqual(hashlib.sha256(result.read_bytes()).hexdigest(), original_sha)
        self.assertEqual(gzip.decompress((self.bundle / 'authentic' / (original_sha + '.gz')).read_bytes()), authentic)

    def test_dependent_container_hash_changes_to_derived_bytes(self):
        first = '/fixture-origin/FIRST.json'
        sha = self.add(first, json.dumps({'path': self.source}).encode(), kind='json')
        second = '/fixture-origin/SECOND.json'
        self.add(second, json.dumps({'input': {'path': first, 'sha256': sha}}).encode(), kind='json')
        row = json.loads(F.materialize(second).read_bytes())['input']
        self.assertEqual(row['sha256'], hashlib.sha256(Path(row['path']).read_bytes()).hexdigest())
        self.assertNotEqual(row['sha256'], sha)

    def test_missing_authentic_input_stays_missing(self):
        with self.assertRaisesRegex(FileNotFoundError, 'authentic fixture is unavailable'):
            F.materialize('/fixture-origin/MISSING.json')
        self.assertFalse((F.root() / 'data/MISSING.json').exists())

    def test_modified_authentic_payload_refuses(self):
        (self.bundle / 'authentic' / (self.source_sha + '.gz')).write_bytes(gzip.compress(b'changed'))
        with self.assertRaisesRegex(ValueError, 'authentic fixture bytes changed'):
            F.materialize(self.source)

    def test_hash_dependency_cycle_refuses(self):
        origin = '/fixture-origin/CYCLE.json'
        self.add(origin, json.dumps({'input': '0' * 64}).encode(), kind='json')
        self.manifest['hashes']['0' * 64] = [origin]
        with self.assertRaisesRegex(ValueError, 'hash dependencies contain a cycle'):
            F.materialize(origin)


if __name__ == '__main__':
    unittest.main()
