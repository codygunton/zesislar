"""Fail when a pinned source-engine file differs from its pin record."""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PIN = ROOT / 'tools/block/FP-20261117.json'


class EnginePin(unittest.TestCase):
    def test_pinned_files_match(self):
        record = json.loads(PIN.read_text())
        self.assertTrue(record['files'])
        for row in record['files']:
            with self.subTest(path=row['path']):
                digest = hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest()
                self.assertEqual(digest, row['sha256'],
                                 row['path'] + ' differs from ' + record['version'] + '; write a new pin record.')


if __name__ == '__main__':
    unittest.main()
