"""Check actual Sail source resolution without compiling any proof."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import scratch
from installed_mappings import InstalledMappings


class SailMappingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.library = self.root / 'sail-stdpp'
        self.library.mkdir()
        project = Path(scratch.__file__).resolve().parents[3]
        self.original = project / 'generated/sail-stdpp/Real.v'
        data = self.original.read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(),
                         'e471c1d9af130af543d84c122bc985c6c8ab0e4327ca0ba86b096f9616fb6817')
        self.source = self.library / 'Real.v'
        self.source.write_bytes(data)
        self.values = self.library / 'Values.v'
        self.values.write_bytes((project / 'generated/sail-stdpp/Values.v').read_bytes())
        self.object = self.values.with_suffix('.vo')
        # A dependency-resolver fixture, never a compiled or admission artifact.
        self.object.write_bytes(b'unit dependency object')
        self.coq = Path(os.environ['OPAM_SWITCH_PREFIX']) / 'lib/coq/theories'

    def flags(self, mode):
        return ['-R', str(self.coq), 'Coq', mode, str(self.library), 'SailStdpp']

    def test_actual_source_and_synthetic_import_resolve_the_same_object(self):
        physical_flags = self.flags('-Q')
        installed = InstalledMappings(physical_flags, receipt_dir=self.root / 'receipts')
        original_flags, original_roots = list(installed.flags), [dict(row) for row in installed.roots]
        origin = {'path': str(self.source), 'sha256': hashlib.sha256(self.source.read_bytes()).hexdigest()}
        dependency_flags = installed.dependency_flags(origin)
        self.assertEqual(dependency_flags, ['-boot', '-dyndep', 'no', *self.flags('-R')])
        before = (self.source.read_bytes(), self.object.read_bytes(), self.object.stat().st_ino)
        actual = subprocess.run([str(installed.coqdep), *dependency_flags, str(self.source)],
                                cwd=self.root, capture_output=True, text=True, check=True)
        self.assertEqual(actual.stderr, '')
        self.assertIn(str(self.object), actual.stdout)
        installed.register_source(self.source.read_text(), self.source)
        self.assertEqual(installed.resolve('Values'), self.values.absolute())
        self.assertEqual(installed.resolutions['Values']['canonical'], 'SailStdpp.Values')
        receipt = next((self.root / 'receipts').glob('*.json'))
        query = json.loads(receipt.read_text())
        self.assertEqual(query['argv'][1:-1], dependency_flags)
        self.assertEqual(query['request']['statement'], 'Require Import Values.\n')
        self.assertEqual(query['stderr'], '')
        self.assertEqual(before, (self.source.read_bytes(), self.object.read_bytes(), self.object.stat().st_ino))
        self.assertEqual(self.source.read_bytes(), self.original.read_bytes())
        self.assertEqual(physical_flags, self.flags('-Q'))
        self.assertEqual(installed.flags, original_flags)
        self.assertEqual(installed.roots, original_roots)

    def test_outside_source_keeps_q_mapping_and_refuses_sibling_import(self):
        installed = InstalledMappings(self.flags('-Q'), receipt_dir=self.root / 'receipts')
        outside = self.root / 'Outside.v'
        outside.write_text('Require Import Values.\n')
        installed.register_source(outside.read_text(), outside)
        self.assertEqual(installed.dependency_flags(installed.requests['Values'][0]['origin']), installed.flags)
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            installed.resolve('Values')
        receipt = json.loads(next((self.root / 'receipts').glob('*.json')).read_text())
        self.assertEqual(receipt['argv'][1:-1], installed.flags)
        self.assertIn('module-not-found', receipt['stderr'])

    def test_other_theory_keeps_q_mapping(self):
        installed = InstalledMappings(['-Q', str(self.library), 'OtherTheory'])
        origin = {'path': str(self.source), 'sha256': hashlib.sha256(self.source.read_bytes()).hexdigest()}
        self.assertEqual(installed.dependency_flags(origin), installed.flags)

    def test_changed_bound_source_refuses(self):
        installed = InstalledMappings(self.flags('-Q'))
        installed.register_source(self.source.read_text(), self.source)
        self.source.write_text(self.source.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'request source changed'):
            installed.resolve('Values')

    def test_receipts_preserve_distinct_source_contexts(self):
        installed = InstalledMappings(self.flags('-Q'), receipt_dir=self.root / 'receipts')
        outside = self.root / 'Outside.v'
        outside.write_text('Require Import Values.\n')
        installed.register_source(self.source.read_text(), self.source)
        installed.register_source(outside.read_text(), outside)
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            installed.resolve('Values')
        receipts = [json.loads(path.read_text()) for path in (self.root / 'receipts').glob('*.json')]
        self.assertEqual(len(receipts), 2)
        self.assertEqual({row['request']['origin']['path'] for row in receipts}, {str(self.source), str(outside)})
        self.assertEqual(sum(not row['stderr'] for row in receipts), 1)

    def test_cached_inside_answer_does_not_suppress_outside_refusal(self):
        installed = InstalledMappings(self.flags('-Q'), receipt_dir=self.root / 'receipts')
        installed.register_source(self.source.read_text(), self.source)
        self.assertEqual(installed.resolve('Values'), self.values)
        outside = self.root / 'Outside.v'
        outside.write_text('Require Import Values.\n')
        installed.register_source(outside.read_text(), outside)
        self.assertNotIn('Values', installed.resolutions)
        with self.assertRaisesRegex(ValueError, 'no actual installed mapping'):
            installed.resolve('Values')

    def test_old_q_mapping_fails_for_actual_and_synthetic_source(self):
        installed = InstalledMappings(self.flags('-Q'))
        query = self.root / 'Import.v'
        query.write_text('Require Import Values.\n')
        for source in (self.source, query):
            result = subprocess.run([str(installed.coqdep), '-boot', '-dyndep', 'no',
                                     *self.flags('-Q'), str(source)],
                                    cwd=self.root, capture_output=True, text=True, check=True)
            self.assertIn('module-not-found', result.stderr)
        self.assertEqual(self.source.read_bytes(), self.original.read_bytes())


if __name__ == '__main__':
    unittest.main()
