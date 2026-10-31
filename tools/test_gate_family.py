"""Check reviewed gate measurements without admission or compiler processes."""
from pathlib import Path
import hashlib
import json
import tempfile
import unittest

import gate_family
from correctness_gate import select_peak, select_admission_basis


class GateFamilyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.result = {'target': 'check-fast', 'success': True, 'exit_code': 0,
            'completed_ns': 1, 'aggregate_peak_bytes': 200,
            'measurement_scope': 'Complete owned stock aggregate before guard cleanup.',
            'cache_provenance': {'mode': 'unknown', 'authority': 'Synthetic test data.'}}
        self.profile = {'schema': 'zesu.reviewed-gate-families.v1', 'families': {'check-fast': {
            'command': ['make', '--no-print-directory', '_check-fast'], 'physical_fence_bytes': 500,
            'measurement': {'path': 'result.json', 'sha256': ''}, 'peak_bytes': 200,
            'authority': 'Synthetic test data. This grants no admission authority.'}}}
        self.write()

    def write(self):
        payload = (json.dumps(self.result) + '\n').encode()
        (self.root / 'result.json').write_bytes(payload)
        self.profile['families']['check-fast']['measurement']['sha256'] = hashlib.sha256(payload).hexdigest()
        (self.root / 'profile.json').write_text(json.dumps(self.profile))

    def select(self, target='check-fast', command=None, fence=500):
        return gate_family.select(target, command or ['make', '--no-print-directory', '_check-fast'],
                                  fence, profile=self.root / 'profile.json')

    def test_completed_family_uses_measured_claim_and_preserves_unknown_cache(self):
        result = self.select()
        self.assertEqual(result['claim_bytes'], 300)
        self.assertEqual(result['physical_fence_bytes'], 500)
        self.assertEqual(result['measurement_provenance'], self.result['cache_provenance'])
        self.assertIn('not an uncached-build claim', result['qualification'])

    def test_actual_approved_fast_peak(self):
        result = gate_family.select('check-fast', ['make', '--no-print-directory', '_check-fast'], 120*1024**3)
        self.assertEqual(result['aggregate_peak_bytes'], 2090127360)
        self.assertEqual(result['claim_bytes'], 3135191040)
        self.assertEqual(result['physical_fence_bytes'], 120*1024**3)

    def test_actual_approved_iris_peak(self):
        result = gate_family.select('check-iris', ['make', '--no-print-directory', '_check-iris'], 120*1024**3)
        self.assertEqual(result['aggregate_peak_bytes'], 389505024)
        self.assertEqual(result['claim_bytes'], 584257536)
        self.assertEqual(result['measurement_provenance']['mode'], 'unknown')

    def test_actual_selector_keeps_unmatched_full_fence_and_ceiling(self):
        fence = 120*1024**3
        basis = select_admission_basis({'runs': []}, 'check-fast', ['make', 'other-target'], fence)
        self.assertEqual((basis['reason'], basis['claim_bytes']), ('full_physical_fence', fence))
        matched = select_admission_basis({'runs': []}, 'check-fast',
            ['make', '--no-print-directory', '_check-fast'], fence, 4*1024**3)
        self.assertEqual(matched['claim_bytes'], 4*1024**3)
        for invalid in [-1, True]:
            with self.assertRaises(ValueError):
                select_admission_basis({'runs': []}, 'check-fast', [], fence, invalid)

    def test_unmeasured_gate_still_books_the_full_fence(self):
        self.assertIsNone(self.select('check-iris'))
        self.assertEqual(select_peak({'runs': []}, 'check-iris', physical_fence_bytes=500)['claim_bytes'], 500)

    def test_changed_command_and_fence_do_not_match_family(self):
        self.assertIsNone(self.select(command=['make', '_check-fast']))
        self.assertIsNone(self.select(fence=501))

    def test_each_incomplete_or_changed_measurement_refuses(self):
        for key, value in [('target', 'check-iris'), ('success', False), ('exit_code', True),
                           ('completed_ns', 0), ('aggregate_peak_bytes', 199), ('measurement_scope', 'partial')]:
            with self.subTest(key=key):
                original = self.result[key]
                self.result[key] = value
                self.write()
                with self.assertRaises(ValueError): self.select()
                self.result[key] = original
                self.write()

    def test_wrong_hash_and_missing_output_refuse(self):
        path = self.root / 'result.json'
        path.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'changed'): self.select()
        path.unlink()
        with self.assertRaises(FileNotFoundError): self.select()

    def test_uncontained_path_and_symlink_escape_refuse(self):
        row = self.profile['families']['check-fast']['measurement']
        row['path'] = '../result.json'
        (self.root / 'profile.json').write_text(json.dumps(self.profile))
        with self.assertRaisesRegex(ValueError, 'not contained'): self.select()
        with tempfile.TemporaryDirectory() as directory:
            outside = Path(directory) / 'result.json'
            outside.write_text(json.dumps(self.result))
            (self.root / 'escape').symlink_to(outside)
            row['path'] = 'escape'
            (self.root / 'profile.json').write_text(json.dumps(self.profile))
            with self.assertRaisesRegex(ValueError, 'leaves'): self.select()


if __name__ == '__main__': unittest.main()
