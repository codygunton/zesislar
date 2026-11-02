"""Keep unmatched compiler measurements at the existing class defaults."""
import json
from pathlib import Path
import unittest

import compiler_snapshot as S
from declaration_resources import GIB, weights
from entry_chain import binding, save
import test_declaration_outputs as fixtures


class DeclarationResourceTests(unittest.TestCase):
    def setUp(self):
        self.case = fixtures.DeclarationOutputTests()
        self.case.setUp()
        self.addCleanup(self.case.doCleanups)
        self.f = self.case.f

    def profile(self, *, peak=900000, module='Example.Control'):
        private, physical = self.case.physical()
        value = json.loads(Path(physical['path']).read_text())
        value['peak_rss_KiB'] = peak
        physical = S._publish(physical['path'], value, replace=True)
        receipt = self.case.accept(private, physical)
        path = self.f.root / 'RESOURCE-PROFILE.json'
        save(path, {'schema': 'entry-chain.declaration-resources.v1',
                    'modules': [{'module': module, 'receipt': receipt}]})
        return binding(path)

    def select(self, profile=None, **changes):
        options = dict(ordered=['Example.Control'], modules=self.f.runtime['module_files'],
                       workspace=self.f.root, compiler=binding(self.f.compiler),
                       flags=self.f.runtime['physical_flags'], profile=profile)
        options.update(changes)
        return weights(**options)

    def test_unknown_module_keeps_16_gib_class_default(self):
        result = self.select()
        self.assertEqual(result['weights']['Example.Control'], 16 * GIB)
        self.assertEqual(result['evidence']['Example.Control']['reason'], 'unmeasured_class_default')

    def test_matching_physical_receipt_uses_1_5_times_peak(self):
        result = self.select(self.profile())
        self.assertEqual(result['weights']['Example.Control'], 900000 * 1024 * 3 // 2)
        self.assertEqual(result['evidence']['Example.Control']['reason'], 'completed_matching_measurement')

    def test_small_completed_measurement_keeps_1_gib_floor(self):
        result = self.select(self.profile(peak=1))
        self.assertEqual(result['weights']['Example.Control'], GIB)

    def test_missing_or_invalid_peak_keeps_class_default(self):
        for value in [None, 0, True]:
            with self.subTest(peak=value):
                # Each receipt needs its own immutable fixture namespace.
                case = DeclarationResourceTests()
                case.setUp()
                try:
                    result = case.select(case.profile(peak=value))
                    self.assertEqual(result['weights']['Example.Control'], 16 * GIB)
                finally:
                    case.doCleanups()

    def test_changed_source_keeps_class_default(self):
        profile = self.profile()
        self.f.source.write_text('Changed nonproof declaration fixture.\n')
        result = self.select(profile)
        self.assertEqual(result['weights']['Example.Control'], 16 * GIB)
        self.assertEqual(result['evidence']['Example.Control']['reason'], 'unmatched_measurement')

    def test_changed_flags_keep_class_default(self):
        result = self.select(self.profile(), flags=['-Q', str(self.f.library), 'Changed'])
        self.assertEqual(result['weights']['Example.Control'], 16 * GIB)

    def test_unauthorized_module_refuses_the_profile(self):
        profile = self.profile(module='Other.Control')
        with self.assertRaisesRegex(ValueError, 'another module'):
            self.select(profile)

    def test_changed_receipt_refuses_before_fallback(self):
        profile = self.profile()
        row = json.loads(Path(profile['path']).read_text())['modules'][0]
        Path(row['receipt']['path']).write_text('{}')
        with self.assertRaises(ValueError):
            self.select(profile)


if __name__ == '__main__':
    unittest.main()
