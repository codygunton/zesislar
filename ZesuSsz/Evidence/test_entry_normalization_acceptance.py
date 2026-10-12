"""Keep the private normalization identity inside the linked acceptance checker."""
import copy
import json
import unittest
from check_decode_item_route_repair import (
    ENTRY_NORMALIZATION_INDEX, ENTRY_NORMALIZATION_IDENTITY,
    entry_normalization_binding, entry_normalization_acceptance,
)


class EntryNormalizationAcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.index = json.loads(ENTRY_NORMALIZATION_INDEX.read_text())

    def test_exact_inventory(self):
        entry_normalization_binding(self.index)
        self.assertEqual(self.index['repair_identity'], ENTRY_NORMALIZATION_IDENTITY)

    def test_no_certificates_rejected(self):
        with self.assertRaises((ValueError, KeyError)):
            entry_normalization_acceptance(self.index, {})

    def test_other_identity_rejected(self):
        for key in ENTRY_NORMALIZATION_IDENTITY:
            candidate = copy.deepcopy(self.index)
            candidate['repair_identity'][key] += '_other'
            with self.subTest(key=key), self.assertRaises(ValueError):
                entry_normalization_binding(candidate)

    def test_each_statement_and_loop_provenance_retained(self):
        for number in range(9):
            for field in ('native_statement', 'capture', 'capture_scope'):
                candidate = copy.deepcopy(self.index)
                candidate['cases'][number][field] = 'different'
                with self.subTest(site=number, field=field), self.assertRaises(ValueError):
                    entry_normalization_binding(candidate)

    def test_import_or_control_change_rejected(self):
        for key in ('ON_imports', 'reject_controls', 'control_module', 'loop_negative_controls'):
            candidate = copy.deepcopy(self.index)
            candidate[key] = []
            with self.subTest(key=key), self.assertRaises(ValueError):
                entry_normalization_binding(candidate)

    def test_changed_preparation_rejected(self):
        candidate = copy.deepcopy(self.index)
        candidate['reviewed_preparation']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            entry_normalization_binding(candidate)


if __name__ == '__main__':
    unittest.main()
