"""Check measured ledger boundaries without asserting native closure."""
import json
from pathlib import Path
import re
import unittest

from check_decode_item_route_repair import historical_file

ROOT = Path(__file__).resolve().parents[2]
SITES = ['6960', '697c', '698c', '69b0', '69e8', '6a08', '6a24', '6a38',
         '6a40', '6a78', '6aa8', '6ac4', '6ad8', '6ae0', '6b08']


class PrecommitmentLedgerTests(unittest.TestCase):
    def setUp(self):
        self.ledger = json.loads((ROOT / 'ZesuSsz/Evidence/precommitment/LEDGER.json').read_text())
        self.rows = {row['block']: row for row in self.ledger['rows']}

    def test_exact_open_inventory_matches_checked_module(self):
        self.assertEqual([row['block'] for row in self.ledger['rows']], SITES)
        module = (ROOT / 'ZesuSsz/Evidence/DecodeItemPrecommitmentLedger.v').read_text()
        self.assertEqual(re.findall(r'precommitmentBlock := 0x800d([0-9a-f]{4})', module), SITES)
        self.assertNotIn('precommitmentStatus := PrecommitmentUnknown', module)
        self.assertEqual(len(self.rows), 15)

    def test_all_contained_bindings_match(self):
        def visit(value):
            if isinstance(value, dict):
                if 'path' in value and 'sha256' in value:
                    historical_file(value, ROOT)
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)
        visit(self.ledger)

    def test_monitored_stops_do_not_claim_requested_assignment(self):
        for site in ('6960', '697c', '69e8'):
            row = self.rows[site]
            self.assertEqual(row['status'], 'MonitoredOperationRecorded')
            self.assertIn('unavailable', row['required_assignment'])
            self.assertIn('restores', row['rollback'])
            self.assertFalse(row['native_closure_claim'])
            self.assertIn('first_global_commitment', row['limits'])

    def test_array_selection_preserves_unresolved_index_and_continuation(self):
        for site in ('698c', '69b0', '6a40', '6a78', '6ae0', '6b08'):
            row = self.rows[site]
            self.assertEqual(row['status'], 'ArraySelectionRecorded')
            self.assertEqual(row['operation'], '1: liFindInContext.')
            self.assertIn('index', row['required_assignment'])
            self.assertFalse(row['native_closure_claim'])
            self.assertEqual(row['retained_scope']['verification_root'],
                             'dc832abbf6291a9008dfb949ef8638bcdfc4b490')
            self.assertEqual(row['retained_scope']['declaration_root'],
                             'e17a8888ac3aed392397113fb97d0a244a2bba6e')

    def test_loop_findings_preserve_failed_old_value_applications(self):
        for site in ('6a24', '6ac4'):
            row = self.rows[site]
            self.assertEqual(row['status'], 'CommittedSuccessorMismatch')
            self.assertIn('i+1', row['required_assignment'])
            self.assertEqual(len(row['measured_applications']), 2)
            self.assertFalse(row['native_closure_claim'])
            for application in row['measured_applications']:
                self.assertFalse(application['native_assignment_executed'])
                self.assertEqual(application['fixture']['site'], site)


if __name__ == '__main__':
    unittest.main()
