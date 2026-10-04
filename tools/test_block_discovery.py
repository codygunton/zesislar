"""Discovery retains contract gaps and distinguishes residual locations."""
import json
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import discovery


class DiscoveryTests(unittest.TestCase):
    def setUp(self):
        self.design = {'blocks': [
            {'entry_pc': '0x10', 'end_pc_exclusive': '0x14',
             'entry_class': 'root', 'successor_pcs': ['0x20']},
            {'entry_pc': '0x20', 'end_pc_exclusive': '0x24',
             'entry_class': 'return', 'successor_pcs': []}]}
        self.cfg = {'functions': [{'entry': 16, 'blocks': [
            {'start': 16, 'end': 20, 'successors': [32]},
            {'start': 32, 'end': 36, 'successors': []}]}]}
        self.state = {'entry': '0x10', 'spatial': ['existingResources args'],
                      'entry_source': {'declaration': 'existingResources'}}

    def test_description_is_a_contract_gap(self):
        ready, gaps = discovery.prepare(self.design, self.cfg, {16: self.state}, 16)
        self.assertEqual(len(ready), 1)
        self.assertEqual(gaps[0]['entry'], '0x20')
        self.assertEqual(gaps[0]['outcomes'], ['contract-gap'])
        self.assertEqual(gaps[0]['first_residual']['class'], 'spec')
        self.assertFalse(gaps[0]['executed'])

    def test_wrong_executable_entry_is_a_contract_gap(self):
        self.state['entry'] = '0x30'
        ready, gaps = discovery.prepare(self.design, self.cfg, {16: self.state}, 16)
        self.assertFalse(ready)
        self.assertIn('different entry PC', gaps[0]['first_residual']['reason'])

    def test_wrong_design_edge_fails_before_execution(self):
        self.design['blocks'][0]['successor_pcs'] = ['0x30']
        with self.assertRaisesRegex(ValueError, 'different block successors'):
            discovery.prepare(self.design, self.cfg, {}, 16)

    def test_duplicate_design_does_not_hide_a_missing_block(self):
        self.design['blocks'].append(dict(self.design['blocks'][0]))
        with self.assertRaisesRegex(ValueError, 'same blocks'):
            discovery.prepare(self.design, self.cfg, {}, 16)

    def test_stall_class_uses_the_residual_pc(self):
        record = {'outcome': 'stalled', 'residual_pcs': [16], 'residual_location': 'known'}
        self.assertEqual(discovery.outcome(record, 16), 'entry-stall')
        record['residual_pcs'] = [20]
        self.assertEqual(discovery.outcome(record, 16), 'execution-stall')
        record['residual_location'] = 'unknown'
        self.assertEqual(discovery.outcome(record, 16), 'unknown-stall')

    def test_first_residual_retains_the_first_goal(self):
        first = {'conclusion': 'FindMemMapsTo ...', 'spatial': ['P']}
        record = {'outcome': 'stalled', 'pending_goals': [first, {'conclusion': 'False'}]}
        row = discovery.summarize(self.design['blocks'][0], [record])
        self.assertEqual(row['first_residual'], first)
        self.assertEqual(row['outcomes'], ['unknown-stall'])

    def test_lookup_class_does_not_require_a_pc_resource(self):
        record = {'outcome': 'stalled', 'residual_pcs': [], 'residual_location': 'unknown',
                  'pending_goals': [{'conclusion': '(find_in_context (FindInstrKind 16 false) continuation)'}]}
        self.assertEqual(discovery.outcome(record, 16), 'instruction-lookup-stall')

    def test_reuse_requires_identical_complete_source(self):
        capture = {'entry': '0x10', 'exit': '0x20', 'outcome': 'stalled',
                   'source_sha256': hashlib.sha256(b'old source').hexdigest(),
                   'performance': {'rc': 0}, 'pending_goals': []}
        previous = {'blocks': [{'entry': '0x10', 'executed': True, 'captures': [capture]}]}
        with patch.object(discovery.chain_root, 'render_probe', return_value='new source'):
            self.assertIsNone(discovery.reuse_capture(self.design['blocks'][0], self.cfg['functions'][0]['blocks'][0], self.state, previous, 'returnAddress'))
        with patch.object(discovery.chain_root, 'render_probe', return_value='old source'):
            result = discovery.reuse_capture(self.design['blocks'][0], self.cfg['functions'][0]['blocks'][0], self.state, previous, 'returnAddress')
            self.assertTrue(result['reused_capture'])

    def test_setup_error_is_not_a_proof_residual(self):
        row = discovery.summarize(self.design['blocks'][0], [{'outcome': 'setup-error',
            'error': 'A dependency is missing', 'proof_phase_entered': False}])
        self.assertFalse(row['executed'])
        self.assertIsNone(row['first_residual'])
        self.assertEqual(row['setup_error'], 'A dependency is missing')

    def test_selected_design_has_24_blocks(self):
        root = Path(__file__).resolve().parents[1]
        design = json.loads((root / 'ZesuSsz/Evidence/decode_item_block_design.json').read_text())
        cfg = json.loads((root / 'build/stock-zisk/cfg.json').read_text())
        ready, gaps = discovery.prepare(design, cfg, {}, int(design['entry_pc'], 16))
        self.assertFalse(ready)
        self.assertEqual(len(gaps), 24)


if __name__ == '__main__':
    unittest.main()
