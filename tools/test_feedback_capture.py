"""Preserve full feedback and reuse completed boundary probes."""
import hashlib
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent/'block'))
import compare_ram_fault as comparison
import discovery
import feedback_mcp


class FeedbackTests(unittest.TestCase):
    def test_full_feedback_replaces_only_the_matching_sdk_display(self):
        raw = 'CHAIN-GOAL-BEGIN active\n' + 'x'*50001 + '\nCHAIN-GOAL-END'
        display = raw[:50000] + '\n... (truncated)'
        with TemporaryDirectory() as directory:
            feedback_mcp.save_feedback(SimpleNamespace(feedback=[(3, raw)]), display, directory)
            result = discovery.feedback({'feedback': [['all: record.', display]]}, directory)
            self.assertEqual(result, raw)
            self.assertEqual(discovery.feedback({'feedback': [['idtac.', 'other']]}, directory), 'other')
            p = next(Path(directory).glob('*.json'))
            payload = json.loads(p.read_text());payload['raw'] += 'corruption'
            p.write_text(json.dumps(payload))
            with self.assertRaisesRegex(ValueError, 'hash'):
                discovery.feedback({'feedback': [['all: record.', display]]}, directory)

    def test_incomplete_record_is_a_capture_error_with_inherited_debts(self):
        block = {'start': '0x10', 'end': '0x14', 'successors': ['0x20']}
        with patch.object(discovery.chain_root.gen_block.call_sites, 'premises', return_value=([], [], [])), \
                patch.object(discovery.chain_root, 'inherited_debts', return_value=[{'debt': 'retained'}]):
            records = discovery.parse_capture((Path(__file__).parent/'block/testdata/truncated_root_recorder.txt').read_text(),
                                              {'binders': [], 'spatial': [], 'coq': []}, block, 0x20)
        self.assertEqual(records[0]['outcome'], 'capture-error')
        self.assertFalse(records[0]['capture_complete'])
        self.assertFalse(records[0]['contract_closed'])
        self.assertEqual(records[0]['inherited_debts'], [{'debt': 'retained'}])

    def test_resume_inputs_reject_contract_changes_and_record_capture_changes(self):
        workspace = Path('/workspace')
        frozen = {'/workspace/ZesuSsz/Contracts/Entry.v': 'old',
                  '/workspace/tools/block/discovery.py': 'old-driver'}
        current = {**frozen, '/workspace/tools/block/discovery.py': 'new-driver'}
        changes = comparison.verify_resume_inputs(frozen, current, workspace)
        self.assertEqual(changes['/workspace/tools/block/discovery.py']['previous'], 'old-driver')
        with self.assertRaisesRegex(ValueError, 'immutable'):
            comparison.verify_resume_inputs(frozen, {**current, '/workspace/ZesuSsz/Contracts/Entry.v': 'changed'}, workspace)

    def test_resume_reuses_completed_boundary_and_rejects_changed_source(self):
        with TemporaryDirectory() as directory:
            row = {'entry_pc': '0x10', 'entry_class': 'root'}
            block = {'start': '0x10', 'end': '0x14', 'successors': ['0x20', '0x30']}
            options = {'out': directory, 'probe_targets': ['0x20']}
            job = ('switch-off', row, block, {}, options)
            p = Path(directory)/'probes'/'block_0x10_800d20.v'
            # Use the driver's boundary naming policy.
            p = Path(directory)/'probes'/('block_0x10_' + comparison.chain_root.boundary_label(0x20) + '.v')
            p.parent.mkdir();p.write_text('frozen source')
            p.with_suffix('.out').write_text('CHAIN-GOAL-BEGIN active\nexit=0 ms=1000 rss_kb=2048\n')
            p.with_suffix('.mcp.json').write_text(json.dumps([{'success': True}]))
            p.with_suffix('.steps.json').write_text(json.dumps([{'label': 'primary-unchanged-zesu_block',
                'arguments': {'body': 'try zesu_block.', 'timeout': 300}}]))
            with patch.object(comparison.chain_root, 'render_probe', return_value='frozen source'), \
                    patch.object(discovery.chain_root, 'parse_probe', side_effect=ValueError('incomplete native goal record')):
                reused = comparison.reuse_completed(job)
                self.assertTrue(reused['reused'])
                self.assertEqual(reused['outcomes'], ['capture-error'])
                self.assertTrue(reused['executed'])
                self.assertEqual(reused['captures'][0]['reused_capture_inputs'][str(p)],
                                 hashlib.sha256(p.read_bytes()).hexdigest())
                missing = (*job[:4], {**options, 'probe_targets': ['0x30']})
                self.assertIsNone(comparison.reuse_completed(missing))
                p.write_text('changed')
                with self.assertRaisesRegex(ValueError, 'source changed'):
                    comparison.reuse_completed(job)


if __name__ == '__main__':
    unittest.main()
