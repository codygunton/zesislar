"""Reject unsound table promotion without running native proofs."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).parent / 'block'))
import promote_table
from tools.test_block_table import BlockTableTests


class PromotionTests(unittest.TestCase):
    def fixture(self):
        cfg, design = BlockTableTests().fixture()
        native = dict(blocks=[dict(entry=b['entry_pc'], block_closed=False,
            outcomes=['native-residual'], entry_provenance={'design_sha256': 'bound'})
            for b in design['blocks']])
        return cfg, design, native

    def test_pending_coverage_is_exact(self):
        args = self.fixture()
        report = promote_table.coverage(*args, design_sha256='bound')
        self.assertEqual(report['pending_instructions'], 3)
        self.assertEqual(report['proved_instructions'], 0)
        self.assertEqual(len({r['pc'] for r in report['instructions']}), 3)
        self.assertTrue(all(r['proof_lemma'] is None for r in report['proof_slots']))

    def test_capture_closure_cannot_promote(self):
        cfg, design, native = self.fixture()
        native['blocks'][0]['block_closed'] = True
        report = promote_table.coverage(cfg, design, native, design_sha256='bound')
        self.assertEqual(report['proved_instructions'], 0)

    def test_missing_block_and_stale_design_are_rejected(self):
        cfg, design, native = self.fixture()
        with self.assertRaisesRegex(ValueError, 'different design'):
            promote_table.coverage(cfg, design, native, design_sha256='new')
        native['blocks'].pop()
        with self.assertRaisesRegex(ValueError, 'omits or repeats'):
            promote_table.coverage(cfg, design, native, design_sha256='bound')

    def evidence(self):
        proof = dict(compiled=True, verified=True, assumptions=[], inherited_debts=[],
                     goal_groups=dict(goals=[], stack=[], shelf=[], given_up=[]))
        native = dict(proof, entry_pc=0x1000, successors=[0x1008, 0x1004],
                      scope='native designed boundary', block_closed=True, design_sha256='bound')
        adapter = dict(proof, statement=promote_table.table_statement(0x1000), lemma='ExactBody')
        return native, adapter

    def test_partial_join_edge_is_rejected(self):
        _, design, _ = self.fixture()
        native, adapter = self.evidence()
        native['successors'].pop()
        with self.assertRaisesRegex(ValueError, 'successor edges'):
            promote_table.validate_promotion(design['blocks'][0], native, adapter, design_sha256='bound')

    def test_signature_and_all_debt_groups_are_required(self):
        _, design, _ = self.fixture()
        native, adapter = self.evidence()
        adapter['statement'] = '⊢ True'
        with self.assertRaisesRegex(ValueError, 'signature'):
            promote_table.validate_promotion(design['blocks'][0], native, adapter, design_sha256='bound')
        for key in ('goals', 'stack', 'shelf', 'given_up'):
            native, adapter = self.evidence()
            adapter['goal_groups'][key] = ['debt']
            with self.assertRaisesRegex(ValueError, 'goal groups'):
                promote_table.validate_promotion(design['blocks'][0], native, adapter, design_sha256='bound')


if __name__ == '__main__':
    unittest.main()
