"""Reject unsound table promotion without running native proofs."""
from copy import deepcopy
from pathlib import Path
import sys
import json
import tempfile
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

    def test_pending_render_contains_no_proof_terms(self):
        report = promote_table.coverage(*self.fixture(), design_sha256='bound')
        source = promote_table.render_slots(report)
        self.assertNotIn('Definition decodeItemPromotedBody', source)
        self.assertNotIn('Admitted', source)

    def test_promoted_reference_has_the_exact_table_type(self):
        source = promote_table.render_slots(dict(proof_slots=[dict(
            pc='0x1000', status='proved', proof_lemma='Proofs.ExactBody')]))
        self.assertIn(promote_table.table_statement(0x1000), source)
        self.assertIn('  Proofs.ExactBody.', source)
        self.assertNotIn('Lemma', source)

    def evidence(self):
        proof = dict(compiled=True, verified=True, assumptions=[], inherited_debts=[],
                     goal_groups=dict(goals=[], stack=[], shelf=[], given_up=[]))
        native = dict(proof, entry_pc=0x1000, successors=[0x1008, 0x1004],
                      scope='native designed boundary', block_closed=True, design_sha256='bound')
        adapter = dict(proof, statement=promote_table.table_statement(0x1000), lemma='Proofs.ExactBody')
        return native, adapter

    def test_certificate_shape_accepts_all_edges(self):
        _, design, _ = self.fixture()
        native, adapter = self.evidence()
        self.assertEqual(promote_table.validate_promotion(design['blocks'][0], native,
            adapter, design_sha256='bound'), 'Proofs.ExactBody')

    def test_certificate_hash_mismatch_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            evidence = root / 'evidence.json'
            evidence.write_text('{}')
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps({'0x1000': {'native': {
                'path': 'evidence.json', 'sha256': 'stale'}}}))
            with self.assertRaisesRegex(ValueError, 'evidence hash'):
                promote_table.load_promotions(manifest)

    def test_missing_proof_source_binding_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            evidence = root / 'evidence.json'
            evidence.write_text('{}')
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps({'0x1000': {'native': {
                'path': 'evidence.json', 'sha256': promote_table.digest(evidence)}}}))
            with self.assertRaisesRegex(ValueError, 'proof-source binding'):
                promote_table.load_promotions(manifest)

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
