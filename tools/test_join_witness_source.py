"""Keep witness provenance separate from the target and every pure conclusion."""
from copy import deepcopy
import hashlib
from pathlib import Path
from types import SimpleNamespace
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from join_witness_source import ownership_source


class JoinWitnessSourceTests(unittest.TestCase):
    def fixture(self, root):
        path = root / 'edges.json';path.write_text('source edges')
        evidence = [{'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}]
        parts = [('reg', 'register', '"x11" ↦ᵣ RVal_Bits word'),
                 ('array', 'byte_array', '(0) ↦ₘ∗ bytes'),
                 ('fact', 'opaque', '⌜meaning word⌝'), ('K', 'opaque', 'K')]
        binder = {'name': 'word', 'type': 'bv 64', 'value_key': 'x11',
                  'expression': {'op': 'input', 'width': 64, 'value': 'word'}}
        edge = {'index': 0, 'predecessor_pc': '0x10', 'path': [0],
                'ordered_witnesses': [{'binder': 'word', 'expression': {'op': 'bits', 'width': 64, 'value': 2}}],
                'original_values': {'x11': 2}, 'original_conditions': [], 'certificate': {'source': 'trace'}}
        seed = SimpleNamespace(ownership={'components': [{'id': key, 'kind': kind} for key, kind, _ in parts],
                                         'binders': [binder]}, join_edges=[edge],
                               join_witness_plan={'ordered_binders': ['word']})
        join = {'seed': seed, 'boundary': {'alternatives': [{'predecessor_pc': None,
                'resource_boundary': {'block_status': 'completed', 'components':
                    [{'id': key, 'source': text} for key, _, text in parts]}}]},
                'continuation': {'terminal_id': 'K'}}
        return join, evidence

    def render(self, join, evidence):
        return ownership_source(join, source_name='observedOwner', target_name='target',
            parameters=[{'name': 'bytes', 'type': 'list (bv 8)'}],
            imports=['ZesuSsz.Automation.All'], source_evidence=evidence)

    def test_retains_all_ownership_and_complete_edges_without_meaning(self):
        with tempfile.TemporaryDirectory() as directory:
            join, evidence = self.fixture(Path(directory));before = deepcopy(join['seed'].join_edges)
            result = self.render(join, evidence)
            self.assertIn('(word : bv 64)', result['source'])
            self.assertIn('"x11" ↦ᵣ RVal_Bits word', result['source'])
            self.assertIn('(0) ↦ₘ∗ bytes', result['source'])
            self.assertNotIn('meaning', result['source'])
            self.assertNotIn('∃', result['source'])
            self.assertNotIn('target', result['source'])
            self.assertNotIn('Proof.', result['source'])
            self.assertEqual(result['edges'], before)
            self.assertEqual(result['retained_components'], ['reg', 'array'])
            self.assertFalse(result['proof_established'])
            result['edges'][0]['path'].append(4)
            self.assertEqual(join['seed'].join_edges, before)

    def test_missing_changed_or_incomplete_evidence_refuses(self):
        for defect in ['hash', 'missing', 'edge', 'duplicate', 'component', 'parameter', 'binder', 'order']:
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                join, evidence = self.fixture(Path(directory))
                if defect == 'hash':evidence[0]['sha256'] = '0' * 64
                elif defect == 'missing':evidence = []
                elif defect == 'edge':del join['seed'].join_edges[0]['certificate']
                elif defect == 'duplicate':join['seed'].join_edges *= 2
                elif defect == 'component':join['boundary']['alternatives'][0]['resource_boundary']['components'].pop()
                elif defect == 'parameter':join['seed'].ownership['binders'][0]['name'] = 'bytes'
                elif defect == 'binder':join['seed'].ownership['binders'][0]['type'] = 'list byte'
                elif defect == 'order':join['seed'].join_witness_plan['ordered_binders'] = []
                with self.assertRaises(ValueError):self.render(join, evidence)

    def test_target_cannot_be_its_own_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            join, evidence = self.fixture(Path(directory))
            with self.assertRaisesRegex(ValueError, 'own witness provenance'):
                ownership_source(join, source_name='target', target_name='target', parameters=[],
                                 imports=['ZesuSsz.Automation.All'], source_evidence=evidence)

    def test_new_array_address_grouping_keeps_fraction_and_payload_exact(self):
        with tempfile.TemporaryDirectory() as directory:
            join, evidence = self.fixture(Path(directory))
            array = join['boundary']['alternatives'][0]['resource_boundary']['components'][1]
            array['source'] = 'pointer bytes ↦ₘ{DfracOwn 1}∗ (take 8 bytes ++ drop 8 bytes)'
            before = array['source']
            result = self.render(join, evidence)
            self.assertIn('(pointer bytes) ↦ₘ{DfracOwn 1}∗ (take 8 bytes ++ drop 8 bytes)', result['source'])
            self.assertEqual(result['source_fragments'][1]['original'], before)
            self.assertEqual(array['source'], before)


if __name__ == '__main__':unittest.main()
