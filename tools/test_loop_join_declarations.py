"""Render source region classes without a fabricated return pullback."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from join_declarations import join_declarations


class LoopJoinDeclarationTests(unittest.TestCase):
    def fixture(self):
        alternatives, classes = [], []
        for index in range(4):
            state = {'registers': {'x11': {'source_class': index}}}
            components = [{'id': 'register', 'source': '"x11" ↦ᵣ RVal_Bits word'},
                          {'id': 'fact', 'source': '⌜classFact' + str(index) + ' word⌝'},
                          {'id': 'K', 'source': 'K'}]
            tree = {'kind': 'sep', 'left': {'kind': 'exists', 'binders': [{'name': 'word', 'type': 'bv 64'}],
                    'body': {'kind': 'sep_list', 'children': [{'kind': 'component', 'id': 'register'},
                                                            {'kind': 'component', 'id': 'fact'}]}},
                    'right': {'kind': 'component', 'id': 'K'}}
            alternatives.append({'source_index': index, 'state': deepcopy(state), 'predecessor_pc': None,
                'seed_pc': '0x100', 'resource_boundary': {'block_status': 'completed', 'tree': tree,
                'components': components}})
            classes.append({'source_index': index, 'seed': state, 'binders': [{'name': 'word', 'type': 'bv 64'}],
                'relations': [{'kind': 'cursor', 'checked': True}], 'folds': [],
                'edge_records': [{'backedge': index}], 'refusals': [{'kind': 'open_zero_return'}],
                'witness_plan': {'ordered_binders': ['word']},
                'body_results': {'path': 'bound-source-body', 'sha256': str(index) * 64}})
        return {'boundary': {'pc': '0x100', 'status': 'generated_loop_head', 'alternatives': alternatives},
                'loop_classes': classes, 'continuation': {'name': 'K', 'coq': 'continuation arg', 'terminal_id': 'K'}}

    def render(self, join):
        return join_declarations(join, entry_name='loopEntry', entry_module='Generated.LoopEntries',
            parameters=[{'name': 'arg', 'type': 'Z'}], imports=['ZesuSsz.Automation.All'])

    def test_four_source_classes_keep_their_records_and_one_outer_continuation(self):
        join = self.fixture();before = deepcopy(join)
        result = self.render(join)
        self.assertEqual(len(result['definitions']), 5)
        self.assertEqual([row['source_index'] for row in result['witness_plans']], [0, 1, 2, 3])
        self.assertEqual(result['loop_classes'], join['loop_classes'])
        self.assertEqual(result['entry'].count('let K :'), 1)
        self.assertEqual(result['definition'].count(' ∨ '), 3)
        self.assertIn(') ∗ K)%I.', result['definition'])
        self.assertNotIn('bool', result['entry'])
        self.assertNotIn('Proof.', result['entry'] + result['structural'])
        self.assertIn('loopEntryClass0_intro', result['structural'])
        self.assertIn('loopEntry_intro', result['structural'])
        self.assertEqual(result['entry'].count('#[global] Typeclasses Opaque '), 5)
        self.assertIn('\n  (let K : iProp Sigma := (continuation arg)%I in', result['structural'])
        self.assertIn(') ∗ K)%I) := @PreOrder_Reflexive', result['structural'])
        self.assertEqual(result['kernel_entailments'], 'OPEN')
        self.assertFalse(result['proof_established'])
        self.assertEqual(join, before)

    def test_incomplete_duplicate_or_mismatched_class_inputs_refuse(self):
        for defect in ['class', 'order', 'field', 'state', 'incoming', 'scope', 'continuation', 'ownership']:
            with self.subTest(defect=defect):
                join = self.fixture();first = join['boundary']['alternatives'][0]
                if defect == 'class':join['loop_classes'][1]['source_index'] = 0
                elif defect == 'order':join['loop_classes'].reverse()
                elif defect == 'field':del join['loop_classes'][0]['edge_records']
                elif defect == 'state':first['state'] = {}
                elif defect == 'incoming':first['predecessor_pc'] = '0x10'
                elif defect == 'scope':first['resource_boundary']['tree']['right'] = {'kind': 'component', 'id': 'other'}
                elif defect == 'continuation':first['resource_boundary']['components'][-1]['source'] = 'differentK'
                elif defect == 'ownership':first['resource_boundary']['block_status'] = 'stopped'
                with self.assertRaises(ValueError):self.render(join)

    def test_loop_exception_does_not_remove_the_return_pullback_requirement(self):
        join = self.fixture();join['boundary']['status'] = 'generated_join'
        with self.assertRaisesRegex(ValueError, 'exit pullback'):self.render(join)

    def test_fold_imports_remain_ordered_and_reach_both_declaration_modules(self):
        join = self.fixture()
        for row in join['loop_classes']:
            row['required_imports'] = ['Coq.ZArith.ZArith', 'ZesuSsz.Automation.ByteWindowFold']
        result = self.render(join)
        for text in [result['entry'], result['structural']]:
            self.assertEqual(text.count('Require Import ZesuSsz.Automation.ByteWindowFold.'), 1)
            self.assertLess(text.index('Require Import Coq.ZArith.ZArith.'),
                            text.index('Require Import ZesuSsz.Automation.ByteWindowFold.'))


if __name__ == '__main__':unittest.main()
