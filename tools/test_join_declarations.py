"""Join renderers emit declarations and preserve the exact introduction body."""
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from join_declarations import join_declarations


class JoinDeclarationTests(unittest.TestCase):
    def fixture(self):
        return {'pullback': {'status': 'generated'}, 'boundary': {'alternatives': [
            {'predecessor_pc': None, 'resource_boundary': {'block_status': 'completed',
                'body': '(∃ (word : bv 64), "x11" ↦ᵣ RVal_Bits word ∗ K)'}}]},
            'continuation': {'name': 'K', 'coq': 'True'},
            'seed': SimpleNamespace(join_witness_plan={'ordered_binders': ['word']})}

    def render(self, join):
        return join_declarations(join, entry_name='machineJoin',
            entry_module='ZesuSsz.Generated.Example.JoinEntries', parameters=[{'name': 'arg', 'type': 'Z'}],
            imports=['ZesuSsz.Automation.All'])

    def test_entry_and_structural_use_the_exact_same_body(self):
        result = self.render(self.fixture())
        for kind in ['entry', 'structural']:
            self.assertTrue(result[kind].startswith(
                'Require Import ZesuSsz.Automation.All.\n'
                'Require Import isla.riscv64.riscv64.\n'))
        self.assertIn('let K : iProp Sigma := (True)%I in', result['entry'])
        self.assertIn('#[global] Typeclasses Opaque machineJoin.', result['entry'])
        self.assertIn('\n  (let K : iProp Sigma := (True)%I in', result['structural'])
        self.assertIn('Instance machineJoin_intro', result['structural'])
        self.assertIn('@PreOrder_Reflexive', result['structural'])
        self.assertIn('(∃ (word : bv 64), "x11" ↦ᵣ RVal_Bits word ∗ K)', result['structural'])
        self.assertNotIn('Proof.', result['entry'] + result['structural'])
        self.assertFalse(result['proof_established'])

    def test_direct_owner_imports_keep_order_and_standard_imports_do_not_repeat(self):
        result = join_declarations(self.fixture(), entry_name='machineJoin',
            entry_module='ZesuSsz.Generated.Example.JoinEntries', parameters=[],
            imports=['ZesuSsz.Automation.All', 'Coq.Lists.List',
                'isla.riscv64.riscv64', 'ZesuSsz.Contracts.ExampleArgs',
                'ZesuSsz.Contracts.ExampleMeaning'])
        for kind in ['entry', 'structural']:
            source = result[kind]
            self.assertEqual(source.count('Require Import isla.riscv64.riscv64.'), 1)
            self.assertEqual(source.count('Require Import Coq.Lists.List.'), 1)
            self.assertIn('Import ListNotations.\n', source)
            self.assertLess(source.index('ExampleArgs.'), source.index('ExampleMeaning.'))

    def test_missing_pullback_refuses(self):
        join = self.fixture()
        join['pullback']['status'] = 'refused'
        with self.assertRaisesRegex(ValueError, 'exit pullback'):
            self.render(join)

    def test_multiple_seeds_refuse(self):
        join = self.fixture()
        join['boundary']['alternatives'] *= 2
        with self.assertRaisesRegex(ValueError, 'one generated seed'):
            self.render(join)

    def test_source_objects_remain_unchanged(self):
        join = self.fixture()
        before = deepcopy(join['boundary'])
        result = self.render(join)
        result['witness_plan']['ordered_binders'].append('extra')
        self.assertEqual(join['seed'].join_witness_plan['ordered_binders'], ['word'])
        self.assertEqual(join['boundary'], before)


if __name__ == '__main__':
    unittest.main()
