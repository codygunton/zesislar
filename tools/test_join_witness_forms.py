"""Preserve source-bound continuation lets without changing witness scope."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from witness_data import declared_witness_slots, has_witness_slots


class JoinWitnessFormTests(unittest.TestCase):
    source = '''Definition target (args : Z) : iProp Sigma :=
      let K : iProp Sigma := (∃ hidden : Z, ⌜hidden = args⌝)%I in
      ((∃ (word : bv 64%N),
        "x11" ↦ᵣ RVal_Bits word ∗
        ⌜(fun outcome : Z => outcome = args) (bv_unsigned word)⌝ ∗ K))%I.'''

    def test_outer_continuation_existential_is_not_a_witness_slot(self):
        before = self.source
        layout = declared_witness_slots(before, 'target')
        self.assertEqual([slot['name'] for slot in layout['declared']], ['word'])
        self.assertEqual(layout['register_slots'], {'word': 'x11'})
        self.assertEqual([item['name'] for item in layout['outer_lets']], ['K'])
        self.assertEqual(before, self.source)
        self.assertTrue(has_witness_slots(before, 'target'))

    def test_existential_only_in_outer_let_does_not_make_a_witness(self):
        self.assertFalse(has_witness_slots(
            'Definition target : iProp Sigma := let K : iProp Sigma := (∃ hidden : Z, True)%I in K.',
            'target'))

    def test_multiple_distinct_source_lets_preserve_the_actual_telescope(self):
        source = self.source.replace('((∃ (word',
            'let J : iProp Sigma := K in ((∃ (word')
        layout = declared_witness_slots(source, 'target')
        self.assertEqual([item['name'] for item in layout['outer_lets']], ['K', 'J'])
        self.assertEqual([slot['name'] for slot in layout['remaining']], ['word'])

    def test_parenthesized_typed_pure_lambda_is_allowed(self):
        layout = declared_witness_slots(self.source.replace('fun outcome : Z', 'fun (outcome : Z)'), 'target')
        self.assertEqual([slot['name'] for slot in layout['remaining']], ['word'])

    def test_outer_let_capture_and_unsupported_patterns_refuse(self):
        cases = [
            self.source.replace('let K :', 'let args :'),
            self.source.replace('let K :', 'let word :'),
            self.source.replace('hidden = args', 'hidden = word'),
            self.source.replace('(word : bv 64%N)', '(word : K)'),
            self.source.replace('((∃ (word', 'let K : iProp Sigma := True in ((∃ (word'),
            self.source.replace('let K :', "let '(K, J) :"),
            self.source.replace('let K : iProp Sigma :=', 'let K :='),
            self.source.replace('(∃ hidden : Z, ⌜hidden = args⌝)%I', '(let J := True in J)%I'),
        ]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(ValueError):
                declared_witness_slots(source, 'target')

    def test_lambda_capture_and_resource_binders_refuse(self):
        cases = [
            self.source.replace('fun outcome :', 'fun args :'),
            self.source.replace('fun outcome :', 'fun word :'),
            self.source.replace('fun outcome :', 'fun K :'),
            self.source.replace('fun outcome : Z', 'fun outcome'),
            self.source.replace('fun outcome : Z =>', 'fun outcome : Z => fun outcome : Z =>'),
            self.source.replace('fun outcome : Z', 'fun outcome : word'),
            self.source.replace('⌜(fun outcome : Z => outcome = args) (bv_unsigned word)⌝',
                                '(fun outcome : Z => True)'),
            self.source.replace('"x11" ↦ᵣ', '∃ (other : bv 64%N), "x11" ↦ᵣ'),
            self.source.replace('"x11" ↦ᵣ', '∀ (other : bv 64%N), "x11" ↦ᵣ'),
            self.source.replace('outcome = args', '(let other := args in outcome = other)'),
        ]
        for source in cases:
            with self.subTest(source=source), self.assertRaises(ValueError):
                declared_witness_slots(source, 'target')

    def test_pure_text_cannot_supply_a_register_owner(self):
        source = self.source.replace('"x11" ↦ᵣ RVal_Bits word ∗', '')
        source = source.replace('outcome = args', '"x11" ↦ᵣ RVal_Bits word')
        self.assertEqual(declared_witness_slots(source, 'target')['register_slots'], {})


if __name__ == '__main__':
    unittest.main()
