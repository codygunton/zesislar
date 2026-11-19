"""A successor history group of source history facts is proved inside the edge, not left as a premise."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from render_edges import check_edge_sentences, derived_term, edge_sentences

T = 'bv 64'
PRE = {'parameters': [{'name': 'args', 'type': 'A'}], 'live': [{'name': 'k', 'type': T}],
       'hist_live': [{'name': 'k', 'type': T}],
       'ghost': [{'name': 'x', 'type': T}, {'name': 'y', 'type': T}],
       'hidden': ['zesu_named_eq x (f k)', 'P y', 'Q x y']}
SUCC = {'live': [{'name': 'k', 'type': T}], 'ghost': []}


class DerivedGroup(unittest.TestCase):
    def test_a_join_history_of_source_facts_is_a_term_over_the_source_hypotheses(self):
        text = 'zesu_join_history (∃ (x : bv 64) (y : bv 64), (zesu_named_eq x (f k)) /\\ (Q x y))'
        self.assertEqual(derived_term(text, PRE, SUCC, {'k'}), '(ex_intro _ x (ex_intro _ y (conj HF0 HF2)))')
        self.assertEqual(derived_term('∃ (y : bv 64), (P y)', PRE, SUCC, {'k'}), '(ex_intro _ y HF1)')

    def test_a_fact_the_source_history_lacks_or_a_renamed_binder_stays_a_premise(self):
        self.assertIsNone(derived_term('zesu_join_history (∃ (x : bv 64), (R x))', PRE, SUCC, {'k'}))
        self.assertIsNone(derived_term('zesu_join_history (∃ (z : bv 64), (P z))', PRE, SUCC, {'k'}))
        self.assertIsNone(derived_term('zesu_join_history (∃ (x : bv 64), (zesu_named_eq x (f k)))', PRE, SUCC, set()))

    def test_the_proof_sentence_is_in_the_edge_sentence_list(self):
        text = ('Proof.\n  split; [exact (ex_intro _ x (ex_intro _ y (conj HF0 HF2)))|].\n'
                '  exact (ex_intro _ y HF1).\nQed.\n')
        check_edge_sentences(text)
        self.assertEqual(len(edge_sentences(text)), 4)


if __name__ == '__main__':
    unittest.main()
