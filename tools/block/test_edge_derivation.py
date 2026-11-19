"""Edge proofs open the block history (and its nested groups); a successor fact the block cannot
prove from its own context is delivered by the edge or by a reveal instance, or reported."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import entry_hist
from render_edges import (Source, check_edge_sentences, edge_sentences, free_witnesses, stated_at_source,
                          visible_accounting)

T = 'bv 64'
PRE = {'parameters': [{'name': 'args', 'type': 'A'}], 'live': [{'name': 'k', 'type': T}],
       'hist_live': [{'name': 'k', 'type': T}],
       'ghost': [{'name': 'x', 'type': T}, {'name': 'y', 'type': T}],
       'visible': ['(zesu_named_eq k (g args))', '(∃ (v : bv 64), (Q v k))'],
       'hidden': ['zesu_named_eq x (f k)', 'P y', 'Q x y',
                  'zesu_join_history (∃ (c : bv 64) (d : bv 64), (R c) /\\ (S c d))',
                  '∃ (v : bv 64), (Q v k)']}
SUCC = {'live': [{'name': 'k', 'type': T}], 'ghost': [], 'visible': [], 'hidden': []}


class Derivation(unittest.TestCase):
    def test_a_group_of_source_history_facts_is_a_term_over_the_opened_history(self):
        source = Source(PRE)
        text = 'zesu_join_history (∃ (x : bv 64) (y : bv 64), (zesu_named_eq x (f k)) /\\ (Q x y))'
        self.assertEqual(source.derive(text), ('(ex_intro _ x (ex_intro _ y (conj HF0 HF2)))', set(), {'HF0', 'HF2'}))
        self.assertEqual(source.derive('∃ (y : bv 64), (P y)')[0], '(ex_intro _ y HF1)')

    def test_members_of_a_nested_source_group_are_taken_from_the_opened_group(self):
        source = Source(PRE)
        term, opened, used = source.derive('zesu_join_history (∃ (c : bv 64) (y : bv 64), (R c) /\\ (P y))')
        self.assertEqual(term, '(ex_intro _ c_HF3 (ex_intro _ y (conj HF3_0 HF1)))')
        self.assertEqual(opened, {'HF3'})
        self.assertEqual(source.open_sentence('HF3'), '  destruct HF3 as (c_HF3 & d_HF3 & HF3_0 & HF3_1).')
        self.assertEqual(source.hidden_names(), {'c', 'd', 'v'})

    def test_a_visible_source_fact_is_a_premise_and_never_a_reveal(self):
        self.assertEqual(Source(PRE).derive('∃ (z : bv 64), (zesu_named_eq k (g args)) /\\ (P z)'), None)
        self.assertEqual(Source(PRE).derive('(zesu_named_eq k (g args))')[0], 'HV0')
        self.assertIsNone(Source(PRE, visible=False).derive('(zesu_named_eq k (g args))'))

    def test_a_missing_member_or_a_split_group_binder_stays_underived(self):
        source = Source(PRE)
        self.assertIsNone(source.derive('zesu_join_history (∃ (x : bv 64), (R x))'))
        # d is bound by the group HF3, c by the same group: taking (S c d) from HF3 and c from elsewhere fails.
        self.assertIsNone(source.derive('∃ (c : bv 64) (d : bv 64), (zesu_named_eq c (f k)) /\\ (S c d)'))

    def test_a_flat_group_is_taken_from_a_group_nested_in_a_history_group(self):
        # The 0368 -> 026c shape: a later join bound the earlier record group as one member of its own
        # group, and the successor states the records as one flat group over a live block binder too.
        pre = {**PRE, 'hidden': ['∃ (a : bv 64), (∃ (b : bv 64), (R b) /\\ (S b a)) /\\ (Q a k) /\\ (P b)']}
        source = Source(pre, visible=False)
        term, opened, used = source.derive('∃ (a : bv 64) (b : bv 64), (R b) /\\ (S b a) /\\ (Q a k)')
        self.assertEqual(term, '(ex_intro _ a_HF0 (ex_intro _ b_HF0_0 (conj HF0_0_0 (conj HF0_0_1 HF0_1))))')
        self.assertEqual(opened, {'HF0', 'HF0_0'})
        self.assertEqual(source.open_sentence('HF0_0'), '  destruct HF0_0 as (b_HF0_0 & HF0_0_0 & HF0_0_1).')
        # (P b) names a b that neither a source group nor the block binds: no single witness for b.
        self.assertIsNone(source.derive('∃ (b : bv 64), (R b) /\\ (P b)'))
        # A member over a name its own group binds (k) does not state the block binder k.
        shadow = Source({**PRE, 'hidden': ['∃ (k : bv 64) (v : bv 64), (Q v k)']}, visible=False)
        self.assertIsNone(shadow.derive('∃ (v : bv 64), (Q v k)'))
        check_edge_sentences('Proof.\n  destruct HF0_0 as (b_HF0_0 & HF0_0_0 & HF0_0_1).\nQed.\n')

    def test_the_proof_sentences_are_in_the_edge_sentence_list(self):
        text = ('Proof.\n  destruct HF3 as (c_HF3 & d_HF3 & HF3_0 & HF3_1).\n'
                '  destruct HV1 as (v_HV1 & HV1_0).\n'
                '  split; [exact (ex_intro _ c_HF3 (ex_intro _ y (conj HF3_0 HF1)))|].\n'
                '  exact (ex_intro _ y HF1).\nQed.\n')
        check_edge_sentences(text)
        self.assertEqual(len(edge_sentences(text)), 6)


def edge(rows, unchanged=()):
    return {'binder_map': rows, 'unchanged': list(unchanged)}


class VisibleAccounting(unittest.TestCase):
    ROWS = [{'succ': 'k', 'role': 'live', 'identity': True, 'expression': 'k', 'type': T},
            {'succ': 'w', 'role': 'live', 'identity': False, 'expression': None, 'type': T}]

    def test_each_successor_visible_fact_is_visible_revealed_path_or_a_violation(self):
        succ = {'live': [{'name': 'k', 'type': T}, {'name': 'w', 'type': T}], 'ghost': [],
                'visible': ['(zesu_named_eq k (g args))',
                            '(∃ (c : bv 64), (R c))',
                            '((w < 4)%Z)',
                            '(∃ (v : bv 64) (z : bv 64), (Q v k) /\\ (T z))',
                            '(P x)'],
                'hidden': []}
        rows = visible_accounting(edge(self.ROWS, [{'succ': ['visible', 0], 'pre': ['visible', 0]}]), PRE, succ)
        self.assertEqual([row['status'] for row in rows], ['visible', 'reveal', 'path', 'violation', 'violation'])
        self.assertEqual(rows[1]['derivation'][0], '(ex_intro _ c_HF3 HF3_0)')
        self.assertEqual(rows[3]['reason'], 'regroups block-entry facts')
        self.assertEqual(rows[4]['reason'], 'names a hidden block binder')

    def test_a_successor_live_binder_without_a_term_is_the_blocks_own_value(self):
        succ = {'live': [{'name': 'w', 'type': T}], 'ghost': [{'name': 'u', 'type': T}]}
        self.assertEqual(stated_at_source('(w = k)', self.ROWS, succ), '(w_succ = k)')
        self.assertIsNone(stated_at_source('(u = k)', self.ROWS, succ))


class FreeMaskWitness(unittest.TestCase):
    MASK = '((bool_decide ((bv_and m (BV 64%N 131072%Z)) = (BV 64%N 0%Z))) = true)'
    GUARD = '((negb (bool_decide ((bv_extract 17%N 1%N m) = (BV 1%N 1%Z)))) = true)'

    def rows(self):
        return [{'succ': 'm', 'role': 'ghost', 'identity': True, 'expression': 'm', 'type': T,
                 'pre': {'name': 'm', 'role': 'ghost'}}]

    def test_a_held_mask_binder_with_a_new_guard_gets_the_witness_zero(self):
        pre = {'hidden': [self.MASK]}
        succ = {'live': [], 'ghost': [{'name': 'm', 'type': T}], 'visible': [], 'hidden': [self.MASK, self.GUARD]}
        rows = self.rows()
        free_witnesses(succ, rows, pre)
        self.assertEqual((rows[0]['expression'], rows[0]['identity'], rows[0].get('free')), ('(BV 64%N 0%Z)', False, True))

    def test_a_held_mask_binder_whose_facts_are_unchanged_keeps_its_value(self):
        pre = {'hidden': [self.MASK]}
        succ = {'live': [], 'ghost': [{'name': 'm', 'type': T}], 'visible': [], 'hidden': [self.MASK]}
        rows = self.rows()
        free_witnesses(succ, rows, pre)
        self.assertEqual((rows[0]['expression'], rows[0]['identity']), ('m', True))


if __name__ == '__main__':
    unittest.main()
