"""Return-fact obligations (profile `calls[].return_facts` rows with `obligation`): the return site
states the row's fact (in its history when `history`); the call block's edge into the return site
proves it by the registered lemma of a data-only declaration, as an edge into a join proves a join
design. A plain return fact keeps its text."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import entry_hist
from render_edges import check_edge_sentences, edge_obligation_rows, rocq_edge

T = 'bv 64'
ROW = {'kind': 'meaning', 'coq': 'walk args 1 k', 'history': True, 'obligation': 'Walk',
       'lemma_module': 'M.Walk', 'premises': ['named_eq']}
FACT = 'zesu_join_history (walk args 1 k)'


class Profile(dict):
    def pc(self, key):
        return hex(int(key.lstrip('+'), 16) + 0x1000)


PROFILE = Profile(calls=[
    {'call_site_pc': '0x101c', 'return_site_pc': '0x1020', 'return_facts': [ROW, {'kind': 'meaning', 'coq': 'q k'}]},
    {'call_site_pc': '0x103c', 'return_site_pc': None, 'return_facts': [{**ROW, 'coq': 'tail'}]}],
    join_designs={'+0x30': [{**ROW, 'obligation': 'CandidateError', 'coq': 'err'}]})
PRE = {'hist': 'fp_machineAt0010_ForwardA0N0_Hist', 'entry': 'fp_machineAt0010_ForwardA0N0',
       'parameters': [{'name': 'args', 'type': 'A'}], 'live': [{'name': 'k', 'type': T}],
       'hist_live': [{'name': 'k', 'type': T}], 'ghost': [], 'visible': ['(zesu_named_eq k (g args))', 'r k'],
       'hidden': ['walk args 0 k']}
SUCC = {'hist': 'fp_machineAt0020_ForwardA0N0_Hist', 'entry': 'fp_machineAt0020_ForwardA0N0',
        'parameters': [{'name': 'args', 'type': 'A'}], 'live': [{'name': 'k', 'type': T}],
        'ghost': [], 'visible': [], 'hidden': [FACT]}


def call_edge():
    return {'binder_map': [{'succ': 'k', 'role': 'live', 'identity': True, 'expression': 'k', 'pre': 'k'}],
            'unchanged': [], 'closed': [], 'kind': 'call_return', 'pre_entry': PRE['entry'],
            'succ_entry': SUCC['entry'], 'new': [{'succ': ['hidden', 0], 'text': FACT, 'binders': [], 'support': []}]}


class ReturnRows(unittest.TestCase):
    def test_rows_are_read_per_return_site_and_by_edge_kind(self):
        self.assertEqual(entry_hist.return_obligations(PROFILE, ['0x1020']), {entry_hist.normal(FACT): ROW})
        self.assertEqual(len(entry_hist.return_obligations(PROFILE)), 2)
        self.assertEqual(edge_obligation_rows(PROFILE, 'call_return', '0x1020'), {entry_hist.normal(FACT): ROW})
        self.assertEqual(edge_obligation_rows(PROFILE, 'forward', '0x1020'), {})
        self.assertEqual(list(edge_obligation_rows(PROFILE, 'join', '0x1030')), ['zesu_join_history (err)'])
        self.assertEqual(edge_obligation_rows(PROFILE, 'call_return', '0x1030'), {})
        with self.assertRaises(ValueError):
            entry_hist.return_obligations(Profile(calls=[{'return_site_pc': '0x1020',
                                                         'return_facts': [{**ROW, 'premises': ['all']}]}]))

    def test_a_plain_return_fact_keeps_its_text(self):
        self.assertEqual(entry_hist.design_fact_text({'kind': 'meaning', 'coq': 'q k'}), 'q k')
        self.assertEqual(entry_hist.design_fact_text(ROW), FACT)

    def test_the_call_blocks_edge_proves_the_fact_by_its_declaration(self):
        declarations = []
        obligation = {'rows': edge_obligation_rows(PROFILE, 'call_return', '0x1020'),
                      'declarations': declarations, 'guards': [], 'name': 'fp_edge0010_0020'}
        text = rocq_edge(call_edge(), PRE, SUCC, 4, obligation)
        check_edge_sentences(text)
        self.assertIn('pose proof Hh as HS.', text)
        self.assertIn('  exact (fp_edge0010_0020_Walk_holds args k HS HV0).', text)
        self.assertEqual([(row['name'], row['module']) for row in declarations], [('fp_edge0010_0020_Walk', 'M.Walk')])
        self.assertEqual(declarations[0]['text'],
                         'Definition fp_edge0010_0020_Walk : Prop :=\n  forall (args : A) (k : bv 64),\n'
                         '  (fp_machineAt0010_ForwardA0N0_Hist (args) (k)) ->\n'
                         '  ((zesu_named_eq k (g args))) ->\n'
                         '  walk args 1 k.\n')

    def test_newest_call_named_eq_takes_only_the_newest_layers_names(self):
        binders = [{'name': name, 'type': T} for name in ('call_after', 'call2_kept_x18', 'call3_kept_x18', 'call3_after')]
        facts = ['(zesu_named_eq call2_kept_x18 (f call_after))', '(zesu_named_eq call3_kept_x18 (f call2_after))',
                 'zesu_named_eq (call3_kept_x19) (g call2_after)', 'r call3_kept_x18']
        self.assertEqual(entry_hist.obligation_premise_positions(binders, facts, ['newest_call_named_eq']), [1, 2])
        self.assertEqual(entry_hist.obligation_premise_positions(binders, facts, ['named_eq']), [0, 1, 2])
        self.assertEqual(entry_hist.obligation_premise_positions(binders[:1], facts, ['newest_call_named_eq']), [])

    def test_newest_call_outcome_takes_every_fact_on_the_newest_outcome(self):
        binders = [{'name': name, 'type': T} for name in ('call2_after', 'call3_after', 'machine_x21_1')]
        facts = ['bv_unsigned machine_x21_1 = fold (w0 call3_after)', 'r call2_after', 'q call3_after_x',
                 '(negb (bool_decide (8 < w8 call3_after))) = true']
        self.assertEqual(entry_hist.obligation_premise_positions(binders, facts, ['newest_call_outcome']), [0, 3])


if __name__ == '__main__':
    unittest.main()
