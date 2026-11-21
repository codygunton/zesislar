"""Join-design obligations (profile `join_designs` rows with `obligation`): a join states the row's fact
in its history; an edge whose block history does not hold it proves it by the registered lemma of a
data-only declaration (`EdgeObligations.v`); an edge whose block history holds it passes it on. Named
call arguments (a word the code passes on unchanged) stay visible at call and return sites."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import entry_hist
from render_edges import check_edge_sentences, edge_proof_problems, own_guards, rocq_edge

T = 'bv 64'
ROW = {'coq': 'cand args = err', 'history': True, 'obligation': 'CandidateError', 'lemma_module': 'M.Lemmas'}
PROFILE = {'join_designs': {'+0x20': [ROW, 'plain args']}}
FACT = 'zesu_join_history (cand args = err)'
PRE = {'hist': 'fp_machineAt0010_ForwardA0N0_Hist', 'entry': 'fp_machineAt0010_ForwardA0N0',
       'parameters': [{'name': 'args', 'type': 'A'}], 'live': [{'name': 'k', 'type': T}, {'name': 'm', 'type': T}],
       'hist_live': [{'name': 'k', 'type': T}], 'ghost': [{'name': 'x', 'type': T}],
       'visible': ['(zesu_named_eq k (g args))'], 'hidden': ['P x k']}
SUCC = {'hist': 'fp_machineAt0020_ForwardA0N0_Hist', 'entry': 'fp_machineAt0020_ForwardA0N0',
        'parameters': [{'name': 'args', 'type': 'A'}], 'live': [], 'ghost': [], 'visible': [], 'hidden': [FACT]}


def join_edge():
    return {'binder_map': [], 'unchanged': [], 'closed': [], 'kind': 'join', 'pre_entry': PRE['entry'],
            'succ_entry': SUCC['entry'],
            'new': [{'succ': ['hidden', 0], 'text': FACT, 'binders': [], 'support': []}]}


class DesignRows(unittest.TestCase):
    def test_a_history_row_is_stated_under_the_join_history_marker(self):
        self.assertEqual(entry_hist.design_fact_text(ROW), FACT)
        self.assertEqual(entry_hist.design_fact_text('plain args'), 'plain args')
        self.assertEqual(entry_hist.design_fact_text({'coq': 'q'}), 'q')
        self.assertEqual(entry_hist.design_obligations(PROFILE), {entry_hist.normal(FACT): ROW})
        self.assertEqual(entry_hist.design_obligations({}), {})

    def test_a_history_row_is_hidden_and_an_obligation_needs_a_lemma_module(self):
        _, _, visible, hidden = entry_hist.classify([], [], [FACT, 'cand args = err'])
        self.assertEqual((visible, hidden), (['cand args = err'], [FACT]))
        with self.assertRaises(ValueError):
            entry_hist.design_obligations({'join_designs': {'+0x20': [{**ROW, 'lemma_module': ''}]}})


class Obligations(unittest.TestCase):
    def test_an_edge_into_the_join_applies_the_registered_lemma_of_its_declaration(self):
        # A row without `premises` takes the edge's own guards only, no block-entry fact.
        declarations = []
        obligation = {'rows': entry_hist.design_obligations(PROFILE), 'declarations': declarations,
                      'guards': ['(negb (bool_decide (m = BV 64 0))) = true'], 'name': 'fp_edge0010_0020'}
        text = rocq_edge(join_edge(), PRE, SUCC, 3, obligation)
        self.assertIn('pose proof Hh as HS.', text)
        self.assertIn('(⌜(negb (bool_decide (m = BV 64 0))) = true⌝ ∗ True)%I', text)
        self.assertIn('iDestruct "HN" as "(%HG0 & _)".', text)
        self.assertIn('  exact (fp_edge0010_0020_CandidateError_holds args k m HS HG0).', text)
        check_edge_sentences(text)
        self.assertEqual([row['name'] for row in declarations], ['fp_edge0010_0020_CandidateError'])
        self.assertEqual(declarations[0]['module'], 'M.Lemmas')
        self.assertEqual(declarations[0]['text'],
                         'Definition fp_edge0010_0020_CandidateError : Prop :=\n'
                         '  forall (args : A) (k : bv 64) (m : bv 64),\n'
                         '  (fp_machineAt0010_ForwardA0N0_Hist (args) (k)) ->\n'
                         '  ((negb (bool_decide (m = BV 64 0))) = true) ->\n'
                         '  cand args = err.\n')

    def test_the_declaration_has_exactly_the_declared_premise_classes(self):
        visible = ['(zesu_named_eq k (g args))', '(D args)', '((List.length k = 3)%nat)',
                   '(call2_after <> (0%Z))', '(decodeItemCallMeaning (h call2_after))', '(E k m)']
        pre = {**PRE, 'visible': visible, 'live': PRE['live'] + [{'name': 'call2_after', 'type': T}]}
        guard = '(negb (bool_decide (m = BV 64 0))) = true'
        cases = [(['named_eq'], [0], False), (['domain', 'length'], [1, 2], False),
                 (['newest_call_record', 'guard'], [4], True), (['newest_call_guard'], [3], False),
                 (['guard'], [], True)]
        for classes, positions, guarded in cases:
            declarations = []
            profile = {'join_designs': {'+0x20': [{**ROW, 'premises': classes}]}}
            obligation = {'rows': entry_hist.design_obligations(profile), 'declarations': declarations,
                          'guards': [guard], 'name': 'fp_edge0010_0020'}
            text = rocq_edge(join_edge(), pre, SUCC, 3, obligation)
            premises = [line[3:-4] for line in declarations[0]['text'].splitlines()[3:-1]]
            self.assertEqual(premises, [visible[p] for p in positions] + ([guard] if guarded else []), classes)
            hypotheses = ['HV' + str(p) for p in positions] + (['HG0'] if guarded else [])
            self.assertIn('_holds ' + ' '.join(b for b in ['args', 'k', 'm', 'call2_after'] if b in {'args', 'k'}
                                               or any(entry_hist.mentions(b, f) for f in premises))
                          + ' HS ' + ' '.join(hypotheses) + ')', text)
            check_edge_sentences(text)

    def test_premise_classes_are_checked_and_rows_are_read_per_join(self):
        with self.assertRaises(ValueError):
            entry_hist.design_obligations({'join_designs': {'+0x20': [{**ROW, 'premises': ['everything']}]}})
        profile = {'join_designs': {'+0x20': [ROW], '+0x30': [{**ROW, 'coq': 'other'}]}}
        self.assertEqual(list(entry_hist.design_obligations(profile, ['+0x30']).values()),
                         [{**ROW, 'coq': 'other'}])

    def test_an_edge_whose_block_history_holds_the_fact_passes_it_on(self):
        declarations = []
        pre = {**PRE, 'hidden': ['P x k', FACT]}
        obligation = {'rows': entry_hist.design_obligations(PROFILE), 'declarations': declarations,
                      'guards': [], 'name': 'fp_edge0010_0020'}
        text = rocq_edge(join_edge(), pre, SUCC, 3, obligation)
        self.assertEqual(declarations, [])
        self.assertNotIn('HS', text)
        self.assertIn('  exact HF1.', text)

    def test_a_fact_on_a_binder_the_edge_sets_is_proved_under_its_equation(self):
        # A second row of the join states a fact on its live binder `t`, which the edge sets to `w m`:
        # its declaration takes `t` and `t = w m` (the block proves the equation); the binder-free row
        # keeps its statement.
        tag = {**ROW, 'coq': 'bv_unsigned t = 3', 'obligation': 'ErrorTag'}
        profile = {'join_designs': {'+0x20': [ROW, tag]}}
        succ = {**SUCC, 'live': [{'name': 't', 'type': T}],
                'hidden': [FACT, 'zesu_join_history (bv_unsigned t = 3)']}
        edge = join_edge()
        edge['binder_map'] = [{'succ': 't', 'type': T, 'role': 'live', 'pre': None, 'identity': False,
                               'expression': '(w m)'}]
        edge['new'].append({'succ': ['hidden', 1], 'text': 'zesu_join_history (bv_unsigned t = 3)',
                            'binders': [], 'support': []})
        declarations = []
        obligation = {'rows': entry_hist.design_obligations(profile), 'declarations': declarations,
                      'guards': [], 'name': 'fp_edge0010_0020'}
        text = rocq_edge(edge, PRE, succ, 3, obligation)
        check_edge_sentences(text)
        self.assertIn('(⌜t = (w m)⌝ ∗ True)%I', text)
        self.assertIn('iDestruct "HN" as "(%HE0 & _)".', text)
        self.assertIn('exact (fp_edge0010_0020_ErrorTag_holds args k m t HS HE0)', text)
        self.assertIn('exact (fp_edge0010_0020_CandidateError_holds args k HS)', text)
        texts = {row['name']: row['text'] for row in declarations}
        self.assertEqual(texts['fp_edge0010_0020_ErrorTag'],
                         'Definition fp_edge0010_0020_ErrorTag : Prop :=\n'
                         '  forall (args : A) (k : bv 64) (m : bv 64) (t : bv 64),\n'
                         '  (fp_machineAt0010_ForwardA0N0_Hist (args) (k)) ->\n'
                         '  (t = (w m)) ->\n'
                         '  bv_unsigned t = 3.\n')
        self.assertNotIn('(t = (w m))', texts['fp_edge0010_0020_CandidateError'])
        edge['binder_map'][0]['expression'] = None
        with self.assertRaises(ValueError):
            rocq_edge(edge, PRE, succ, 3, {**obligation, 'declarations': []})

    def test_the_history_copy_is_the_only_new_sentence_form(self):
        self.assertEqual(edge_proof_problems('Proof.\n  pose proof Hh as HS.\nQed.\n'), [])
        self.assertTrue(edge_proof_problems('Proof.\n  pose proof Hh as HX.\nQed.\n'))

    def test_an_obligation_argument_may_be_a_record_field_and_a_refused_sentence_fails_fast(self):
        field = 'Proof.\n  split; [exact (f_holds args (Z_to_bv 64 (nextRestPointer (r))) HS HV0)|].\nQed.\n'
        self.assertEqual(edge_proof_problems(field), [])
        self.assertTrue(edge_proof_problems('Proof.\n  exact (f (x + 1)).\nQed.\n'))
        # 2026-11-21: the earlier `(?:NAME|[ ()])+` backtracked exponentially on such a sentence.
        slow = 'Proof.\n  exact (' + ' '.join(['abcdefghij'] * 60) + ' 64%N).\nQed.\n'
        self.assertTrue(edge_proof_problems(slow))


def path(predecessor, seed, conditions):
    return {'predecessor_pc': predecessor, 'seed_pc': seed,
            'resource_boundary': {'path_conditions': conditions, 'owned_read_renderings': []}}


def condition(name):
    return {'op': 'input', 'width': None, 'value': name}


class OwnGuards(unittest.TestCase):
    FORWARD = {'boundaries': [
        {'pc': '0x20', 'alternatives': [path('0x10', '0x8', [condition('a'), condition('b')])]},
        {'pc': '0x30', 'alternatives': [path('0x10', '0x8', [condition('a'), condition('c')]),
                                        path('0x18', '0x8', [condition('d')])]}]}

    def test_the_guards_are_the_conditions_after_the_prefix_the_blocks_paths_share(self):
        self.assertEqual(own_guards(self.FORWARD, '0x10', '0x20'), ['b = true'])
        self.assertEqual(own_guards(self.FORWARD, '0x10', '0x30'), ['c = true'])
        self.assertEqual(own_guards(self.FORWARD, '0x18', '0x30'), [])


class NamedArguments(unittest.TestCase):
    def test_a_named_call_argument_is_visible_at_the_call_and_return_sites(self):
        calls = {'0x40': {'call_site_pc': '0x3c', 'return_site_pc': '0x40', 'named_registers': {},
                          'named_arguments': {'call2_arg_word_1_0': 'call_word_1_0'}}}
        binders = [{'name': 'call_word_1_0', 'type': T}, {'name': 'call2_arg_word_1_0', 'type': T}]
        patterns = entry_hist.call_visible_patterns('0x40', calls, [0x30, 0x40, 0x50], binders)
        fact = 'zesu_named_eq call2_arg_word_1_0 call_word_1_0'
        self.assertTrue(any(__import__('re').search(pattern, fact) for pattern in patterns))


if __name__ == '__main__':
    unittest.main()
