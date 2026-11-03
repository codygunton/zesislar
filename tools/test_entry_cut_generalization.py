"""Check every-cut formatting against actual source-owned alternatives."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from entry_formatter import SourceComponents, SymbolicConditions, format_owned_entry_boundary
from forward_resources import ownership_from_assertion_tree, render_resource_boundary, apply_owned_writes
from resource_seed import OwnedSeed
from symbolic_state import SymbolicState, bits, input_expr, operation


class EntryCutTests(unittest.TestCase):
    def fixture(self, values=(1, 2), conditions=()):
        tree = {'kind': 'exists', 'binders': [{'name': 'old', 'type': 'bv 64',
                                              'expression': input_expr('old').to_dict()}],
                'components': [{'kind': 'register', 'id': 'r', 'register': 'x13', 'value_coq': 'old'},
                               {'kind': 'opaque', 'id': 'terminal', 'coq': 'True'}]}
        ownership = ownership_from_assertion_tree(tree, provenance={'source': 'fixture'})
        seed = OwnedSeed(SymbolicState(registers={'PC': bits(32, 64), 'x13': input_expr('old')}),
                         ownership, [], [], [])
        vocabulary = {'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        alternatives = []
        for value in values:
            state = seed.state.copy()
            state.registers['x13'] = bits(value, 64)
            state.conditions = list(conditions)
            resource = render_resource_boundary(ownership, apply_owned_writes([], []), state,
                                                vocabulary=vocabulary)
            alternatives.append({'predecessor_pc': '0x10', 'seed_pc': '0x10', 'path': [],
                                 'state': state.to_dict(), 'resource_boundary': deepcopy(resource)})
        return seed, {'pc': '0x20', 'status': 'generated', 'alternatives': alternatives}, vocabulary

    def render(self, seed, boundary, vocabulary):
        def provenance(*args):
            return {'source': 'fixture'}
        return format_owned_entry_boundary(boundary, original_seed=seed, vocabulary=vocabulary,
            continuation={'name': 'K', 'coq': 'instr_pre exit_pc exit_resources',
                          'source_binding': {'source': 'Level1'}, 'terminal_id': 'terminal'},
            continuation_id='level1_K', case_id='cut', source_policy='source-only',
            handwritten_owner='Level1', guard_scope=(0,),
            component_adapter=SourceComponents({'K': {'owner': 'parameter', 'name': 'K'}},
                                              continuation_id='level1_K', provenance=provenance),
            condition_adapter=SymbolicConditions(provenance),
            helper_arguments=lambda body, context: [])

    def test_ordinary_cut_generalizes_without_named_join_status(self):
        seed, boundary, vocabulary = self.fixture()
        before = deepcopy(boundary)
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        summary = result.manifest['cut_generalization']
        self.assertEqual(summary['kind'], 'generalized_owned_cut')
        self.assertEqual(result.manifest['emitted_alternative_count'], 1)
        self.assertEqual(summary['plan']['binders'][0]['name'], 'machine_x13')
        self.assertEqual(summary['plan']['relations'][0]['coq'],
                         '(1%Z <= bv_unsigned machine_x13 <= 2%Z)%Z')
        self.assertEqual(boundary, before)

    def test_identical_alternatives_deduplicate_before_generalization(self):
        seed, boundary, vocabulary = self.fixture((1, 1))
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        self.assertEqual(result.manifest['cut_generalization']['kind'], 'exact_deduplication')
        self.assertEqual(result.manifest['emitted_alternative_count'], 1)

    def test_single_alternative_keeps_its_source_shape(self):
        seed, boundary, vocabulary = self.fixture((1,))
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        self.assertEqual(result.manifest['cut_generalization']['kind'], 'single_alternative')

    def test_common_nonempty_guard_survives_generalization(self):
        guard = operation('not', operation('=', input_expr('length'), bits(0, 64)))
        seed, boundary, vocabulary = self.fixture(conditions=(guard,))
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        self.assertIn(guard.to_dict(), result.manifest['cut_generalization']['plan']['common_guards'])

    def test_handwritten_cut_uses_same_multi_alternative_rule(self):
        seed, boundary, vocabulary = self.fixture()
        boundary['status'] = 'handwritten_cut'
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        self.assertEqual(result.manifest['cut_generalization']['kind'], 'generalized_owned_cut')

    def test_mismatched_ownership_refuses_without_disjunction_fallback(self):
        seed, boundary, vocabulary = self.fixture()
        boundary['alternatives'][1]['resource_boundary']['tree']['binders'][0]['name'] = 'other'
        result = self.render(seed, boundary, vocabulary)
        self.assertIsNone(result.response)
        self.assertTrue(result.reports)


if __name__ == '__main__':
    unittest.main()
