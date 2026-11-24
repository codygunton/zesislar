"""A return package reached by several alternatives generalizes at the return site (G-ret):
`entry_formatter.format_owned_entry_boundary` on a `function_return` boundary calls
`join_generalize.generalize_owned_join` with no join location; the shared return-address
expression stays the package's PC and what differs between the exits becomes existential."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from entry_formatter import RETURN_LIVE_REGISTERS, SourceComponents, SymbolicConditions, format_owned_entry_boundary
from forward_resources import ownership_from_assertion_tree, render_resource_boundary, apply_owned_writes
from resource_seed import OwnedSeed
from symbolic_state import SymbolicState, bits, input_expr, operation
import entry_hist

RETURN = input_expr('returnAddress', 64)
LEFT, RIGHT = input_expr('leftWord', 64), input_expr('rightWord', 64)
# Three genuine exits of a compare: left below right, left past the input end, right past it.
GUARDS = [operation('bvult', LEFT, RIGHT), operation('=', LEFT, bits(0, 64)), operation('=', RIGHT, bits(0, 64))]


class ReturnGeneralization(unittest.TestCase):
    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap'})

    def fixture(self, exits, pc='function_return', closing='True'):
        """exits: (x10 value, x5 value, guards, return address) per exit. closing: the seed's closing leaf."""
        binders = [{'name': name, 'type': 'bv 64', 'expression': input_expr(name).to_dict()}
                   for name in ('old10', 'old5')]
        tree = {'kind': 'exists', 'binders': binders,
                'components': [{'kind': 'register', 'id': 'a0', 'register': 'x10', 'value_coq': 'old10'},
                               {'kind': 'register', 'id': 't0', 'register': 'x5', 'value_coq': 'old5'},
                               {'kind': 'opaque', 'id': 'terminal', 'coq': closing}]}
        ownership = ownership_from_assertion_tree(tree, provenance={'source': 'fixture'})
        seed = OwnedSeed(SymbolicState(registers={'PC': bits(0x800f0000, 64), 'x10': input_expr('old10'),
                                                  'x5': input_expr('old5')}), ownership, [], [], [])
        vocabulary = {'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        alternatives = []
        for x10, x5, guards, target in exits:
            state = seed.state.copy()
            state.registers.update({'PC': target, 'x10': x10, 'x5': x5})
            state.conditions = list(guards)
            resource = render_resource_boundary(ownership, apply_owned_writes([], []), state, vocabulary=vocabulary)
            alternatives.append({'predecessor_pc': '0x800f0230', 'seed_pc': '0x800f0000', 'path': [],
                                 'state': state.to_dict(), 'resource_boundary': deepcopy(resource)})
        return seed, {'pc': pc, 'status': 'generated', 'alternatives': alternatives}, vocabulary

    def render(self, seed, boundary, vocabulary):
        def provenance(*args):
            return {'source': 'fixture'}
        return format_owned_entry_boundary(boundary, original_seed=seed, vocabulary=vocabulary,
            continuation={'name': 'K', 'coq': 'instr_pre exit_pc exit_resources',
                          'source_binding': {'source': 'Level1'}, 'terminal_id': 'terminal'},
            continuation_id='level1_K', case_id='ret', source_policy='source-only',
            handwritten_owner='Level1', guard_scope=(0,),
            component_adapter=SourceComponents({'K': {'owner': 'parameter', 'name': 'K'}},
                                              continuation_id='level1_K', provenance=provenance),
            condition_adapter=SymbolicConditions(provenance),
            helper_arguments=lambda body, context: [])

    def test_one_alternative_renders_as_before(self):
        seed, boundary, vocabulary = self.fixture([(bits(1, 64), bits(7, 64), GUARDS[:1], RETURN)])
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        self.assertEqual(result.manifest['cut_generalization']['kind'], 'single_alternative')
        # The same exit at a join location renders the same body: the return path adds nothing.
        _, at_block, _ = self.fixture([(bits(1, 64), bits(7, 64), GUARDS[:1], RETURN)], pc='0x800f0238')
        body = self.render(seed, at_block, vocabulary).response['body']
        self.assertEqual(result.response['body'], {**body, 'at': 'function_return'})

    def test_a_seed_closed_by_the_continuation_frames_it_once(self):
        # A seed below a loop-owned root (loop_design.owned_seed) ends in its root's closing `K`.
        exits = [(bits(1, 64), bits(7, 64), GUARDS[:1], RETURN)]
        seed, boundary, vocabulary = self.fixture(exits, pc='0x800f0238', closing='K')
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        body = result.response['body']
        self.assertEqual([row['kind'] for row in body['components']], ['application', 'continuation'])
        kinds = [row['kind'] for row in body['additional_definitions'][0]['body']['components']]
        self.assertNotIn('continuation', kinds)
        self.assertNotIn('application', kinds)
        # The same seed closed by `True` keeps that leaf in its witness scope; nothing else differs.
        plain_seed, plain, _ = self.fixture(exits, pc='0x800f0238')
        plain_kinds = [row['kind'] for row in self.render(plain_seed, plain, vocabulary)
                       .response['body']['additional_definitions'][0]['body']['components']]
        self.assertEqual(plain_kinds, [*kinds[:2], 'true', *kinds[2:]])

    def test_three_exits_differing_in_a_dead_register(self):
        seed, boundary, vocabulary = self.fixture([(bits(1, 64), bits(n, 64), [guard], RETURN)
                                                   for n, guard in enumerate(GUARDS)])
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        summary = result.manifest['cut_generalization']
        self.assertEqual(summary['kind'], 'generalized_owned_cut')
        self.assertEqual(summary['original_alternative_count'], 3)
        self.assertEqual(result.manifest['emitted_alternative_count'], 1)
        self.assertEqual([row['name'] for row in summary['plan']['binders']], ['machine_x5'])
        text = repr(result.response['body'])
        # The result register keeps its common value; the dead one is existential and its only
        # facts are its range over the exits' values (no link to a path guard).
        self.assertNotIn('machine_x10', text)
        self.assertIn('RVal_Bits (machine_x5 : bv 64%N)', text)
        self.assertNotIn('leftWord', text)

    def test_exits_differing_in_the_result_register(self):
        seed, boundary, vocabulary = self.fixture([(bits(n, 64), bits(0, 64), [guard], RETURN)
                                                   for n, guard in enumerate(GUARDS)])
        result = self.render(seed, boundary, vocabulary)
        self.assertEqual(result.status, 'complete', result.reports)
        summary = result.manifest['cut_generalization']
        self.assertEqual([row['name'] for row in summary['plan']['binders']], ['machine_x10'])
        # The live result is existential, stated by the exits' values (the guards here name no
        # contract input, so no guarded link is admissible).
        text = repr(result.response['body'])
        self.assertIn('RVal_Bits (machine_x10 : bv 64%N)', text)
        for n in range(3):
            self.assertIn('((bv_unsigned machine_x10) = (%d%%Z))' % n, text)

    def test_exits_to_different_addresses_are_refused(self):
        seed, boundary, vocabulary = self.fixture([(bits(1, 64), bits(0, 64), GUARDS[:1], RETURN),
                                                   (bits(1, 64), bits(1, 64), GUARDS[1:2], bits(0x80000000, 64))])
        result = self.render(seed, boundary, vocabulary)
        self.assertIsNone(result.response)
        self.assertIn('different addresses', result.reports[0]['detail'])


if __name__ == '__main__':
    unittest.main()
