"""Loop-cut owned state from an annotation row (`owned`): compile, class and seed."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'oblig'))

import annotations  # noqa: E402
from loop_design import loop_class, owned_node, owned_seed, replaced_components  # noqa: E402
from resource_seed import configure_array_words, seed_owned_resources  # noqa: E402
from symbolic_state import SymbolicState, input_expr  # noqa: E402

HEAD, PRED = '+0x10', '+0x8'


def annotation(row):
    return {'schema': annotations.SCHEMA, 'function': 'f', 'symbol': 'f', 'profile': {}, 'rows': [row]}


def cut_row(**extra):
    return {'id': 'loop', 'request': None, 'at': {'pc': HEAD, 'boundary': 'loop_cut', 'predecessor': PRED},
            'binders': [{'name': 'machine_x10', 'register': 'x10'}, {'name': 'i', 'role': 'index'}, *extra.pop('binders', [])],
            'facts': [{'coq': '(0 <= i)%Z', 'role': 'index_range'}, *extra.pop('facts', [])], **extra}


class Profile:
    args_type = 'Args'

    @staticmethod
    def pc(key):
        return hex(int(key[1:], 16))

    @staticmethod
    def telescope():
        return ''


OWNED = {'binders': [{'name': 'list_state', 'type': 'ArrayListState'}],
         'resources': [{'coq': '(sp - 448) ↦ₘ∗ arrayListHeaderBytes list_state', 'length': '24'},
                       'arrayListBuffer 40 3 list_state'],
         'replaces': ['(sp - 448) ↦ₘ? 24']}


def report():
    sources = [('x10', '"x10" ↦ᵣ RVal_Bits (v : bv 64%N)'), ('frame', '(sp - 448) ↦ₘ? 24'),
               ('input', 'p ↦ₘ∗ bytes'), ('domain', '⌜domain args⌝'), ('true', 'True')]
    state = SymbolicState(registers={'x10': input_expr('v', 64)})
    edge = {'predecessor_pc': Profile.pc(PRED), 'state': state.to_dict(),
            'resource_boundary': {'block_status': 'completed', 'components': [
                {'id': key, 'source': text} for key, text in sources],
                'tree': {'kind': 'exists', 'binders': [], 'body': {'children': [{'id': key} for key, _ in sources]}}}}
    return {'boundaries': [{'pc': Profile.pc(HEAD), 'alternatives': [edge]}]}


def design(**extra):
    return {'head': HEAD, 'entry_predecessor': PRED, 'registers': {'x10': 'machine_x10'}, 'index': 'i',
            'facts': [{'kind': 'index_range', 'coq': '(0 <= i)%Z'}], **extra}


class CompileTest(unittest.TestCase):
    def test_a_row_without_owned_state_compiles_as_before(self):
        profile = annotations.compile_profile(annotation(cut_row()))
        self.assertNotIn('owned', profile['loop_designs'][0])

    def test_typed_binders_resources_and_replaces_become_owned(self):
        row = cut_row(binders=[{'name': 'list_state', 'type': 'ArrayListState'}],
                      resources=OWNED['resources'], replaces=OWNED['replaces'])
        self.assertEqual(annotations.compile_profile(annotation(row))['loop_designs'][0]['owned'], OWNED)

    def test_a_loose_binder_needs_a_type(self):
        with self.assertRaises(annotations.AnnotationError):
            annotations.compile_profile(annotation(cut_row(binders=[{'name': 'list_state'}])))


class ClassTest(unittest.TestCase):
    def test_the_class_swaps_the_replaced_component_for_the_owned_state(self):
        source, record = loop_class(report(), design(
            owned=OWNED, facts=[{'kind': 'index_range', 'coq': '(0 <= i)%Z'},
                                {'kind': 'fact', 'coq': 'arrayListLength list_state = i'}]), Profile)
        self.assertNotIn('↦ₘ? 24', source)
        self.assertIn('(sp - 448) ↦ₘ∗ arrayListHeaderBytes list_state', source)
        self.assertIn('arrayListBuffer 40 3 list_state', source)
        self.assertIn('(list_state : ArrayListState)', source)
        self.assertIn('⌜arrayListLength list_state = i⌝', source)
        self.assertEqual(record['owned'], OWNED)

    def test_a_replaced_component_may_be_named_by_its_id(self):
        self.assertEqual(replaced_components({'replaces': [{'id': 'a'}]}, {'a': 'p ↦ₘ? 8'}), ['a'])
        with self.assertRaises(ValueError):
            replaced_components({'replaces': [{'id': 'b'}]}, {'a': 'p ↦ₘ? 8'})

    def test_a_hand_design_whose_head_is_not_reached_is_a_refused_cut(self):
        from loop_design import loop_head_rows
        unreached = {'boundaries': [{'pc': Profile.pc(HEAD), 'alternatives': []}]}
        profile = type('P', (Profile,), {'path': __file__, 'domain_component': '⌜domain args⌝',
                                         'get': staticmethod(lambda key, default=None: [design()]
                                                             if key == 'loop_designs' else default)})
        rows = loop_head_rows(unreached, Path(__file__), profile)
        self.assertEqual(rows['rows'], [])
        self.assertIn(HEAD, rows['inferred_refusals'])
        with self.assertRaises(ValueError):
            loop_head_rows(report(), Path(__file__), type('Q', (profile,), {
                'get': staticmethod(lambda key, default=None: [design(entry_predecessor='+0x8', index='i',
                                                                       owned={'replaces': ['nothing'],
                                                                              'resources': [], 'binders': []})]
                                    if key == 'loop_designs' else default)}))

    def test_without_owned_state_the_class_is_unchanged(self):
        source, record = loop_class(report(), design(), Profile)
        self.assertIn('(sp - 448) ↦ₘ? 24', source)
        self.assertNotIn('owned', record)

    def test_a_replaced_text_must_name_one_component(self):
        with self.assertRaises(ValueError):
            replaced_components({'replaces': ['q ↦ₘ? 8']}, {'a': 'p ↦ₘ? 8'})


class SeedTest(unittest.TestCase):
    def test_node_kinds(self):
        self.assertEqual(owned_node('arrayListBuffer 40 3 s', 0)['kind'], 'opaque')
        self.assertEqual(owned_node('(sp - 8) ↦ₘ? 8', 1)['kind'], 'uninitialized_memory')
        self.assertEqual(owned_node({'coq': 'sp ↦ₘ∗ bytes', 'length': '24'}, 2)['kind'], 'byte_array')
        with self.assertRaises(ValueError):
            owned_node('sp ↦ₘ∗ bytes', 3)

    def test_the_seed_swaps_the_replaced_component_for_the_owned_state(self):
        public = {'schema': 'h1-public-entry-seed.v1', 'entry_pc': '0x10', 'source_bindings': [],
                  'assertion_tree': {'kind': 'exists', 'binders': [], 'components': [
                      {'kind': 'uninitialized_memory', 'id': 'frame', 'original_component': '(sp - 448) ↦ₘ? 24',
                       'address_z': 'sp - 448', 'length_original_coq': '24'},
                      {'kind': 'opaque', 'id': 'true', 'coq': 'True'}]}}
        public['_input_sha256'] = '0' * 64
        seed = seed_owned_resources(public, entry_pc=0x10, vocabulary={'rows': []})
        rebuilt = owned_seed(seed, design(owned=OWNED, facts=[{'kind': 'fact', 'coq': 'arrayListLength list_state = 0'},
                                                              {'kind': 'bound', 'coq': 'bv_unsigned {x10} = 0'}]),
                             0x10, {'rows': []})
        texts = [str(c['seed_component'].get('original_component', c['seed_component'].get('coq')))
                 for c in rebuilt.ownership['components']]
        self.assertNotIn('(sp - 448) ↦ₘ? 24', texts)
        self.assertIn('(sp - 448) ↦ₘ∗ arrayListHeaderBytes list_state', texts)
        self.assertIn('arrayListBuffer 40 3 list_state', texts)
        self.assertIn('⌜arrayListLength list_state = 0⌝', texts)
        self.assertNotIn('⌜bv_unsigned {x10} = 0⌝', texts)
        self.assertEqual(texts[-1], 'True')
        self.assertIn('list_state', [binder['name'] for binder in rebuilt.ownership['binders']])
        self.assertEqual(rebuilt.join_kind, 'loop_head')
        self.assertEqual([resource.id for resource in rebuilt.resources], ['loop_owned_0'])
        # A loop nested below this one keeps these ids; its own carry its head.
        inner = {'binders': [{'name': 'inner_state', 'type': 'ArrayListState'}],
                 'resources': [{'coq': '(sp - 280) ↦ₘ∗ arrayListHeaderBytes inner_state', 'length': '24'}],
                 'replaces': []}
        nested = owned_seed(rebuilt, design(owned=inner, facts=[{'kind': 'fact', 'coq': 'arrayListLength inner_state = 0'}]),
                            0x20, {'rows': []})
        ids = [component['id'] for component in nested.ownership['components']]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertIn('loop_owned_fact_0', ids)
        self.assertIn('loop_owned_20_fact_0', ids)
        self.assertEqual([resource.id for resource in nested.resources], ['loop_owned_0', 'loop_owned_20_0'])

    def test_a_pure_fact_keeps_the_text_the_join_gave_it(self):
        # The join before the head dropped the binder `kept` and moved its fact into its history (here
        # `⌜True⌝`); the owned seed must not restore the root's text, which names an unbound binder.
        public = {'schema': 'h1-public-entry-seed.v1', 'entry_pc': '0x10', 'source_bindings': [],
                  'assertion_tree': {'kind': 'exists', 'binders': [
                      {'name': 'kept', 'type': 'bv 64', 'expression': input_expr('kept', 64).to_dict()}],
                      'components': [
                          {'kind': 'uninitialized_memory', 'id': 'frame', 'original_component': '(sp - 448) ↦ₘ? 24',
                           'address_z': 'sp - 448', 'length_original_coq': '24'},
                          {'kind': 'opaque', 'id': 'kept_value', 'coq': '⌜(zesu_named_eq kept 1)⌝'},
                          {'kind': 'opaque', 'id': 'true', 'coq': 'True'}]}}
        public['_input_sha256'] = '0' * 64
        seed = seed_owned_resources(public, entry_pc=0x10, vocabulary={'rows': []})
        component = next(row for row in seed.ownership['components'] if row['id'] == 'kept_value')
        component['source'] = '⌜True⌝'
        seed.ownership['binders'] = [row for row in seed.ownership['binders'] if row['name'] != 'kept']
        rebuilt = owned_seed(seed, design(owned=OWNED), 0x10, {'rows': []})
        texts = {c['id']: c['seed_component'].get('coq') for c in rebuilt.ownership['components']}
        self.assertEqual(texts['kept_value'], '⌜True⌝')


class ArrayWordsTest(unittest.TestCase):
    """Profile `array_words`: an owned array `F ARG` holds the word `G ARG` at each listed offset."""

    def seed(self, value):
        public = {'schema': 'h1-public-entry-seed.v1', 'entry_pc': '0x10', 'source_bindings': [],
                  'assertion_tree': {'kind': 'exists', 'binders': [], 'components': [
                      owned_node({'coq': '(sp - 280) ↦ₘ∗ ' + value, 'length': '24'}, 0),
                      {'kind': 'opaque', 'id': 'true', 'coq': 'True'}]}}
        public['_input_sha256'] = '0' * 64
        return seed_owned_resources(public, entry_pc=0x10, vocabulary={'rows': []})

    def tearDown(self):
        configure_array_words({})

    def test_the_rule_links_each_word(self):
        configure_array_words({'array_words': [{'array': 'arrayListHeaderBytes',
                                                'words': {'0': 'arrayListPointer', '8': 'arrayListLength'}}]})
        links = self.seed('arrayListHeaderBytes (listAfter out)').state.word_links
        self.assertEqual([(link['offset'], link['value'].value) for link in links],
                         [(0, '(Z_to_bv 64%N (arrayListPointer (listAfter out)))'),
                          (8, '(Z_to_bv 64%N (arrayListLength (listAfter out)))')])
        self.assertEqual(self.seed('otherBytes s').state.word_links, [])

    def test_without_the_key_no_word_is_linked(self):
        self.assertEqual(self.seed('arrayListHeaderBytes s').state.word_links, [])
        with self.assertRaisesRegex(ValueError, 'array_words'):
            configure_array_words({'array_words': [{'array': 'arrayListHeaderBytes', 'words': {'x': 'p'}}]})


class JoinOwnedTest(unittest.TestCase):
    """A join row with owned state (`join_owned`): the loop_cut owned schema at a join."""

    def row(self, **extra):
        return {'id': 'join', 'request': None,
                'at': {'pc': '+0x42c', 'boundary': 'join', 'predecessors': ['+0x400', '+0x428']},
                'binders': [{'name': 'entries', 'type': 'ArrayListState'}, *extra.pop('binders', [])],
                'resources': ['arrayListBuffer 40 3 entries'], 'replaces': ['p ↦ₘ∗ old'],
                'facts': [{'coq': 'arrayListLength entries = n', 'role': 'owned'},
                          {'coq': 'bv_unsigned {x10} = 0', 'role': 'fact'}], **extra}

    def test_the_row_compiles_to_join_owned_and_keeps_its_other_facts_as_join_facts(self):
        profile = annotations.compile_profile(annotation(self.row()))
        self.assertEqual(profile['join_owned'], {'+0x42c': {
            'binders': [{'name': 'entries', 'type': 'ArrayListState'}],
            'resources': ['arrayListBuffer 40 3 entries'], 'replaces': ['p ↦ₘ∗ old'],
            'facts': [{'coq': 'arrayListLength entries = n'}], 'predecessors': ['+0x400', '+0x428']}})
        self.assertEqual(profile['join_designs'], {'+0x42c': ['bv_unsigned {x10} = 0']})
        # A join row without resources or replaces compiles as before.
        plain = self.row()
        del plain['resources'], plain['replaces']
        self.assertNotIn('join_owned', annotations.compile_profile(annotation(plain)))

    def test_binders_are_existentials_never_selectors(self):
        for row, message in (
                (self.row(binders=[{'name': 'machine_x10', 'register': 'x10'}]), 'no register'),
                (self.row(binders=[{'name': 'grew', 'type': 'bool'}]), 'Boolean path selector'),
                (self.row(binders=[{'name': 'path', 'type': 'Z'}],
                          facts=[{'coq': '(path = 1%Z)', 'role': 'owned'}]), 'branch literal'),
                (self.row(binders=[{'name': 'grew', 'type': 'Z'}],
                          facts=[{'coq': 'true = grew', 'role': 'owned'}]), 'branch literal'),
                (self.row(at={'pc': '+0x42c', 'boundary': 'join'}), 'predecessor blocks')):
            with self.assertRaisesRegex(annotations.AnnotationError, message):
                annotations.compile_profile(annotation(row))

    def test_the_join_seed_takes_the_owned_state_and_keeps_its_join_records(self):
        from loop_design import owned_join_seed
        public = {'schema': 'h1-public-entry-seed.v1', 'entry_pc': '0x42c', 'source_bindings': [],
                  'assertion_tree': {'kind': 'exists', 'binders': [], 'components': [
                      {'kind': 'uninitialized_memory', 'id': 'frame', 'original_component': '(sp - 448) ↦ₘ? 24',
                       'address_z': 'sp - 448', 'length_original_coq': '24'},
                      {'kind': 'opaque', 'id': 'true', 'coq': 'True'}]}}
        public['_input_sha256'] = '0' * 64
        seed = seed_owned_resources(public, entry_pc=0x42c, vocabulary={'rows': []})
        seed.join_kind, seed.join_edges, seed.join_witness_plan = 'call_return', [{'predecessor_pc': '0x400'}], {'x': 1}
        owned = {**OWNED, 'facts': [{'coq': 'arrayListLength list_state = n'}], 'predecessors': ['0400', '0428']}
        rebuilt = owned_join_seed(seed, owned, 0x42c, {'rows': []})
        texts = [str(c['seed_component'].get('original_component', c['seed_component'].get('coq')))
                 for c in rebuilt.ownership['components']]
        self.assertNotIn('(sp - 448) ↦ₘ? 24', texts)
        self.assertIn('arrayListBuffer 40 3 list_state', texts)
        self.assertIn('⌜arrayListLength list_state = n⌝', texts)
        self.assertEqual((rebuilt.join_kind, rebuilt.join_edges, rebuilt.join_witness_plan),
                         ('call_return', [{'predecessor_pc': '0x400'}], {'x': 1}))
        binder, = [binder for binder in rebuilt.ownership['binders'] if binder['name'] == 'list_state']
        self.assertTrue(binder['owned'])


if __name__ == '__main__':
    unittest.main()
