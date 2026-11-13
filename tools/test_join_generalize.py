"""Join design controls use declarations and symbolic states, never proof states."""
from pathlib import Path
from copy import deepcopy
import json
import hashlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from forward_design import _footprint, source_liveness
from join_generalize import (anti_unify, exit_pullback, generalize_registers, hull,
                             attach_exit_pullback, continuation_observables,
                             generalize_owned_join, validate_edges, witness_plan, common_conditions)
from forward_resources import (OwnedBytes, ownership_from_assertion_tree,
                               render_resource_boundary, apply_owned_writes)
from resource_seed import OwnedSeed
from forward_resource_design import _state_from_result
from symbolic_state import Expr, MemoryRegion, MemoryWrite, SymbolicState, bits, input_expr, operation


class FootprintTests(unittest.TestCase):
    def test_constant_write_does_not_read_its_destination(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', '#x01']], {'x11'}),
                         (set(), {'x11'}))

    def test_write_expression_keeps_source_reads(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', ['x12']]], {'x11', 'x12'}),
                         ({'x12'}, {'x11'}))

    def test_self_update_reads_its_destination(self):
        self.assertEqual(_footprint([['write-reg', '|x11|', 'nil', ['x11']]], {'x11'}),
                         ({'x11'}, {'x11'}))

    def test_prior_read_survives_a_write(self):
        self.assertEqual(_footprint([['read-reg', '|x11|', 'nil', 'v'],
                                     ['write-reg', '|x11|', 'nil', '#x01']], {'x11'}),
                         ({'x11'}, {'x11'}))

    def test_only_writes_common_to_every_branch_kill_liveness(self):
        branches = [['cases', 'condition', ['trace', ['write-reg', '|x11|', 'nil', '#x01']],
                     ['trace', ['read-reg', '|x12|', 'nil', 'v']]]]
        self.assertEqual(_footprint(branches, {'x11', 'x12'}), ({'x12'}, set()))


class JoinRegisterTests(unittest.TestCase):
    def test_6ae0_generalizes_only_the_two_differing_registers(self):
        fixture = json.loads((Path(__file__).parent / 'block/testdata/join-6ae0-registers.json').read_text())
        alternatives = []
        for row in fixture['alternatives']:
            alternatives.append({**row, 'state': {
                'registers': {**fixture['common_registers'], **row['registers']},
                'conditions': [fixture['conditions'][index] for index in row['condition_ids']]}})
        before = deepcopy(alternatives)
        plan = generalize_registers(alternatives, register_order=fixture['register_order'])
        self.assertEqual([b['name'] for b in plan['binders']], ['machine_x13', 'machine_x14'])
        self.assertEqual(len(plan['edges']), 17)
        self.assertTrue(validate_edges(plan))
        self.assertEqual(plan['witness_plan']['ordered_binders'], ['machine_x13', 'machine_x14'])
        self.assertEqual(plan['witness_plan']['input']['left']['register'], 'x13')
        self.assertEqual(plan['witness_plan']['input']['right']['left']['register'], 'x14')
        self.assertFalse(plan['proof_established'])
        self.assertEqual(alternatives, before)

    def test_equal_after_exact_normalization_keeps_the_value(self):
        word = input_expr('word')
        result = anti_unify([{'x': Expr('bvadd', (word, bits(0, 64)), 64)}, {'x': word}],
                            names={'x': 'machine_x'})
        self.assertEqual(result.values, {'x': word})
        self.assertEqual(result.binders, [])

    def test_width_change_refuses(self):
        with self.assertRaisesRegex(ValueError, 'one closed positive width'):
            anti_unify([{'x': bits(1, 8)}, {'x': bits(1, 64)}], names={'x': 'machine_x'})

    def test_missing_owned_value_refuses(self):
        with self.assertRaisesRegex(ValueError, 'different owned value sets'):
            anti_unify([{'x': bits(1, 64)}, {}], names={'x': 'machine_x'})

    def test_unknown_source_value_refuses(self):
        with self.assertRaisesRegex(ValueError, 'no source binding'):
            anti_unify([{'x': Expr('unknown_read', width=64)}, {'x': bits(1, 64)}],
                       names={'x': 'machine_x'})

    def test_new_binder_cannot_capture_an_outer_input(self):
        with self.assertRaisesRegex(ValueError, 'captures a source input'):
            anti_unify([{'x': input_expr('machine_x')}, {'x': bits(1, 64)}], names={'x': 'machine_x'})

    def test_new_binder_cannot_capture_a_source_declaration(self):
        with self.assertRaisesRegex(ValueError, 'captures a source input'):
            anti_unify([{'x': bits(0, 64)}, {'x': bits(1, 64)}], names={'x': 'machine_x'},
                       reserved_names=['machine_x'])

    def test_equal_dead_values_become_free_binders_without_literal_hulls(self):
        alternatives = [{'state': {'registers': {'x11': bits(0, 64).to_dict()}, 'conditions': []}}] * 2
        result = generalize_registers(alternatives, register_order=['x11'], dead_registers=['x11'])
        self.assertEqual(result['binders'][0]['name'], 'machine_x11')
        self.assertEqual(result['relations'], [])
        self.assertEqual(result['generalized_values'][0]['edge_values'], [bits(0, 64).to_dict()] * 2)
        self.assertTrue(validate_edges(result))


class CommonGuardTests(unittest.TestCase):
    def test_constant_register_substitution_preserves_nonempty_guard(self):
        length = input_expr('input_length', 64)
        guard = operation('not', operation('=', length, bits(0, 64)))
        alternatives = [{'state': {'registers': {'x13': value.to_dict()},
                                   'conditions': [guard.to_dict()]}}
                        for value in [input_expr('byte', 64), bits(0, 64)]]
        plan = generalize_registers(alternatives, register_order=['x13'])
        self.assertIn(guard, common_conditions(alternatives, plan))

    def test_signed_byte_class_becomes_unsigned_hull(self):
        byte = input_expr('source_byte', 8)
        word = Expr('sign_extend', (byte,), 64)
        guard = operation('not', operation('bvslt', word, bits(0, 64)))
        result = hull([word, bits(0, 64)], [[guard], []], name='machine_x13')
        self.assertEqual((result['lower'], result['upper']), (0, 127))
        self.assertIn('bv_unsigned machine_x13', result['coq'])
        self.assertNotIn('Z_to_bv', result['coq'])

    def test_correlated_equal_values_keep_an_existential_source_link(self):
        byte = input_expr('source_byte', 8)
        word = Expr('sign_extend', (byte,), 64)
        guard = operation('not', operation('bvslt', word, bits(0, 64)))
        alternatives = [{'state': {'registers': {'x13': word.to_dict()},
                                   'conditions': [guard.to_dict()]}}] * 2
        plan = generalize_registers(alternatives, register_order=['x13'], relational_registers=['x13'])
        self.assertEqual(plan['binders'][0]['name'], 'machine_x13')
        self.assertTrue(validate_edges(plan))
        self.assertEqual([r['kind'] for r in plan['relations']], ['source_equality', 'unsigned_hull'])
        self.assertIn('source_byte', plan['relations'][0]['coq'])
        self.assertNotIn('Z_to_bv', plan['relations'][1]['coq'])

    def test_correlated_source_link_refuses_different_values(self):
        alternatives = [{'state': {'registers': {'x13': input_expr(name, 64).to_dict()},
                                   'conditions': []}} for name in ['left', 'right']]
        with self.assertRaisesRegex(ValueError, 'differs across incoming edges'):
            generalize_registers(alternatives, register_order=['x13'], relational_registers=['x13'])

    def test_correlated_source_link_refuses_a_branch_literal(self):
        alternatives = [{'state': {'registers': {'x13': bits(0, 64).to_dict()}, 'conditions': []}}] * 2
        with self.assertRaisesRegex(ValueError, 'branch literal'):
            generalize_registers(alternatives, register_order=['x13'], relational_registers=['x13'])

    def test_signed_byte_without_class_fact_has_no_narrow_hull(self):
        byte = input_expr('source_byte', 8)
        word = Expr('sign_extend', (byte,), 64)
        self.assertIsNone(hull([word, bits(0, 64)], [[], []], name='machine_x13'))


class ObservableTests(unittest.TestCase):
    def binding(self, directory, body):
        path = Path(directory) / 'Fixture.v'
        path.write_text('Definition exitResources := ' + body + '.\n')
        return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'declaration': 'exitResources'}

    def test_fixed_exit_value_is_observable_but_independent_ownership_is_not(self):
        with tempfile.TemporaryDirectory() as directory:
            binding = self.binding(directory,
                '(∃ (arbitrary : bv 64), "x11" ↦ᵣ RVal_Bits arbitrary ∗ "x1" ↦ᵣ RVal_Bits return_address)%I')
            result = continuation_observables('instr_pre ret (exitResources)', [binding])
            self.assertEqual(result['registers'], ['x1'])

    def test_pure_relation_keeps_an_existential_register_value_observable(self):
        with tempfile.TemporaryDirectory() as directory:
            binding = self.binding(directory,
                '(∃ (arbitrary : bv 64), "x11" ↦ᵣ RVal_Bits arbitrary ∗ ⌜bv_unsigned arbitrary = meaning⌝)%I')
            self.assertEqual(continuation_observables('exitResources', [binding])['registers'], ['x11'])

    def test_missing_resource_definition_refuses(self):
        with self.assertRaisesRegex(ValueError, 'acyclic source binding'):
            continuation_observables('unknown_exit args', [])

    def test_changed_source_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            binding = self.binding(directory, 'True%I')
            Path(binding['path']).write_text('Definition exitResources := different.\n')
            with self.assertRaisesRegex(ValueError, 'source changed'):
                continuation_observables('exitResources', [binding])

    def test_liveness_keeps_a_trace_read_and_excludes_a_write_target(self):
        function = {'blocks': [{'start': 16, 'end': 20, 'successors': []}], 'rows': [{'pc': 16}]}
        traces = {16: '(trace (read-reg |x1| nil v) (write-reg |x11| nil #x0000000000000000))'}
        result = source_liveness(function, traces, {16: SymbolicState(registers={'x1': input_expr('ret'),
                                                                                 'x11': input_expr('unused')})})
        self.assertEqual(result[16], ['x1'])

    def test_hull_uses_direct_unsigned_binder_bounds(self):
        word = input_expr('word')
        bounded = operation('bvule', word, bits(55, 64))
        result = hull([bits(1, 64), word], [[], [bounded]], name='machine_x12')
        self.assertEqual((result['lower'], result['upper']), (0, 55))
        self.assertIn('bv_unsigned machine_x12', result['coq'])
        self.assertNotIn('Z_to_bv', result['coq'])

    def test_full_type_interval_emits_no_artificial_bound(self):
        self.assertIsNone(hull([input_expr('word')], [[]], name='machine_x12'))

    def test_unavailable_memory_witness_requires_packaging(self):
        with self.assertRaisesRegex(ValueError, 'array packaging'):
            witness_plan([{'name': 'memory_word', 'type': 'bv 64'}], register_bindings={})

    def test_order_is_declaration_order_without_a_python_reversal(self):
        result = witness_plan([{'name': 'last_register', 'type': 'bv 64'},
                               {'name': 'first_register', 'type': 'bv 8'}],
                              register_bindings={'last_register': ('x16', 64), 'first_register': ('x1', 8)})
        self.assertEqual(result['ordered_binders'], ['last_register', 'first_register'])
        self.assertEqual(result['data']['left']['binder'], 'last_register')
        self.assertEqual(result['data']['right']['left']['binder'], 'first_register')

    def test_tampered_edge_value_refuses(self):
        alternatives = [{'state': {'registers': {'x1': bits(value, 64).to_dict()}, 'conditions': []}}
                        for value in (1, 2)]
        plan = generalize_registers(alternatives, register_order=['x1'])
        plan['edges'][0]['widened_substitution']['machine_x1'] = bits(7, 64).to_dict()
        with self.assertRaisesRegex(ValueError, 'changes an owned value'):
            validate_edges(plan)

    def test_tampered_hull_certificate_refuses(self):
        alternatives = [{'state': {'registers': {'x1': bits(value, 64).to_dict()}, 'conditions': []}}
                        for value in (1, 2)]
        plan = generalize_registers(alternatives, register_order=['x1'])
        plan['relations'][0]['edge_intervals'][0] = [0, 0]
        with self.assertRaisesRegex(ValueError, 'interval certificate'):
            validate_edges(plan)


class ExitPullbackTests(unittest.TestCase):
    def test_one_image_creates_one_separate_meaning_link(self):
        exits = [{'kind': 'symbolic_return', 'return': 'return_address', 'image': 'closed_image'}] * 2
        result = exit_pullback(exits, allows={'application': 'allows args', 'source_binding': {'sha256': 'fixture'}})
        self.assertEqual(result['status'], 'generated')
        self.assertEqual(result['image'], 'closed_image')
        self.assertFalse(result['proof_established'])

    def test_different_images_refuse_instead_of_selecting_a_path(self):
        result = exit_pullback([{'kind': 'symbolic_return', 'image': 'a'},
                                {'kind': 'symbolic_return', 'image': 'b'}], allows={})
        self.assertEqual(result['status'], 'refused')

    def test_nonreturn_exit_refuses(self):
        self.assertEqual(exit_pullback([{'kind': 'outside_pc'}], allows={})['status'], 'refused')


class OwnedJoinTests(unittest.TestCase):
    def fixture(self, values=None):
        tree = {'kind': 'exists', 'binders': [{'name': 'old', 'type': 'bv 64',
                                              'expression': input_expr('old').to_dict()}],
                'components': [{'kind': 'register', 'id': 'r', 'register': 'x13', 'value_coq': 'old'},
                               {'kind': 'opaque', 'id': 'terminal', 'coq': 'True'}]}
        ownership = ownership_from_assertion_tree(tree, provenance={'source': 'fixture'})
        seed = OwnedSeed(SymbolicState(registers={'PC': bits(32, 64), 'x13': input_expr('old')}),
                         ownership, [], [], [])
        vocabulary = {'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        alternatives = []
        for value in values or [input_expr('old'), bits(2, 64)]:
            state = seed.state.copy()
            state.registers['x13'] = value
            resource = render_resource_boundary(ownership, apply_owned_writes([], []), state, vocabulary=vocabulary)
            alternatives.append({'predecessor_pc': '0x10', 'seed_pc': '0x10', 'path': [],
                                 'state': state.to_dict(), 'resource_boundary': resource})
        continuation = {'name': 'K', 'coq': 'instr_pre exit_pc exit_resources',
                        'source_binding': {'source': 'Level1.IslarisContractSpec'}, 'terminal_id': 'terminal'}
        return seed, alternatives, vocabulary, continuation

    def test_join_seed_replaces_true_with_outer_continuation(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        before = deepcopy(seed.ownership)
        result = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        owned = result['seed']
        self.assertEqual(owned.join_kind, 'join')
        self.assertEqual([binder['name'] for binder in owned.ownership['binders']], ['machine_x13'])
        self.assertEqual(owned.ownership['tree']['right'], {'kind': 'component', 'id': 'terminal'})
        self.assertEqual(owned.ownership['components'][-1]['source'], 'K')
        self.assertEqual(seed.ownership, before)
        self.assertEqual(result['boundary']['status'], 'generated_join')
        self.assertEqual(result['boundary']['alternatives'][0]['predecessor_pc'], None)
        self.assertEqual(result['boundary']['alternatives'][0]['seed_pc'], '0x20')

    def test_missing_contract_binding_refuses(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        continuation['source_binding'] = {}
        with self.assertRaisesRegex(ValueError, 'source-bound outer continuation'):
            generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                  vocabulary=vocabulary, continuation=continuation)

    def test_different_system_state_refuses(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        alternatives[0]['state']['registers']['system'] = bits(1, 64).to_dict()
        alternatives[1]['state']['registers']['system'] = bits(2, 64).to_dict()
        with self.assertRaisesRegex(ValueError, 'changes system state'):
            generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                  vocabulary=vocabulary, continuation=continuation)

    def test_pullback_uses_the_complete_owned_image_and_keeps_outer_k(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        component = {'id': 'output', 'kind': 'byte_array', 'source': 'base ↦ₘ∗ bytes',
                     'provenance': {'source': 'fixture'}, 'scope': [[]]}
        seed.ownership['components'].insert(-1, component)
        seed.ownership['tree']['body']['children'].insert(-1, {'kind': 'component', 'id': 'output'})
        seed.resources = [OwnedBytes('output', bits(4096, 64), 'base', input_expr('bytes', None),
                                    4, True, 'DfracOwn 1', component, {'source': 'fixture'}, 8)]
        for alternative in alternatives:
            alternative['resource_boundary']['tree'] = deepcopy(seed.ownership['tree'])
            alternative['resource_boundary']['components'].insert(-1, component)
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        before = deepcopy(joined['seed'].ownership)
        state = joined['seed'].state.copy()
        state.registers['PC'] = input_expr('return_address')
        traversal = {'stops': [{'reason': 'unknown_pc', 'stage': 'block_exit', 'path': [],
                               'actual_pc': input_expr('return_address').to_dict(), 'state': state.to_dict()}]}
        result = attach_exit_pullback(joined, traversal, output_resource_id='output',
                                     return_expression=input_expr('return_address'),
                                     allows={'application': 'allows args', 'source_binding': {'source': 'fixture'}},
                                     vocabulary=vocabulary)
        self.assertEqual(result['pullback']['status'], 'generated')
        self.assertEqual(result['pullback']['image'], 'bytes')
        self.assertEqual(result['seed'].ownership['components'][-2]['id'], 'join_exit_meaning')
        self.assertEqual(result['seed'].ownership['components'][-1]['source'], 'K')
        self.assertEqual(joined['seed'].ownership, before)

    def test_exception_path_prevents_attaching_exit_meaning(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        result = attach_exit_pullback(joined, {'stops': [{'reason': 'outside_pc', 'path': []}]},
                                     output_resource_id='output', return_expression=input_expr('return_address'),
                                     allows={}, vocabulary=vocabulary)
        self.assertEqual(result['pullback']['status'], 'refused')
        self.assertFalse(any(c['id'] == 'join_exit_meaning' for c in joined['seed'].ownership['components']))
    def test_a_partial_frame_join_states_the_agreed_saved_word(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        component = {'id': 'frame', 'kind': 'unknown_byte_array', 'source': 'frame ↦ₘ{DfracOwn 1}? 16%Z',
                     'address_z': 'frame', 'length': '16', 'provenance': {'source': 'fixture'}, 'scope': [[]]}
        seed.ownership['components'].insert(-1, component)
        seed.ownership['tree']['body']['children'].insert(-1, {'kind': 'component', 'id': 'frame'})
        seed.resources = [OwnedBytes('frame', bits(4096, 64), 'frame', None, 16, True, 'DfracOwn 1',
                                     component, {'source': 'fixture'}, 8)]
        seed.facts = [{'fact_id': kind, 'kind': kind, 'status': 'supplied', 'origin': {'source': 'fixture'},
                       'terms': {'resource_id': 'frame', 'fraction': 'DfracOwn 1'}}
                      for kind in ('permission', 'nonwrap')]
        saved = MemoryWrite(bits(4104, 64), input_expr('saved_ra'), 8, True)
        for index, alternative in enumerate(alternatives):
            state = _state_from_result(alternative['state'])
            state.writes = [saved] + ([MemoryWrite(bits(4096, 64), bits(7, 8), 1, True)] if index else [])
            image = apply_owned_writes(seed.resources, state.writes, facts=seed.facts)
            alternative['state'] = state.to_dict()
            alternative['resource_boundary'] = render_resource_boundary(seed.ownership, image, state,
                                                                        vocabulary=vocabulary)
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        frame, = [row['source'] for row in joined['boundary']['alternatives'][0]['resource_boundary']['components']
                  if row['id'] == 'frame']
        self.assertIn('(frame) ↦ₘ{DfracOwn 1}? 8%Z', frame)
        self.assertIn('bv_extract 56%N 8%N saved_ra', frame)
        self.assertNotIn('? 16%Z', frame)

    def add_component(self, seed, alternatives, component, sources):
        seed.ownership['components'].insert(-1, component)
        seed.ownership['tree']['body']['children'].insert(-1, {'kind': 'component', 'id': component['id']})
        for alternative, source in zip(alternatives, sources):
            alternative['resource_boundary']['tree'] = deepcopy(seed.ownership['tree'])
            alternative['resource_boundary']['components'].insert(-1, {**component, 'source': source})

    def test_a_pure_fact_the_edges_state_differently_is_dropped(self):
        seed, alternatives, vocabulary, continuation = self.fixture()
        self.add_component(seed, alternatives, {'id': 'fact', 'kind': 'opaque', 'source': '⌜P 0⌝',
                                                'provenance': {'source': 'fixture'}, 'scope': [[]]},
                           ['⌜P 0⌝', '⌜P 1⌝'])
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        fact, = [row['source'] for row in joined['boundary']['alternatives'][0]['resource_boundary']['components']
                 if row['id'] == 'fact']
        self.assertEqual(fact, '⌜True⌝')

    def test_a_pure_fact_over_each_edges_register_value_generalizes(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        seed, alternatives, vocabulary, continuation = self.fixture([input_expr('old'), moved])
        self.add_component(seed, alternatives, {'id': 'fact', 'kind': 'opaque', 'source': '⌜P old⌝',
                                                'provenance': {'source': 'fixture'}, 'scope': [[]]},
                           ['⌜P old⌝', '⌜P %s⌝' % moved.coq()])
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        fact, = [row['source'] for row in joined['boundary']['alternatives'][0]['resource_boundary']['components']
                 if row['id'] == 'fact']
        self.assertEqual(fact, '⌜P machine_x13⌝')
        self.assertEqual(joined['plan']['generalized_facts'], ['fact'])

    def test_a_join_binder_avoids_a_name_that_an_edge_fact_binds(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        seed, alternatives, vocabulary, continuation = self.fixture([input_expr('old'), moved])
        local = '⌜∃ machine_x13, P %s machine_x13⌝'
        self.add_component(seed, alternatives, {'id': 'fact', 'kind': 'opaque', 'source': local % 'old',
                                                'provenance': {'source': 'fixture'}, 'scope': [[]]},
                           [local % 'old', local % moved.coq()])
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        self.assertEqual([binder['name'] for binder in joined['seed'].ownership['binders']], ['machine_x13_1'])
        fact, = [row['source'] for row in joined['boundary']['alternatives'][0]['resource_boundary']['components']
                 if row['id'] == 'fact']
        self.assertEqual(fact, local % 'machine_x13_1')

    def test_a_pure_fact_naming_a_value_slice_keeps_the_binders_placement(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        seed, alternatives, vocabulary, continuation = self.fixture([input_expr('old'), moved])
        array = {'id': 'input', 'kind': 'byte_array', 'source': 'base ↦ₘ∗ bytes',
                 'provenance': {'source': 'fixture'}, 'scope': [[]]}
        self.add_component(seed, alternatives, array, ['base ↦ₘ∗ bytes'] * 2)
        seed.resources = [OwnedBytes('input', bits(4096, 64), 'base', input_expr('bytes', None),
                                     4, True, 'DfracOwn 1', array, {'source': 'fixture'}, 8)]
        slice_of = '⌜Q (drop (Z.to_nat (bv_unsigned (%s) - base)) bytes)⌝'
        self.add_component(seed, alternatives, {'id': 'fact', 'kind': 'opaque', 'source': slice_of % 'old',
                                                'provenance': {'source': 'fixture'}, 'scope': [[]]},
                           [slice_of % 'old', slice_of % moved.coq()])
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        rows = {row['id']: row['source'] for row in
                joined['boundary']['alternatives'][0]['resource_boundary']['components']}
        self.assertEqual(rows['fact'], slice_of % 'machine_x13')
        self.assertEqual(rows['join_relation_0'],
                         '⌜(base <= bv_unsigned machine_x13 <= base + Z.of_nat (List.length (bytes)))%Z⌝')
        self.assertEqual(joined['plan']['relations'][-1]['kind'], 'array_placement')

    def slot_join(self, values, stored, *, initialized=True):
        """A join of edges whose 8-byte slot holds the bytes of `stored[i]` from the edge's seed."""
        seed, alternatives, vocabulary, continuation = self.fixture(values)
        old = 'slot ↦ₘ∗ slot_bytes' if initialized else 'slot ↦ₘ? 8'
        slot = {'id': 'slot', 'kind': 'byte_array' if initialized else 'unknown_byte_array', 'source': old,
                'address_z': 'slot', 'provenance': {'source': 'fixture'}, 'scope': [[]]}
        if initialized:
            slot['value'] = 'slot_bytes'
        listed = lambda word: '[' + '; '.join(operation('extract', word, width=8, value=8 * index).coq()
                                              for index in range(8)) + ']'
        self.add_component(seed, alternatives, slot, ['slot ↦ₘ∗ ' + listed(word) for word in stored])
        seed.resources = [OwnedBytes('slot', bits(4096, 64), 'slot',
                                     input_expr('slot_bytes', None) if initialized else None,
                                     8, True, 'DfracOwn 1', slot, {'source': 'fixture'}, 8)]
        for alternative, word in zip(alternatives, stored):
            state = _state_from_result(alternative['state'])
            state.memory = [MemoryRegion(bits(4096, 64), tuple(operation('extract', word, width=8, value=8 * index)
                                                                 for index in range(8)),
                                         input_expr(listed(word), None), 8, ownership_id='slot')]
            alternative['state'] = state.to_dict()
        joined = generalize_owned_join(alternatives, original_seed=seed, entry_pc=32,
                                       vocabulary=vocabulary, continuation=continuation)
        rows = {row['id']: row['source'] for row in
                joined['boundary']['alternatives'][0]['resource_boundary']['components']}
        return joined, rows, listed

    def test_a_slot_holding_each_edges_register_value_states_the_register_binder(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        joined, rows, listed = self.slot_join([input_expr('old'), moved], [input_expr('old'), moved])
        binder = input_expr('machine_x13')
        self.assertEqual(rows['slot'], 'slot ↦ₘ∗ ' + listed(binder))
        self.assertNotIn('join_slot_bytes', [row['name'] for row in joined['seed'].ownership['binders']])
        self.assertEqual(joined['plan']['memory_relations'][0]['kind'], 'register_image')
        region, = [row for row in joined['seed'].state.memory if row.ownership_id == 'slot']
        self.assertEqual(region.bytes, tuple(operation('extract', binder, width=8, value=8 * index)
                                             for index in range(8)))

    def test_an_uninitialized_slot_holding_each_edges_register_value_states_the_register_binder(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        _, rows, listed = self.slot_join([input_expr('old'), moved], [input_expr('old'), moved], initialized=False)
        self.assertEqual(rows['slot'], 'slot ↦ₘ∗ ' + listed(input_expr('machine_x13')))

    def test_a_slot_holding_another_value_on_one_edge_stays_packed(self):
        moved = operation('bvadd', input_expr('old'), bits(8, 64))
        joined, rows, _ = self.slot_join([input_expr('old'), moved], [input_expr('old'), bits(5, 64)])
        self.assertEqual(rows['slot'], 'slot ↦ₘ∗ join_slot_bytes')
        self.assertEqual(joined['plan']['memory_relations'][0]['kind'], 'array_packaging')

    def test_a_register_value_without_a_coq_rendering_states_no_slot(self):
        from join_generalize import register_image
        unrendered = Expr('owned_array_byte', (input_expr('frame', None),), 64, 0)
        word = input_expr('machine_x13')
        listed = '[' + '; '.join(operation('extract', word, width=8, value=8 * index).coq()
                                 for index in range(8)) + ']'
        plan = {'values': {'x13': word.to_dict()}, 'edges': [{'original_values': {'x13': value.to_dict()}}
                                                           for value in (word, unrendered)]}
        slot = OwnedBytes('slot', bits(4096, 64), 'slot', input_expr('slot_bytes', None), 8, True,
                          'DfracOwn 1', {}, {'source': 'fixture'}, 8)
        self.assertIsNone(register_image(slot, ['slot ↦ₘ∗ ' + listed] * 2, plan, ['x13'], 'little'))
        self.assertEqual(register_image(slot, ['slot ↦ₘ∗ ' + listed] * 2, {**plan, 'edges': plan['edges'][:1] * 2},
                                        ['x13'], 'little')[0], 'x13')


class LiftedEdges(unittest.TestCase):
    def test_an_edge_from_a_seed_below_another_root_lifts_on_its_own_tree(self):
        from test_resource_seed import ORIGIN, VOCABULARY, public_seed
        from join_generalize import lift_call_return_edges
        from resource_seed import seed_owned_resources
        from symbolic_state import MemoryWrite, bits, input_expr, operation
        vocabulary = {**VOCABULARY, 'input_sha256': 'fixture', 'source_vocabulary': {'imports': []}}
        base = seed_owned_resources(public_seed(), entry_pc=16, vocabulary=vocabulary,
                                    constants={'frame_size': {'value': 16, 'origin': ORIGIN}})
        state = base.state.copy()
        frame = base.resources[1]
        state.writes = [MemoryWrite(operation('bvadd', frame.base, bits(8, 64)), input_expr('v', 64), 8,
                                    ownership_id='frame')]
        edge = {'seed_pc': 'J', 'predecessor_pc': '0x10', 'path': [], 'state': state.to_dict()}
        # J is a join seed whose root R lies below the ancestor A: its edge lifts byte by byte.
        lifted, _ = lift_call_return_edges([edge], seeds={'A': base, 'J': base}, roots={'A': 'A', 'J': 'R'},
                                           ancestor='A', vocabulary=vocabulary)
        self.assertEqual((lifted[0]['lifted_from'], len(lifted[0]['state']['writes'])), ('J', 8))
        with self.assertRaisesRegex(ValueError, 'without a root'):
            lift_call_return_edges([edge], seeds={'A': base, 'J': base}, roots={'A': 'A'},
                                   ancestor='A', vocabulary=vocabulary)


if __name__ == '__main__':
    unittest.main()
