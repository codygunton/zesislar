"""Assemble loop ownership without discarding source obligations."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from forward_resources import OwnedBytes, ownership_from_assertion_tree, parse_source_ownership
from loop_join_resources import assemble_loop_class
from resource_seed import OwnedSeed
from symbolic_state import MemoryWrite, SymbolicState, bits, input_expr, operation


class LoopJoinResourceTests(unittest.TestCase):
    def fixture(self):
        tree = {'kind': 'exists', 'binders': [{'name': 'before', 'type': 'bv 64'}],
            'components': [
                {'kind': 'register', 'id': 'cursor', 'register': 'x15', 'value_coq': 'before'},
                {'kind': 'register', 'id': 'endpoint', 'register': 'x11', 'value_coq': 'end'},
                {'kind': 'opaque', 'id': 'terminal', 'coq': 'True'}]}
        ownership = ownership_from_assertion_tree(tree, provenance={'source': 'bound-source'})
        original = SymbolicState({'PC': bits(16, 64), 'x15': input_expr('before'), 'x11': input_expr('end')})
        seed = OwnedSeed(original, ownership, [], [], [])
        state = original.copy();state.registers['x15'] = input_expr('machine_x15')
        state.conditions = [operation('=', bits(1, 64), bits(1, 64))]
        relation = {'kind': 'affine_cursor', 'term': 'bv_unsigned machine_x15 = origin + i',
                    'lower_bound': '0 <= i', 'upper_bound': 'bv_unsigned machine_x15 < bv_unsigned machine_x11'}
        rows = [{'name': 'machine_x15', 'type': 'bv 64', 'register': 'x15', 'role': 'free'},
            {'name': 'machine_x11', 'type': 'bv 64', 'register': 'x11', 'role': 'observed_alias',
             'source_expression': input_expr('end').to_dict(), 'meaning_link': 'machine_x11 = end'},
            {'name': 'i', 'type': 'lvar "zesuLoopIndex" Z', 'role': 'derived'}]
        source = {'source_index': 0, 'proposed_state': state.to_dict(),
            'relation_condition_projection': {'condition_indices': [0], 'conditions': [state.conditions[0].to_dict()]},
            'loop_binders': rows, 'loop_witness_plan': {'ordered_binders': [row['name'] for row in rows]},
            'checked_cursor_relations': [relation], 'retained_fold_relations': [],
            'minimal_condition_sets': [{'relation': relation, 'preheader': [0]}],
            'dropped_relation_records': [{'kind': 'open_fold'}], 'induction_checks': [{'edge': 'bound-backedge'}],
            'body_results': {'path': 'bound-results', 'sha256': 'a' * 64},
            'control_transfer_obligations': [{'status': 'OPEN'}],
            'zero_read_arm_refutation_source': {'status': 'OPEN'}, 'kernel_entailments': 'OPEN'}
        continuation = {'name': 'K', 'terminal_id': 'terminal', 'source_binding': {'level1': 'bound-exit'}}
        return seed, source, continuation

    def assemble(self, seed, source, continuation, outer=()):
        return assemble_loop_class(source, original_seed=seed,
            vocabulary={'input_sha256': 'bound', 'source_vocabulary': {'imports': []}},
            continuation=continuation, outer_names=outer)

    def test_exact_binders_endpoint_link_and_open_obligations_survive(self):
        seed, source, continuation = self.fixture();before = deepcopy(source)
        result = self.assemble(seed, source, continuation)
        self.assertEqual([row['name'] for row in result['seed'].ownership['binders']],
                         ['machine_x15', 'machine_x11', 'i'])
        self.assertIn('machine_x11 = end', result['boundary']['body'])
        self.assertIn('bv_unsigned machine_x15 < bv_unsigned machine_x11', result['boundary']['body'])
        self.assertEqual(result['seed'].state.registers['x11'], input_expr('machine_x11'))
        self.assertEqual(len(result['seed'].state.conditions), 2)
        self.assertEqual(result['class_record']['control_transfer_obligations'], [{'status': 'OPEN'}])
        self.assertEqual(result['class_record']['source_class_preserved'], source)
        self.assertEqual(result['removed_binders'][0]['binder']['name'], 'before')
        self.assertEqual(source, before)
        self.assertEqual(seed.state.registers['x11'], input_expr('end'))

    def test_wrong_endpoint_link_projection_order_and_capture_refuse(self):
        for defect in ['meaning', 'endpoint', 'projection', 'dependencies', 'order', 'capture', 'fold']:
            with self.subTest(defect=defect):
                seed, source, continuation = self.fixture();outer = ()
                if defect == 'meaning':source['loop_binders'][1]['meaning_link'] = 'machine_x11 = 0'
                elif defect == 'endpoint':source['loop_binders'][1]['source_expression'] = bits(0, 64).to_dict()
                elif defect == 'projection':source['relation_condition_projection']['conditions'] = []
                elif defect == 'dependencies':source['minimal_condition_sets'][0]['preheader'] = []
                elif defect == 'order':source['loop_witness_plan']['ordered_binders'].reverse()
                elif defect == 'capture':outer = ['machine_x15']
                elif defect == 'fold':source['retained_fold_relations'] = [{'kind': 'unproved_fold'}]
                with self.assertRaises(ValueError):self.assemble(seed, source, continuation, outer)

    def test_used_inherited_witness_is_not_silently_removed(self):
        seed, source, continuation = self.fixture()
        source['loop_binders'][1]['source_expression'] = input_expr('before').to_dict()
        source['loop_binders'][1]['meaning_link'] = 'machine_x11 = before'
        source['proposed_state']['registers']['x11'] = input_expr('before').to_dict()
        with self.assertRaisesRegex(ValueError, 'inherited loop witness'):
            self.assemble(seed, source, continuation)

    def test_unused_original_condition_is_recorded_and_cannot_strengthen_the_seed(self):
        seed, source, continuation = self.fixture()
        condition = operation('=', input_expr('unbound_system_word'), bits(0, 64)).to_dict()
        source['proposed_state']['conditions'].append(condition)
        result = self.assemble(seed, source, continuation)
        self.assertNotIn(condition, [value.to_dict() for value in result['seed'].state.conditions])
        refused = [row for row in result['seed'].join_refusals if row['kind'] == 'loop_condition_projection']
        self.assertEqual(refused[0]['condition'], condition)
        self.assertEqual(refused[0]['condition_index'], 1)

    def test_owned_write_and_full_fraction_survive_once(self):
        seed, source, continuation = self.fixture()
        component = parse_source_ownership('(32)%Z ↦ₘ{DfracOwn 1}∗ bytes',
            provenance={'source': 'bound-array'})['components'][0]
        component.update(id='memory', scope=[[]])
        seed.ownership['components'].insert(-1, component)
        seed.ownership['tree']['body']['children'].insert(-1, {'kind': 'component', 'id': 'memory'})
        seed.resources.append(OwnedBytes('memory', bits(32, 64), '32', input_expr('bytes', None),
            4, True, 'DfracOwn 1', component, {'source': 'bound-array'}, 8))
        seed.facts.append({'fact_id': 'permission', 'kind': 'permission', 'status': 'supplied',
            'terms': {'resource_id': 'memory', 'fraction': 'DfracOwn 1'}, 'origin': {'source': 'bound-array'}})
        write = MemoryWrite(bits(32, 64), bits(9, 8), 1, True, ownership_id='memory')
        source['proposed_state']['writes'] = [write.to_dict()]
        result = self.assemble(seed, source, continuation)
        array = next(row for row in result['boundary']['components'] if row['id'] == 'memory')
        self.assertIn('↦ₘ{DfracOwn 1}∗', array['source'])
        self.assertIn('9%Z', array['source'])
        self.assertEqual(result['boundary']['write_accounting']['processed_writes'], 1)
        self.assertEqual(seed.resources[0].byte_array, input_expr('bytes', None))
        self.assertEqual(len(result['seed'].state.writes), 1)
        self.assertEqual(result['class_record']['inherited_source_facts'], seed.facts)

    def test_trace_conditioned_fact_cannot_bypass_projection(self):
        condition = operation('=', input_expr('unbound_system_word'), bits(0, 64)).to_dict()
        for dependency in ([condition], False, []):
            with self.subTest(dependency=dependency):
                seed, source, continuation = self.fixture()
                seed.facts.append({'fact_id': 'conditional', 'kind': 'bounds', 'status': 'derived-by-pass',
                    'terms': {'resource_id': 'memory'}, 'origin': {'source_conditions': dependency}})
                with self.assertRaisesRegex(ValueError, 'trace-condition justification'):
                    self.assemble(seed, source, continuation)

    def test_retained_fold_uses_the_supplied_renderer_and_preserves_pending_metadata(self):
        seed, source, continuation = self.fixture()
        relation = {'kind': 'byte_window_fold', 'register': 'x15'}
        source['retained_fold_relations'] = [relation]
        source['minimal_condition_sets'].append({'relation': relation, 'preheader': [0]})
        source['pending_fold_candidates'] = [{'status': 'OPEN', 'assertion': 'pending_only'}]
        calls = []
        def renderer(value, *, scope):
            calls.append((value, scope))
            return {'term': 'bv_unsigned machine_x15 = 0', 'imports': ['ZesuSsz.Automation.ByteWindowFold']}
        result = assemble_loop_class(source, original_seed=seed,
            vocabulary={'input_sha256': 'bound', 'source_vocabulary': {'imports': []}},
            continuation=continuation, fold_renderer=renderer)
        self.assertEqual(calls[0][1]['machine_x15'], 'bv 64')
        self.assertEqual(calls[0][1]['i'], 'lvar "zesuLoopIndex" Z')
        self.assertIn('⌜bv_unsigned machine_x15 = 0⌝', result['boundary']['body'])
        self.assertNotIn('pending_only', result['boundary']['body'])
        self.assertEqual(result['class_record']['pending_fold_candidates'], source['pending_fold_candidates'])
        self.assertEqual(result['required_imports'], ['ZesuSsz.Automation.ByteWindowFold'])


if __name__ == '__main__':unittest.main()
