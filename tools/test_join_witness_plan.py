"""Derive source witnesses through Register/Pair inputs without target inversion."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from forward_witnesses import forward_witness_data
from witness_data import resolved_witness_data


def binding(path):return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def spine(items):
    result = {'kind': 'unit'}
    for item in reversed(items):result = {'kind': 'pair', 'left': item, 'right': result}
    return result


class JoinWitnessPlanTests(unittest.TestCase):
    def fixture(self, root, derived_first=False):
        owner = root / 'Owner.v'
        owner.write_text('Definition owner (base : Z) (cursor limit : bv 64%N) : iProp Sigma :=\n'
                         '  "r1" ↦ᵣ RVal_Bits cursor ∗ "r2" ↦ᵣ RVal_Bits limit.\n')
        slots = ([('i', 'lvar "zesuLoopIndex" Z'), ('cursor', 'bv 64%N'), ('limit', 'bv 64%N')]
                 if derived_first else [('cursor', 'bv 64%N'), ('limit', 'bv 64%N'), ('i', 'lvar "zesuLoopIndex" Z')])
        target = ('Definition target (base : Z) : iProp Sigma :=\n'
                  ' let K : iProp Sigma := (∃ outcome : Z, ⌜outcome = base⌝)%I in\n'
                  ' ((∃ ' + ' '.join('(' + n + ' : ' + t + ')' for n, t in slots) + ',\n'
                  ' "r1" ↦ᵣ RVal_Bits cursor ∗ "r2" ↦ᵣ RVal_Bits limit ∗ ⌜0 <= i⌝) ∗ K)%I.')
        expressions = {'cursor': {'op': 'input', 'width': 64, 'value': 'cursor'},
                       'limit': {'op': 'input', 'width': 64, 'value': 'limit'},
                       'i': {'op': 'input', 'value': '(bv_unsigned cursor - base)%Z'}}
        witnesses = [{'binder': name, 'expression': expressions[name],
                      **({'derived_from': ['r1']} if name == 'i' else {})} for name, _ in slots]
        plan = {'schema': 'source.join-witness-plan.v1', 'ordered_binders': [name for name, _ in slots],
                'ordered_witnesses': witnesses, 'input': spine([
                    {'kind': 'register', 'register': 'r1', 'width': 64},
                    {'kind': 'register', 'register': 'r2', 'width': 64}]), 'data': spine(witnesses)}
        row = {'parameters': [{'name': 'base', 'type': 'Z'}, {'name': 'cursor', 'type': 'bv 64%N'},
                              {'name': 'limit', 'type': 'bv 64%N'}], 'existentials': [], 'lets': [],
               'resources': [{'kind': 'register', 'name': 'r1', 'value': 'RVal_Bits cursor'},
                             {'kind': 'register', 'name': 'r2', 'value': 'RVal_Bits limit'}],
               'execution_facts': [], 'join_witness_plan': plan}
        path = root / 'Forward.json';path.write_text(json.dumps({'definitions': [row]}))
        source = {**binding(owner), 'declaration': 'owner'}
        forward = {'name': 'joinData', 'report': binding(path), 'pointer': '/definitions/0',
                   'source_assertion': source, 'declaration_sources': [], 'resource_templates': [source]}
        return target, forward, path

    def produce(self, root, target, forward):
        result = forward_witness_data(forward, target, 'target', [{'name': 'base', 'type': 'Z'}], root / 'values.v')
        data = resolved_witness_data(target, 'target', result['data'], source_texts=result['source_texts'])
        return result, data

    def test_source_register_expression_goes_to_pending_without_new_input_constructor(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);target, forward, _ = self.fixture(root)
            result, data = self.produce(root, target, forward)
            self.assertIn('source_words : (bv 64%N * (bv 64%N * unit)%type)%type', result['prefix'])
            self.assertIn('bv_unsigned (fst source_words) - base', result['prefix'])
            self.assertEqual(data['registers'], [('r1', 64), ('r2', 64)])
            self.assertEqual([slot['name'] for slot in data['declaration_order']], ['cursor', 'limit', 'i'])
            self.assertIn('ZesuWitnessPair', data['input'])
            self.assertNotIn('Proof.', result['prefix'] + data['source'])
            changed, again = self.produce(root, target.replace('0 <= i', 'i = 999'), forward)
            self.assertEqual(result['prefix'], changed['prefix'])
            self.assertEqual(data['source'], again['source'])

    def test_derived_slot_can_precede_the_registers_it_observes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);target, forward, _ = self.fixture(root, derived_first=True)
            result, data = self.produce(root, target, forward)
            self.assertEqual([slot['name'] for slot in data['declaration_order']], ['i', 'cursor', 'limit'])
            self.assertEqual(data['registers'], [('r1', 64), ('r2', 64)])
            self.assertIn('bv_unsigned (fst source_words)', data['source'])

    def test_literal_width_with_or_without_N_scope_has_the_same_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory);target, forward, _ = self.fixture(root)
            _, explicit = self.produce(root, target, forward)
            _, implicit = self.produce(root, target.replace('bv 64%N', 'bv 64'), forward)
            self.assertEqual(explicit['registers'], implicit['registers'])
            self.assertEqual(explicit['input'], implicit['input'])
            for bad in ['bv 64%Z', 'bv width', 'word64']:
                with self.subTest(kind=bad), self.assertRaises(ValueError):
                    self.produce(root, target.replace('bv 64%N', bad), forward)

    def test_wrong_order_inputs_constants_and_source_scope_refuse(self):
        for defect in ['order', 'data', 'input_order', 'constructor', 'width', 'literal', 'source', 'command', 'local']:
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                root = Path(directory);target, forward, path = self.fixture(root)
                document = json.loads(path.read_text());row = document['definitions'][0];plan = row['join_witness_plan']
                derived = plan['ordered_witnesses'][-1]
                if defect == 'order':plan['ordered_binders'].reverse()
                elif defect == 'data':plan['data']['left'] = deepcopy(derived)
                elif defect == 'input_order':plan['input']['left']['register'] = 'r2'
                elif defect == 'constructor':plan['input']['left'] = {'kind': 'memory', 'width': 64, 'register': 'r1'}
                elif defect == 'width':plan['input']['left']['width'] = 32
                elif defect == 'literal':derived['expression']['value'] = '0%Z'
                elif defect == 'source':derived['derived_from'] = ['r2']
                elif defect == 'command':derived['expression']['value'] = 'bv_unsigned cursor. Axiom bad : Z.'
                elif defect == 'local':
                    row['lets'] = [{'name': 'uncaptured'}]
                    derived['expression']['value'] = '(bv_unsigned cursor - uncaptured)%Z'
                if defect in ['literal', 'source', 'command', 'local']:
                    plan['data']['right']['right']['left'] = deepcopy(derived)
                path.write_text(json.dumps(document));forward['report'] = binding(path)
                with self.assertRaises(ValueError):self.produce(root, target, forward)


if __name__ == '__main__':unittest.main()
