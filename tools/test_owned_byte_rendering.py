"""Keep symbolic byte rendering tied to its original owned array and read."""
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from forward_resources import OwnedBytes, apply_owned_writes, parse_source_ownership, render_resource_boundary
from symbolic_state import Expr, SymbolicState, bits, input_expr, operation


class OwnedByteRendering(unittest.TestCase):
    def fixture(self):
        provenance = {'source': 'bound-array'}
        ownership = parse_source_ownership('"x13" ↦ᵣ RVal_Bits previous ∗ address ↦ₘ{DfracOwn 1}∗ bytes',
                                          provenance=provenance)
        component = ownership['components'][1]
        array = input_expr('bytes', None);base = input_expr('base');address = input_expr('cursor')
        owner = OwnedBytes(component['id'], base, 'address', array, 8, True, 'DfracOwn 1',
                           component, provenance, 8)
        byte = Expr('owned_array_byte', (array, address, base), 8, 'a' * 64)
        condition = operation('bvult', address, operation('bvadd', base, bits(8, 64)))
        read = {'kind': 'owned_symbolic_byte_range', 'status': 'OPEN', 'owner': owner.id,
                'array': array.to_dict(), 'address': address.to_dict(), 'base': base.to_dict(),
                'value': byte.to_dict(), 'source': provenance,
                'source_chain': [condition.to_dict()], 'goal': 'source range obligation'}
        state = SymbolicState(registers={'x13': operation('zero_extend', byte, width=64)},
                              conditions=[condition], read_obligations=[read])
        result = apply_owned_writes([owner], [])
        return ownership, state, result

    def render(self, ownership, state, result):
        return render_resource_boundary(ownership, result, state,
            vocabulary={'input_sha256': 'bound', 'source_vocabulary': {'imports': []}})

    def test_existing_nth_term_keeps_array_fraction_and_open_range_obligation(self):
        ownership, state, result = self.fixture();before = deepcopy(state.to_dict())
        output = self.render(ownership, state, result)
        self.assertEqual(output['block_status'], 'completed')
        self.assertIn('List.nth (Z.to_nat ((bv_unsigned cursor - bv_unsigned base)%Z)) bytes',
                      output['components'][0]['source'])
        self.assertIn('↦ₘ{DfracOwn 1}∗', output['components'][1]['source'])
        self.assertEqual(output['owned_read_renderings'][0]['bounds_status'], 'OPEN')
        self.assertEqual(output['path_conditions'], before['conditions'])
        self.assertEqual(state.to_dict(), before)

    def test_missing_owner_changed_array_base_width_and_relation_refuse(self):
        for defect in ['owner', 'array', 'base', 'width', 'relation', 'provenance', 'chain']:
            with self.subTest(defect=defect):
                ownership, state, result = self.fixture();read = state.read_obligations[0]
                if defect == 'owner':read['owner'] = 'missing'
                elif defect == 'array':read['array'] = input_expr('anotherArray', None).to_dict()
                elif defect == 'base':read['base'] = input_expr('anotherBase').to_dict()
                elif defect == 'width':read['address'] = input_expr('cursor', 32).to_dict()
                elif defect == 'relation':read['value'] = bits(0, 8).to_dict()
                elif defect == 'provenance':read['source'] = {}
                else:read['source_chain'] = []
                self.assertEqual(self.render(ownership, state, result)['block_status'], 'stopped')

    def test_missing_source_record_and_uninitialized_array_refuse(self):
        for defect in ['record', 'uninitialized']:
            with self.subTest(defect=defect):
                ownership, state, result = self.fixture()
                if defect == 'record':state.read_obligations = []
                else:result.resources[0] = replace(result.resources[0], byte_array=None)
                self.assertEqual(self.render(ownership, state, result)['block_status'], 'stopped')

    def test_intervening_owned_array_write_refuses(self):
        ownership, state, result = self.fixture()
        result.transitions = [{'resource_id': result.resources[0].id}]
        output = self.render(ownership, state, result)
        self.assertEqual(output['block_status'], 'stopped')
        self.assertIn('intervening write', output['reports'][-1]['detail'])


if __name__ == '__main__':
    unittest.main()
