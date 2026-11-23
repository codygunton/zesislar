"""Public seed binding preserves unknown values and source ownership."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
from resource_seed import (load_public_seed, load_scalar_constants, seed_owned_resources,
                           source_bv_expression, source_z_expression)
from symbolic_state import Expr, bits, operation


ORIGIN = {'path': 'public_source.v', 'sha256': 'source_fixture'}
VOCABULARY = {'rows': [{'kind': 'owned_byte_array', 'source_bindings': []},
                       {'kind': 'uninitialized_stack_span', 'source_bindings': []},
                       {'kind': 'permission_fraction', 'source_bindings': []}]}


def public_seed():
    return {'_input_sha256': 'fixture', 'source_bindings': [ORIGIN],
            'assertion_tree': {'kind': 'sep', 'left': {'kind': 'exists',
                'binders': [{'name': 'initial', 'type': 'bv 64',
                             'expression': Expr('unknown_input', width=64, value='entry.initial').to_dict()}],
                'components': [
                    {'id': 'collection', 'kind': 'reg_col', 'coq': 'reg_col selected_map'},
                    {'id': 'pointer', 'kind': 'register', 'register': 'x2', 'width': 64,
                     'value_coq': 'Z_to_bv 64 stack_pointer', 'symbolic_witness': None},
                    {'id': 'register', 'kind': 'register', 'register': 'x3', 'width': 64,
                     'value_coq': 'initial', 'symbolic_witness': 'initial'},
                    {'id': 'array', 'kind': 'byte_array', 'original_component': 'output ↦ₘ∗ output_bytes',
                     'original_address_z': 'output', 'byte_array_expr': {'op': 'input', 'value': 'output_bytes'},
                     'element_bits': 8, 'length_original_coq': 'length (output_bytes)'},
                    {'id': 'frame', 'kind': 'uninitialized_memory',
                     'original_component': '(stack_pointer - frame_size) ↦ₘ? frame_size',
                     'original_address_z': 'stack_pointer - frame_size', 'length_original_coq': 'frame_size'},
                    {'id': 'domain', 'kind': 'pure', 'coq': 'public_domain arguments',
                     'well_formed_facts': ['(List.length (output_bytes) = 8)%nat']}]},
                'right': {'id': 'caller', 'kind': 'opaque_caller_continuation', 'coq': 'instr_pre return_address post'}}}


class ResourceSeedTests(unittest.TestCase):
    def test_source_arithmetic_links_register_and_owned_stack_addresses(self):
        constants = {'frame_size': {'value': 16, 'origin': ORIGIN}}
        register = source_bv_expression('(Z_to_bv 64 stack_pointer)', constants)
        memory = source_z_expression('(stack_pointer - frame_size)', constants)
        self.assertEqual(memory, operation('bvsub', register, bits(16, 64)))
        self.assertEqual(source_z_expression('(-1)%Z', constants), bits(-1, 64))

    def test_bound_seed_retains_three_resource_kinds_and_the_caller_scope(self):
        seed = seed_owned_resources(public_seed(), entry_pc=16, vocabulary=VOCABULARY,
                                    constants={'frame_size': {'value': 16, 'origin': ORIGIN}})
        self.assertEqual(seed.state.registers['PC'], bits(16, 64))
        self.assertEqual(seed.state.registers['x3'], Expr('unknown_input', width=64, value='entry.initial'))
        self.assertEqual([resource.id for resource in seed.resources], ['array', 'frame'])
        self.assertEqual([resource.length for resource in seed.resources], [8, 16])
        self.assertTrue(seed.state.memory[1].uninitialized)
        self.assertFalse(seed.state.memory[1].bytes)
        self.assertEqual(seed.ownership['tree']['right'], {'kind': 'component', 'id': 'caller'})
        self.assertEqual({fact['kind'] for fact in seed.facts}, {'permission', 'nonwrap'})

    def test_missing_stack_length_remains_symbolic(self):
        seed = seed_owned_resources(public_seed(), entry_pc=16, vocabulary=VOCABULARY)
        self.assertEqual(seed.resources[1].length.op, 'input')
        self.assertEqual(seed.reports[0]['kind'], 'symbolic_owned_length')

    def test_incorrect_array_type_does_not_become_byte_ownership(self):
        source = public_seed()
        source['assertion_tree']['left']['components'][3]['element_bits'] = 16
        with self.assertRaisesRegex(ValueError, 'eight-bit element'):
            seed_owned_resources(source, entry_pc=16, vocabulary=VOCABULARY)

    def test_scalar_constant_reader_checks_source_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'public.v'
            path.write_text('Definition frame_size : Z := 16.\nDefinition other : nat := 7.\n')
            binding = {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            constants = load_scalar_constants([binding], ['frame_size'])
            self.assertEqual(constants['frame_size']['value'], 16)
            self.assertNotIn('other', constants)
            path.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'constant source changed'):
                load_scalar_constants([binding], ['frame_size'])

    def test_public_seed_loader_checks_each_bound_source(self):
        with tempfile.TemporaryDirectory() as directory:
            path, packet = Path(directory)/'public.v', Path(directory)/'seed.json'
            path.write_text('public source')
            data = {'schema': 'h1-public-entry-seed.v1', 'source_bindings': [
                    {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}]}
            packet.write_text(json.dumps(data))
            digest = hashlib.sha256(packet.read_bytes()).hexdigest()
            self.assertEqual(load_public_seed(packet, digest)['_input_sha256'], digest)
            path.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'public seed source changed'):
                load_public_seed(packet, digest)


if __name__ == '__main__':
    unittest.main()
