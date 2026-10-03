"""Tests for strict whole-block generation and inferred resource ownership."""

import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS / "det"))
import call_sites
import gen_boundary
import gen_coverage
import infer_boundary
import gen_segment

spec = importlib.util.spec_from_file_location("block_gen", TOOLS / "block/gen_block.py")
gen_block = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen_block)

TMP = 'reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers)'
BINDERS = '`{!islaG Sigma} `{!threadG} (tail : spec)'
ATOMS = ['reg_col zesu_ram_sys_regs', TMP, 'spec_trace tail']


class StrictCalls(unittest.TestCase):
    def test_unknown_target_is_an_error_only_in_strict_mode(self):
        with patch.object(call_sites, "call_sites", return_value={1: (3, "unknown")}), \
             patch.object(call_sites, "contracts", return_value={}):
            self.assertEqual(call_sites.premises(0, 2)[2], [3])
            with self.assertRaisesRegex(ValueError, "0x3"):
                call_sites.premises(0, 2, strict=True)

    def test_unresolved_indirect_call_is_an_error(self):
        with patch.object(call_sites, "call_sites", return_value={1: (None, "a0")}), \
             patch.object(call_sites, "contracts", return_value={}):
            with self.assertRaisesRegex(ValueError, "at 0x1"):
                call_sites.premises(0, 2, strict=True)
            self.assertEqual(call_sites.premises(2, 3, strict=True), ([], [], []))

    def test_table_covers_every_pinned_write_success_call(self):
        _lines, _modules, unknown = call_sites.premises(0x14d30, 0x15a14, strict=True)
        self.assertEqual(unknown, [])
        self.assertIn(0x15cb0, call_sites.contracts())
        self.assertIn(0x15ce4, call_sites.contracts())


class StatePartition(unittest.TestCase):
    def test_captured_register_numeral_uses_recorded_width(self):
        state = dict(binders=BINDERS, spatial=ATOMS +
                     ['"x12" ↦ᵣ RVal_Bits 720%bv'])
        default = gen_block.state_source(0x14d7c, state)
        self.assertIn('RVal_Bits 720%bv', default)
        state['register_bit_widths'] = {'x12': 64}
        self.assertIn('RVal_Bits (BV 64 720)',
                      gen_block.state_source(0x14d7c, state))

    def test_captured_scope_metadata_is_opt_in(self):
        state = dict(binders=BINDERS, spatial=ATOMS)
        default = gen_block.state_source(0x14d7c, state)
        self.assertNotIn('Local Open Scope', default)
        self.assertEqual(default, gen_block.state_source(
            0x14d7c, dict(state, open_scopes=[])))
        self.assertIn('Local Open Scope Z_scope.', gen_block.state_source(
            0x14d7c, dict(state, open_scopes=['Z_scope'])))

    def test_captured_unsigned_numeral_keeps_its_bit_width(self):
        atom = 'bv_unsigned 96709 ↦ₘ∗ bytes'
        self.assertEqual(gen_boundary.normalize_bitvector_addresses(
            [atom], {'96709': 64}), ['bv_unsigned (BV 64 96709) ↦ₘ∗ bytes'])
        with self.assertRaisesRegex(ValueError, 'missing captured bit width'):
            gen_boundary.normalize_bitvector_addresses([atom], {})
        self.assertEqual(infer_boundary.bitvector_address_widths(
            'BOUNDARY-ADDRESS-WIDTH 96709%bv : 64%N'), {'96709': 64})

    def test_captured_array_numerals_keep_their_bit_width(self):
        atom = 'bv_unsigned pointer ↦ₘ∗ [90%bv; 83%bv; byte]'
        self.assertEqual(gen_boundary.normalize_memory_literals(
            [atom], {'(bv_unsigned pointer)': 8}),
            ['bv_unsigned pointer ↦ₘ∗ [(BV 8 90); (BV 8 83); byte]'])
        with self.assertRaisesRegex(ValueError, 'missing captured bit width'):
            gen_boundary.normalize_memory_literals([atom], {})
        self.assertIn('@mem_mapsto_array', infer_boundary.PRINT_MEMORY_WIDTHS)

    def test_captured_memory_numeral_keeps_its_bit_width(self):
        atom = '(base - 8) ↦ₘ 89232%bv'
        self.assertEqual(gen_boundary.normalize_memory_literals(
            [atom, 'base ↦ₘ word'], {'(base - 8)': 64}),
            ['(base - 8) ↦ₘ (BV 64 89232)', 'base ↦ₘ word'])
        with self.assertRaisesRegex(ValueError, 'missing captured bit width'):
            gen_boundary.normalize_memory_literals([atom], {})
        event = 'spec_trace (scons (SWriteMem (BV 64 (port + 16)) 8%bv) tail)'
        self.assertEqual(gen_boundary.normalize_memory_literals(
            [event], {'(BV 64 (port + 16))': 64}),
            ['spec_trace (scons (SWriteMem (BV 64 (port + 16)) (BV 64 8)) tail)'])

    def test_captured_slice_and_return_wand_restore_the_array(self):
        borrowed = '(base + 16) ↦ₘ∗ take 20 (drop 16 bytes)'
        whole = 'base ↦ₘ∗ bytes'
        self.assertEqual(gen_boundary.normalize_lent_arrays(
            [borrowed, borrowed + ' -∗ ' + whole, 'spec_trace tail']),
            ['spec_trace tail', whole])
        unmatched = [borrowed + ' -∗ ' + whole, '(base + 17) ↦ₘ∗ bytes']
        self.assertEqual(gen_boundary.normalize_lent_arrays(unmatched), unmatched)

    def test_recorded_set_sort_is_a_value_witness(self):
        source = gen_boundary.boundary_source(
            'State', BINDERS, [('returned', 'bv 64')],
            ATOMS + ['"x10" ↦ᵣ RVal_Bits returned'], seal=False,
            call_resources=True, sorts={'returned': 'Set'})
        self.assertIn('∃ returned : bv 64', source)

    def test_captured_successor_preserves_persistent_mmio_permission(self):
        permission = 'mmio_range (machineOutputAddress defaultMap) 16'
        state = dict(binders=BINDERS, coq=[], spatial=list(ATOMS),
                     persistent=[permission, permission], post_state=True,
                     seal_memory=False)
        source = gen_block.state_source(0x1562c, state)
        self.assertEqual(source.count(permission), 1)

    def test_context_capture_preserves_persistent_mmio_permission(self):
        permission = 'mmio_range (machineOutputAddress defaultMap) 16'
        context = ('Sigma : gFunctors\n' + '============================\n'
                   + '_ : ' + permission + '\n'
                   + '--------------------------------------\u25a1\n'
                   + '\n'.join('_ : ' + atom for atom in ATOMS) + '\n'
                   + '--------------------------------------\u2217\nPOST')
        source = gen_block.state_source(0x1562c, dict(
            binders=BINDERS, context=context, seal_memory=False))
        self.assertIn(permission, source)

    def test_binary_successor_count_bounds_keep_resources(self):
        state = dict(binders=BINDERS, coq=[('remaining', 'nat'),
                     ('Hcount', '(S remaining < 2 ^ 64)%nat')],
                     spatial=list(ATOMS), local_sorts={'remaining': 'Type',
                     'Hcount': 'Prop'}, seal_memory=False)
        source = gen_block.state_source(0x15754, state)
        self.assertIn('(Z.of_nat remaining + 1 < 2 ^ 64)%Z', source)
        self.assertNotIn('(S remaining < 2 ^ 64)%nat', source)
        self.assertIn('reg_col zesu_ram_sys_regs', source)
        self.assertIn('spec_trace tail', source)


    def test_binary_count_normalization_preserves_other_facts(self):
        facts = {'(S remaining < 2 ^ 64)%nat':
                 '(Z.of_nat remaining + 1 < 2 ^ 64)%Z',
                 '(S count <= 3 ^ 32)%nat':
                 '(Z.of_nat count + 1 <= 3 ^ 32)%Z',
                 '(count < 2 ^ 64)%Z': '(count < 2 ^ 64)%Z',
                 'length bytes = 32 * (processed + S remaining)':
                 'length bytes = 32 * (processed + S remaining)'}
        for source, expected in facts.items():
            with self.subTest(source=source):
                self.assertEqual(gen_boundary.normalize_binary_count_bounds(source), expected)


    def test_return_point_discards_legacy_register_values(self):
        state = {"binders": BINDERS, "spatial": [ATOMS[0], ATOMS[2]] +
                 [f'"{register}" ↦ᵣ RVal_Bits (BV 64 8)'
                  for register in ("x1", "x5", "x10", "x11")],
                 "return_point": True}
        with patch.object(gen_boundary, "boundary_source", return_value="") as boundary:
            gen_block.state_source(0x150fc, state)
        spatial = boundary.call_args.args[3]
        for register in ("x1", "x5", "x10", "x11"):
            self.assertTrue(any(f'KindReg "{register}", BitsShape 64' in atom
                                for atom in spatial))
            self.assertFalse(any(atom.startswith(f'"{register}" ↦ᵣ')
                                 for atom in spatial))

    def test_flat_capture_opens_named_memory_without_array_splits(self):
        source = ('Definition sampleMemory := memory.\n'
                  'Definition sampleTailWords := words.\n'
                  'Definition samplePayload := payload.\n')
        with tempfile.TemporaryDirectory() as directory:
            tactics = gen_boundary.flat_state_tactics(source, Path(directory))
        self.assertIn('unfold sampleMemory', tactics)
        self.assertIn('unfold sampleTailWords', tactics)
        self.assertNotIn('unfold samplePayload', tactics)
        self.assertNotIn('array_split', tactics)

    def test_stack_expression_keeps_existing_binders(self):
        state = {'binders': BINDERS, 'stack_size': 16,
                 'stack_pointer': '(entry_sp - 2000)'}
        atoms = ['"x2" ↦ᵣ RVal_Bits (bv_to_bvn (entry_sp - 2000))']
        result = gen_block.add_stack_resources(state, atoms)
        self.assertEqual(state['binders'], BINDERS)
        self.assertIn('bv_unsigned (entry_sp - 2000)', ' '.join(result))
        with self.assertRaisesRegex(ValueError, 'exact x2 ownership'):
            gen_block.add_stack_resources(state, [])

    def test_partitioned_temporaries_keep_captured_conditional_ownership(self):
        atoms = ['reg_col zesu_ram_sys_regs', '"x5" ↦ᵣ value',
                 'reg_col match saved with | [] => [] | _ => ['
                 + '; '.join(f'(KindReg "{r}", BitsShape 64)'
                             for r in gen_boundary.TMP_REGISTERS[1:]) + '] end']
        original = list(atoms)
        gen_boundary.require_call_resources(atoms)
        self.assertEqual(atoms, original)
        with self.assertRaisesRegex(ValueError, 'temporary register collection'):
            gen_boundary.require_call_resources(atoms[:-1])

    def test_stack_boundary_replaces_unknown_x2_and_keeps_arguments(self):
        state = {'binders': BINDERS, 'stack_size': 16}
        atoms = ['reg_col [(KindReg "x1", BitsShape 64); (KindReg "x2", BitsShape 64)]']
        result = gen_block.add_stack_resources(state, atoms)
        self.assertEqual(state['arguments'], 'tail sp')
        self.assertIn('(sp : bv 64)', state['binders'])
        self.assertNotIn('(KindReg "x2", BitsShape 64)', ' '.join(result))
        self.assertIn('"x2" ↦ᵣ RVal_Bits (bv_to_bvn sp)', result)
        self.assertIn('⌜(bv_unsigned sp `mod` 16 = 0)%Z⌝', result)
        self.assertEqual(gen_block.add_stack_resources(state, result), result)
        self.assertIn('(bv_unsigned sp - 16) ↦ₘ? 16', result)

    def test_supplied_successor_removes_only_its_legacy_continuation(self):
        state = {'binders': BINDERS, 'spatial': ATOMS +
                 ['instr_pre 86280 P', 'instr_pre 89360 P'],
                 'supplied_successors': ['0x15108']}
        with patch.object(gen_boundary, 'boundary_source', return_value='') as boundary:
            gen_block.state_source(0x150fc, state)
        self.assertNotIn('instr_pre 86280 P', boundary.call_args.args[3])
        self.assertIn('instr_pre 89360 P', boundary.call_args.args[3])

    def test_post_state_removes_unused_anonymous_facts_and_keeps_memory_open(self):
        state = {'binders': BINDERS, 'spatial': ATOMS + ['"x8" ↦ᵣ RVal_Bits b'],
                 'coq': [('b', 'bv 64'), ('H0', 'bv_unsigned b < 100')],
                 'post_state': True, 'seal_memory': False}
        with patch.object(gen_boundary, 'boundary_source', return_value='') as boundary:
            gen_block.state_source(0x15108, state)
        self.assertEqual(boundary.call_args.args[2], [])
        self.assertFalse(boundary.call_args.kwargs['seal'])

    def test_full_register_file_preserves_exact_values_and_does_not_duplicate(self):
        atoms = ATOMS + ['"x2" ↦ᵣ RVal_Bits sp', '"x12" ↦ᵣ RVal_Bits argument']
        completed = gen_boundary.complete_register_file(atoms)
        self.assertIn('"x12" ↦ᵣ RVal_Bits argument', completed)
        self.assertNotIn('(KindReg "x12", BitsShape 64)', completed[-1])
        self.assertNotIn('(KindReg "x5", BitsShape 64)', completed[-1])
        self.assertEqual(gen_boundary.complete_register_file(completed), completed)

    def test_conditional_register_collection_is_preserved(self):
        atom = 'reg_col (match saved with [] => [(KindReg "x8", BitsShape 64)] | _ => [] end)'
        self.assertIn(atom, gen_boundary.complete_register_file([atom]))

    def test_exact_register_ownership_removes_only_bits_duplicate(self):
        atoms = ['"x5" ↦ᵣ RVal_Bits value',
                 'reg_col [(KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64)]']
        result = gen_boundary.deduplicate_register_shapes(atoms)
        self.assertEqual(result, [atoms[0], 'reg_col [(KindReg "x6", BitsShape 64)]'])

    def test_captured_literal_temporaries_keep_their_shapes(self):
        atom = 'reg_col [' + '; '.join('(KindReg "' + r + '", BitsShape 64)'
                                      for r in gen_boundary.TMP_REGISTERS) + ']'
        normalized = gen_boundary.normalize_temporaries([atom])
        self.assertIn('tmp_registers', normalized[0])
        self.assertEqual(normalized[0].count('BitsShape 64'), 7)

    def test_direct_shape_ownership_removes_its_temporary_duplicate(self):
        direct = '"x5" ↦ᵣ: λ r : valu, ⌜valu_has_shape r (BitsShape 64)⌝'
        collection = 'reg_col (zip_with (fun r shape => (KindReg r, shape)) '
        collection += 'tmp_registers [' + '; '.join(['BitsShape 64'] * 7) + '])'
        result = gen_boundary.deduplicate_register_shapes([direct, collection])
        self.assertEqual(result[0], direct)
        self.assertNotIn('KindReg "x5"', result[1])
        self.assertIn('KindReg "x6"', result[1])
        gen_boundary.complete_register_file(result)

    def test_printed_byte_list_fixpoint_keeps_its_explicit_arguments(self):
        atom = '(fix byteListItemResources (address : Z) := body (address + 16)) Sigma islaG0 base items'
        self.assertEqual(gen_boundary.fold_printed_resources([atom]),
                         ['(@byteListItemResources) Sigma islaG0 base items'])
        with self.assertRaisesRegex(ValueError, 'unbalanced'):
            gen_boundary.fold_printed_resources(['(fix byteListItemResources (address : Z) := body'])

    def test_successor_precision_keeps_known_stack_pointer(self):
        atoms = ['"x2" ↦ᵣ RVal_Bits sp',
                 'reg_col [(KindReg "x8", ExactShape (RVal_Bits value))]']
        self.assertEqual(gen_boundary.preserve_register_precision(atoms, {"x8"}),
                         [atoms[0], 'reg_col [(KindReg "x8", BitsShape 64)]'])

    def test_named_successor_state_uses_its_recorded_name(self):
        state = {"name": "Successor_15118_1513c", "binders": BINDERS, "arguments": "tail"}
        self.assertEqual(gen_block.state_application(0x1513c, state),
                         "Successor_15118_1513c tail")

    def test_post_state_anonymous_register_uses_bits_shape(self):
        atoms = ['reg_col [(KindReg "x8", ExactShape (RVal_Bits b))]',
                 '"x10" ↦ᵣ RVal_Bits returned']
        result = gen_boundary.post_state_register_precision(
            atoms, BINDERS, [('b', 'bv 64'), ('returned', 'bv 64')])
        self.assertIn('reg_col [(KindReg "x8", BitsShape 64)]', result)
        self.assertIn('reg_col [(KindReg "x10", BitsShape 64)]', result)

    def test_post_state_keeps_parameters_and_memory_related_values(self):
        atoms = ['"x10" ↦ᵣ RVal_Bits value', '"x11" ↦ᵣ RVal_Bits loaded',
                 '(bv_unsigned sp + 8) ↦ₘ loaded']
        result = gen_boundary.post_state_register_precision(
            atoms, BINDERS + ' (value : bv 64)',
            [('value', 'bv 64'), ('loaded', 'bv 64')])
        self.assertEqual(result, atoms)

    def test_internal_handoffs_do_not_close_the_block(self):
        atoms = ['instr_pre (88368 + 4) P', 'instr_pre 88380 Q', 'instr_pre 88384 R']
        self.assertEqual(gen_boundary.strip_internal_handoffs(atoms, 88368, 88384), [atoms[2]])

    def test_duplicate_register_ownership_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate register.*x5"):
            gen_boundary.complete_register_file(ATOMS + ['"x5" ↦ᵣ RVal_Bits value'])

    def test_recorded_witness_replaces_memory_address_and_dependent_facts(self):
        source = gen_boundary.boundary_source(
            "State", BINDERS + ' (sp : bv 64)',
            [('pointer', 'bv 64'), ('H0', 'bv_unsigned pointer = bv_unsigned sp + 1000')],
            ['bv_unsigned pointer ↦ₘ? 32'], seal=False,
            sorts={'pointer': 'Type', 'H0': 'Prop'}, witnesses={'pointer': '(sp + 1000)%bv'})
        self.assertNotIn('∃ pointer', source)
        self.assertIn('bv_unsigned ((sp + 1000)%bv) ↦ₘ? 32', source)
        self.assertNotIn('bv_unsigned pointer', source)

    def test_seal_contains_only_memory_and_declares_coverage(self):
        atoms = ATOMS + ['(base + 8) ↦ₘ∗ take 8 bytes', 'base ↦ₘ word',
                         '(base + 16) ↦ₘ? 8', '⌜base >= 0⌝']
        source = gen_boundary.boundary_source(
            "State", BINDERS + ' (base : Z) (word : bv 64) (bytes : list (bv 8))',
            [], atoms, seal=True, call_resources=True)
        memory, state = source.split("Definition State\n", 1)
        self.assertNotIn("reg_col", memory)
        self.assertNotIn("spec_trace", memory)
        self.assertNotIn("⌜base", memory)
        self.assertIn("ZesuSealed", memory)
        self.assertIn("1 * Z.of_nat (length (take 8 bytes))", memory)
        self.assertNotIn("base ↦ₘ word", memory)
        self.assertIn("base ↦ₘ word", state)
        self.assertIn("((base + 16), ((base + 16)) + (8))", memory)
        self.assertIn("Global Opaque StateMemory.", memory)
        self.assertNotIn("Global Opaque State.", source)
        self.assertIn("reg_col zesu_ram_sys_regs", state)
        self.assertIn(TMP, state)
        self.assertIn("spec_trace tail", state)

    def test_nested_conjunction_splits_without_splitting_array_notation(self):
        atoms = gen_boundary.spatial_atoms(
            '(reg_col zesu_ram_sys_regs ∗ (base + 8) ↦ₘ∗ bytes ∗ spec_trace tail)%I')
        self.assertEqual(atoms, ['reg_col zesu_ram_sys_regs', '(base + 8) ↦ₘ∗ bytes',
                                 'spec_trace tail'])

    def test_register_lambda_keeps_its_scope(self):
        atom = '"x10" ↦ᵣ: fun r10 => ⌜r10 = RVal_Bits value⌝ ∗ spec_trace tail'
        self.assertEqual(gen_boundary.spatial_atoms(atom), [atom])
        source = gen_boundary.boundary_source("State", BINDERS, [], [atom], seal=True)
        self.assertNotIn("Global Opaque", source)

    def test_exact_temporaries_keep_their_values(self):
        atoms = [f'"{register}" ↦ᵣ RVal_Bits v{index}'
                 for index, register in enumerate(gen_boundary.TMP_REGISTERS)]
        normalized = gen_boundary.normalize_temporaries(atoms + ['spec_trace tail'])
        self.assertEqual(len(normalized), 2)
        for index in range(7):
            self.assertIn(f"(RVal_Bits v{index})", normalized[0])
        self.assertIn("ExactShape (RVal_Bits v0)", normalized[0])
        self.assertIn("tmp_registers", normalized[0])

    def test_incomplete_temporaries_are_not_invented(self):
        atoms = ['reg_col zesu_ram_sys_regs', '"x5" ↦ᵣ RVal_Bits value']
        with self.assertRaisesRegex(ValueError, "temporary register collection"):
            gen_boundary.boundary_source("State", BINDERS, [], atoms,
                                         seal=False, call_resources=True)

    def test_shaped_temporaries_keep_their_predicate(self):
        atoms = [f'"{register}" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝ ∗ True'
                 for register in gen_boundary.TMP_REGISTERS]
        normalized = gen_boundary.normalize_temporaries(atoms)
        self.assertEqual(len(normalized), 1)
        self.assertEqual(normalized[0].count('(BitsShape 64)'), 7)
        self.assertIn('tmp_registers', normalized[0])

    def test_missing_system_collection_is_not_invented(self):
        with self.assertRaisesRegex(ValueError, "zesu_ram_sys_regs"):
            gen_boundary.boundary_source("State", BINDERS, [], [TMP],
                                         seal=False, call_resources=True)

    def test_unknown_word_width_stays_open(self):
        self.assertIsNone(gen_coverage.memory_range('base ↦ₘ unknown', {}))
        source = gen_boundary.boundary_source("State", BINDERS, [],
                                              ATOMS + ['base ↦ₘ unknown'], seal=True)
        self.assertNotIn("Global Opaque", source)

    def test_folded_resource_package_requires_an_inference_step(self):
        with self.assertRaisesRegex(ValueError, 'folded or unsupported spatial resource'):
            gen_boundary.boundary_source('State', BINDERS, [],
                                         ATOMS + ['OldWholeStateFrame witness'], False,
                                         call_resources=True)
        source = gen_boundary.boundary_source('State', BINDERS + ' (P : iProp Sigma)', [],
                                              ATOMS + ['P'], False, call_resources=True)
        self.assertIn('(P) ∗', source)

    def test_state_does_not_extend_a_register_lambda_to_the_next_atom(self):
        atom = '"x10" ↦ᵣ: fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝ ∗ True'
        source = gen_boundary.boundary_source('State', BINDERS, [],
                                              [atom, 'spec_trace outer_tail'], False)
        self.assertIn('(' + atom + ') ∗\n   (spec_trace outer_tail)', source)

    def test_array_coverage_uses_element_width(self):
        byte_range = gen_coverage.memory_range('base ↦ₘ∗ bytes', {'bytes': 'list (bv 8)'})
        word_range = gen_coverage.memory_range('base ↦ₘ∗ words', {'words': 'list (bv 64)'})
        self.assertIn('1 * Z.of_nat (length (bytes))', byte_range)
        self.assertIn('8 * Z.of_nat (length (words))', word_range)
        self.assertIsNone(gen_coverage.memory_range('base ↦ₘ∗ words', {}))
        self.assertIsNone(gen_coverage.memory_range('Folded (base ↦ₘ∗ words)',
                                                    {'words': 'list (bv 64)'}))
        self.assertIsNone(gen_coverage.memory_range('base ↦ₘ∗ map cast8 words',
                                                    {'words': 'list (bv 64)'}))
        typed = gen_coverage.memory_range('base ↦ₘ∗ map cast8 words',
                                         {'map cast8 words': 'list (bv 8)'})
        self.assertIn('1 * Z.of_nat', typed)

    def test_unknown_local_sort_is_a_residual(self):
        with self.assertRaisesRegex(ValueError, 'missing Coq sort for local Hvalid'):
            gen_boundary.boundary_source('State', BINDERS, [('Hvalid', 'CustomFact value')],
                                         ATOMS, False, call_resources=True)
        source = gen_boundary.boundary_source(
            'State', BINDERS, [('Hvalid', 'CustomFact value')], ATOMS, False,
            call_resources=True, sorts={'Hvalid': 'Prop'})
        self.assertIn('⌜CustomFact value⌝', source)

    def test_proposition_variable_stays_quantified(self):
        source = gen_boundary.boundary_source('State', BINDERS,
                                              [('P', 'Prop'), ('HP', 'P')], ATOMS, False,
                                              call_resources=True,
                                              sorts={'P': 'Type', 'HP': 'Prop'})
        self.assertIn('∃ P : Prop,', source)
        self.assertIn('⌜P⌝', source)
        self.assertNotIn('⌜Prop⌝', source)

    def test_pure_hypothesis_becomes_a_pure_atom(self):
        source = gen_boundary.boundary_source("State", BINDERS + ' (value : Z)',
                                              [('Hbound', '0 <= value')], ATOMS, False)
        self.assertIn('⌜0 <= value⌝', source)
        self.assertNotIn('∃ Hbound', source)


class StopInference(unittest.TestCase):
    def test_stop_record_names_stop_when_it_differs_from_original_exit(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailFieldsThirdSegment.v')
        lemma = 'write_success_exact_tail_fields_third_segment'
        with patch.object(infer_boundary, 'probe_source', return_value='source'), \
             patch.object(infer_boundary, 'run', return_value=(
                 infer_boundary.probes.BEGIN + '\n' + infer_boundary.REACHED + '\n'
                 + '1 goal\n=====\nTrue\n' + infer_boundary.probes.END)):
            record = infer_boundary.infer(module, lemma, '0x30', Path('build'),
                                           [], 30, stop='0x20', after_return=True)
        self.assertEqual(record['outcome'], 'reached')
        self.assertEqual(record['exit'], '0x30')
        self.assertEqual(record['state_entry'], '0x20')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'states.jsonl'
            path.write_text(json.dumps(record) + '\n')
            self.assertEqual(set(gen_block.read_states(path)), {0x20})

    def test_local_sorts_preserve_values_and_arbitrary_proof_facts(self):
        text = (infer_boundary.SORT_BEGIN + '\n'
                'BOUNDARY-LOCAL-SORT Hvalid : Prop\n'
                'BOUNDARY-LOCAL-SORT n : Set\n'
                'BOUNDARY-LOCAL-SORT P : Type@{u}\n'
                + infer_boundary.SORT_END)
        self.assertEqual(infer_boundary.local_sorts(text),
                         {'Hvalid': 'Prop', 'n': 'Type', 'P': 'Type'})
        self.assertEqual(infer_boundary.goal_record(text)[1]['local_sorts'],
                         {'Hvalid': 'Prop', 'n': 'Type', 'P': 'Type'})

    def test_stop_keeps_the_entry_after_a_single_line_exit_premise(self):
        statement = ['Lemma test ' + BINDERS + ' :',
                     '  instr_body 0x20 exit -∗', '  instr_body 0x10 entry.']
        stopped = infer_boundary.stop_statement(statement, "0x20")
        self.assertIn('  instr_body 0x10 entry.', stopped)
        self.assertIn('  instr_pre 0x20 BLK_STOP_20 -∗', stopped)
        self.assertIn('(BLK_STOP_20 : iProp Sigma)', stopped[0])

    def test_spec_stop_records_after_return_rules(self):
        record = {'name': 'test', 'entry': '0x14d30', 'exit': '0x14d34',
                  'imports': ['ZesuSsz.Automation.All'], 'binders': BINDERS, 'spec': 'True'}
        source = infer_boundary.spec_source(record, stop='0x14d34', after_return=True)
        self.assertIn('instr_pre 0x14d34 BLK_STOP_14d34 -∗', source)
        self.assertIn('Switches.ReturnBundle', source)
        self.assertLess(source.index('zesu_enter_return_bundle_if_enabled.'),
                        source.index(infer_boundary.RAW_BEGIN))
        self.assertLess(source.index('zesu_enter_return_wand_if_enabled.'),
                        source.index(infer_boundary.RAW_BEGIN))


class BlockGeneration(unittest.TestCase):
    def test_unreachable_successor_uses_false_without_a_state_import(self):
        states = {0x14d30: {'binders': BINDERS, 'spatial': ATOMS},
                  0x14d34: {'outcome': 'unreachable-successor'}}
        block = {'start': 0x14d30, 'end': 0x14d34,
                 'successors': ['0x14d34']}
        with patch.object(call_sites, 'call_sites', return_value={}):
            source, _ = gen_block.generate(block, states)
        self.assertIn('instr_pre 0x14d34\n    (False)', source)
        self.assertNotIn('States.State_14d34', source)

    def test_dune_launch_removes_credentials(self):
        with patch.dict(os.environ, {'ARISTOTLE_API_KEY': 'test-a',
                                     'OPEN_ROUTER_API_KEY': 'test-b',
                                     'PROVER_API_KEY': 'test-c'}), \
             patch.object(gen_segment.subprocess, 'run') as build:
            build.return_value.returncode = 0
            build.return_value.stdout = build.return_value.stderr = ''
            gen_segment._build_staged(Path('Block_10.v'), Path('build'), 30, jobs=32)
            environment = build.call_args.kwargs['env']
            for key in ('ARISTOTLE_API_KEY', 'OPEN_ROUTER_API_KEY', 'PROVER_API_KEY'):
                self.assertNotIn(key, environment)
                self.assertIn(key, os.environ)
        command = build.call_args.args[0]
        self.assertEqual(command[command.index('--build-dir') + 1], str(Path('build').resolve()))

    def test_two_successors_keep_guarded_premises_and_one_block_proof(self):
        states = {value: {'binders': BINDERS, 'spatial': ATOMS}
                  for value in (0x14d30, 0x14d34, 0x14d38)}
        block = {'start': 0x14d30, 'end': 0x14d34, 'successors': ['0x14d34', '0x14d38']}
        with patch.object(call_sites, 'call_sites', return_value={}):
            source, name = gen_block.generate(block, states)
        self.assertTrue(source.startswith('Require Import ZesuSsz.Automation.All.'))
        self.assertIn('Automation.Sets.call', source)
        self.assertIn('instr_pre 0x14d34', source)
        self.assertIn('instr_pre 0x14d38', source)
        self.assertEqual(source.count('Proof. zesu_block. Qed.'), 1)
        self.assertEqual(name, 'block_14d30')

    def test_missing_successor_is_a_residual(self):
        with self.assertRaisesRegex(ValueError, 'missing inferred states: 0x14d34'):
            gen_block.generate({'start': 0x14d30, 'end': 0x14d34, 'successors': ['0x14d34']},
                               {0x14d30: {'binders': BINDERS, 'spatial': ATOMS}})

    def test_probe_context_belongs_to_exit_address(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'states.jsonl'
            path.write_text(json.dumps({'entry': '0x10', 'exit': '0x20', 'context': 'context'}) + '\n')
            self.assertEqual(set(gen_block.read_states(path)), {0x20})

    def test_single_inferred_json_record_does_not_need_original_entry(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'states.json'
            path.write_text(json.dumps({'state_entry': '0x20', 'exit': '0x30',
                                        'context': 'context'}))
            self.assertEqual(set(gen_block.read_states(path)), {0x20})

    def test_failed_compile_restores_existing_files_and_removes_new_files(self):
        self._compile_result(False, True, False)

    def test_preview_compile_does_not_promote_closed_block(self):
        self._compile_result(True, False, False)

    def test_only_successful_compile_promotes(self):
        self._compile_result(True, True, True)

    def _compile_result(self, compiled, promote, retained):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state, block = root / 'State_10.v', root / 'Block_10.v'
            state.write_text('new state')
            block.write_text('new block')
            generated = root / 'Generated'
            existing = generated / 'States' / state.name
            existing.parent.mkdir(parents=True)
            existing.write_text('previous state')
            with patch.object(gen_block, 'GENERATED', generated), \
                 patch.object(gen_block.gen_segment, '_build_staged',
                              return_value={'compiled': compiled}) as build:
                result = gen_block.compile_module(block, [state], root / 'build', 30, promote)
            self.assertEqual(result['promoted'], retained)
            self.assertEqual(existing.read_text(), 'new state' if retained else 'previous state')
            self.assertEqual((generated / 'Blocks' / block.name).exists(), retained)
            self.assertEqual(build.call_args.kwargs['jobs'], 32)


if __name__ == '__main__':
    unittest.main()


class ExtraLeaders(unittest.TestCase):
    def test_split_preserves_instructions_and_final_successors(self):
        block = {"start": 0x15754, "end": 0x157d4, "successors": ["0x15800"],
                 "instructions": [{"pc": pc} for pc in range(0x15754, 0x157d4, 4)]}
        parts = gen_block.split_blocks([block], {0x157d0})
        self.assertEqual(parts[0]["end"], 0x157d0)
        self.assertEqual(parts[0]["successors"], ["0x157d0"])
        self.assertEqual(parts[1]["successors"], block["successors"])
        self.assertEqual([i for part in parts for i in part["instructions"]],
                         block["instructions"])
        with self.assertRaisesRegex(ValueError, "instruction boundary"):
            gen_block.split_blocks([block], {0x157cf})


class SuccessorPruning(unittest.TestCase):
    def test_unused_pure_locals_are_removed(self):
        coq = [("kept", "bv 64"), ("unused", "bv 64"),
               ("Hkept", "bv_unsigned kept < 1024"),
               ("Hunused", "Z.land (bv_unsigned unused) 131072 = 0")]
        sorts = {name: ("Prop" if name.startswith("H") else "Type")
                 for name, _ in coq}
        spatial = ['"x8" ↦ᵣ RVal_Bits kept',
                   '⌜Z.land (bv_unsigned unused) 131072 = 0⌝']
        emitted, atoms = gen_boundary.prune_unowned_capture_locals(
            coq, spatial, BINDERS, sorts, True)
        self.assertEqual(emitted, [coq[0], coq[2]])
        self.assertEqual(atoms, [spatial[0]])
        self.assertEqual(len(coq), 4)  # The raw capture is unchanged.

    def test_owned_payload_provenance_is_preserved(self):
        coq = [("words", "list (bv 64)"), ("bytes", "list (bv 8)"),
               ("Hpacking", "words = u64s_of_bytes 16 bytes")]
        sorts = {"words": "Type", "bytes": "Type", "Hpacking": "Prop"}
        atoms = ["base ↦ₘ∗ words", "⌜words = u64s_of_bytes 16 bytes⌝"]
        self.assertEqual(gen_boundary.prune_unowned_capture_locals(
            coq, atoms, BINDERS, sorts, True), (coq, atoms))

    def test_dependent_value_type_is_preserved(self):
        coq = [("width", "N"), ("word", "bv width"), ("unused", "nat")]
        sorts = {name: "Type" for name, _ in coq}
        retained, _ = gen_boundary.prune_unowned_capture_locals(
            coq, ['"x8" ↦ᵣ RVal_Bits word'], BINDERS, sorts, True)
        self.assertEqual(retained, coq[:2])
