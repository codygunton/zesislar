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

remaining_spec = importlib.util.spec_from_file_location(
    'remaining_states', TOOLS.parent / 'ZesuSsz/Evidence/det/remaining/run_states.py')
remaining_states = importlib.util.module_from_spec(remaining_spec)
remaining_spec.loader.exec_module(remaining_states)

TMP = 'reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers)'
BINDERS = '`{!islaG Sigma} `{!threadG} (tail : spec)'
ATOMS = ['reg_col zesu_ram_sys_regs', TMP, 'spec_trace tail']


class RemainingStates(unittest.TestCase):
    def test_successor_record_uses_stop_and_preserves_entry_and_exit(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessPrologueChunk14d30.v')
        row = {'leader': '0x14d30', 'stop': '0x14d80', 'exit': '0x14d90',
               'lemma': 'write_success_prologue_chunk_14d30',
               'parameter_types': {'tag': 'bv 64'}}
        output = 'BOUNDARY-REACHED BLK_STOP_14d80\n1 goal\n====\nBLK_STOP_14d80\n'
        record = remaining_states.from_mcp(row, {'seconds': 1, 'result': {
            'success': True, 'feedback': [['Show.', output]]}}, module)
        self.assertEqual(record['state_entry'], '0x14d80')
        self.assertEqual(record['probe_entry'], '0x14d30')
        self.assertEqual(record['exit'], '0x14d90')
        self.assertEqual(record['parameter_types']['tag'], 'bv 64')

    def test_another_goals_stop_marker_does_not_supply_a_state(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessPrologueChunk14d30.v')
        row = {'leader': '0x14d30', 'lemma': 'write_success_prologue_chunk_14d30'}
        output = 'BOUNDARY-REACHED BLK_STOP_14d30\n1 goal\n====\nBLK_STOP_20\n'
        record = remaining_states.from_mcp(row, {'seconds': 1, 'result': {
            'success': True, 'feedback': [['Show.', output]]}}, module)
        self.assertEqual(record['outcome'], 'error')
        self.assertNotIn('state_entry', record)

    def test_successor_probe_does_not_measure_reassigned_predecessors(self):
        manifest = [{'leader': '0x14e14', 'outcome': 'missing-entry',
                     'predecessors': ['0x14d80']}]
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(infer_boundary, 'probe_source') as probe:
            rows = remaining_states.prepare_successors(manifest, Path(directory))
        probe.assert_not_called()
        self.assertEqual(rows[0]['outcome'], 'external-predecessor')

    def test_successor_probe_requires_an_actual_predecessor_state(self):
        manifest = [{'leader': '0x14e88', 'outcome': 'residual'},
                    {'leader': '0x14e94', 'outcome': 'missing-entry',
                     'predecessors': ['0x14e88']}]
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(infer_boundary, 'probe_source') as probe:
            rows = remaining_states.prepare_successors(manifest, Path(directory))
        probe.assert_not_called()
        self.assertEqual(rows[0]['outcome'], 'missing-predecessor-state')

    def test_reassigned_blocks_are_excluded(self):
        reassigned = remaining_states.shared.LEADERS
        blocks = [{'start': hex(leader)} for leader in reassigned] + [
            {'start': '0x14d30'}, {'start': '0x15190'}, {'start': '0x159c8'}]
        self.assertEqual(remaining_states.remaining_blocks(blocks), blocks[-3:])

    def test_mcp_record_keeps_the_kernel_context_and_native_selection(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessPrologueChunk14d30.v')
        row = {'leader': '0x14d30', 'lemma': 'write_success_prologue_chunk_14d30'}
        output = ('BOUNDARY-REACHED BLK_STOP_14d30\n'
                  'BOUNDARY-ALL-GOALS-BEGIN\n1 goal\nsp : bv 64\n====\n'
                  '_ : reg_col zesu_ram_sys_regs\n---∗\nBLK_STOP_14d30\n'
                  'BOUNDARY-ALL-GOALS-END\n1 goal\nsp : bv 64\n====\n'
                  '_ : reg_col zesu_ram_sys_regs\n---∗\nBLK_STOP_14d30\n')
        record = remaining_states.from_mcp(row, {'seconds': 1, 'result': {
            'success': True, 'feedback': [['Show.', output]]}}, module)
        self.assertEqual(record['outcome'], 'reached')
        self.assertEqual(record['state_entry'], '0x14d30')
        self.assertIn('reg_col zesu_ram_sys_regs', record['context'])
        self.assertEqual(record['module'], module.name)

    def test_mcp_failure_does_not_create_a_state(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessPrologueChunk14d30.v')
        row = {'leader': '0x14d30', 'lemma': 'write_success_prologue_chunk_14d30'}
        record = remaining_states.from_mcp(row, {'seconds': 1, 'result': {
            'success': False, 'error': 'MCP memory limit'}}, module)
        self.assertEqual(record['outcome'], 'error')
        self.assertNotIn('state_entry', record)


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
    def test_strengthening_does_not_duplicate_unknown_temporary_ownership(self):
        state = {'binders': BINDERS, 'standard_call_frame': True,
                 'spatial': ['spec_trace tail', 'reg_col [(KindReg "x5", CustomShape)]']}
        with self.assertRaisesRegex(ValueError, 'unsupported collection'):
            gen_block.state_source(0x10, state)

    def test_memory_coverage_uses_integer_scope(self):
        source = gen_boundary.boundary_source(
            'State', BINDERS + ' (sp : bv 64)', [],
            ATOMS + ['(bv_unsigned sp - 48) ↦ₘ? 48'], seal=True)
        self.assertIn('((bv_unsigned sp - 48), ((bv_unsigned sp - 48)) + (48))%Z',
                      source)

    def test_recorded_instruction_address_width_is_preserved(self):
        atom = 'instr_pre (bv_unsigned 87484) True'
        state = {'binders': BINDERS, 'spatial': ATOMS + [atom],
                 'resource_values': [{'source': atom, 'value': '87484%bv',
                                      'type': '(bv 32)'}]}
        self.assertIn('@bv_unsigned 32 87484', gen_block.state_source(0x10, state))

    def test_unused_parameter_types_survive_stop_inference(self):
        state = {'binders': BINDERS + ' old_ra', 'spatial': ATOMS,
                 'parameter_types': {'old_ra': 'bv 64'}}
        self.assertIn('(old_ra : bv 64)', gen_block.state_source(0x10, state))

    def test_recorded_value_types_preserve_bitvector_widths(self):
        atom = '"x5" ↦ᵣ RVal_Bits (bv_to_bvn 8)'
        state = {'binders': BINDERS, 'standard_call_frame': True,
                 'spatial': ['reg_col zesu_ram_sys_regs', atom, 'spec_trace tail'],
                 'resource_values': [{'source': '(' + atom + ')%I',
                                      'value': '8%bv', 'type': '(bv 32)'}]}
        source = gen_block.state_source(0x10, state)
        self.assertIn('@bv_to_bvn 32 (8%bv)', source)

    def test_recorded_local_types_type_untyped_native_parameters(self):
        source = gen_boundary.boundary_source('State', BINDERS + ' sp old_ra',
            [('sp', 'bv 64'), ('old_ra', 'bv 64')], ATOMS + ['bv_unsigned sp ↦ₘ? 8'],
            seal=True, call_resources=True)
        self.assertIn('(sp : bv 64) (old_ra : bv 64)', source)

    def test_parameter_types_do_not_rewrite_dependent_binder_types(self):
        binders = '(f : forall (x : bv 64), P x) sp'
        self.assertEqual(gen_boundary.typed_parameters(
            binders, {'sp': 'bv 64', 'P': 'iProp Sigma', 'x': 'bv 32'}),
            '(f : forall (x : bv 64), P x) (sp : bv 64)')

    def test_application_keeps_untyped_native_parameters(self):
        binders = '`{!islaG Sigma} `{!threadG} sp base cursor (P : iProp Sigma)'
        self.assertEqual(gen_boundary.explicit_arguments(binders), 'sp base cursor P')

    def test_standard_frame_strengthening_is_explicit(self):
        state = {'binders': BINDERS + ' (P : iProp Sigma)',
                 'spatial': ['P', 'spec_trace tail']}
        with self.assertRaisesRegex(ValueError, 'zesu_ram_sys_regs'):
            gen_block.state_source(0x10, state)
        source = gen_block.state_source(0x10, dict(state, standard_call_frame=True))
        self.assertIn('reg_col zesu_ram_sys_regs', source)
        self.assertIn('tmp_registers', source)
        self.assertIn('P', source)
        self.assertIn('spec_trace tail', source)

    def test_standard_frame_preserves_partial_exact_ownership(self):
        atoms = ['reg_col zesu_ram_sys_regs', '"x5" ↦ᵣ RVal_Bits value',
                 '"x6" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝', 'P']
        strengthened = gen_block.with_standard_call_frame(atoms)
        self.assertEqual(strengthened.count('reg_col zesu_ram_sys_regs'), 1)
        self.assertIn('ExactShape (RVal_Bits value)', strengthened[0])
        self.assertEqual(strengthened[0].count('BitsShape 64'), 6)
        self.assertEqual(strengthened[-1], 'P')
        gen_boundary.require_call_resources(strengthened)

    def test_standard_frame_preserves_complete_collections(self):
        self.assertEqual(gen_block.with_standard_call_frame(ATOMS), ATOMS)

    def test_system_alias_does_not_duplicate_ownership(self):
        state = {'binders': BINDERS, 'standard_call_frame': True,
                 'spatial': ['reg_col zesu_instr_sys_regs', TMP, 'spec_trace tail']}
        source = gen_block.state_source(0x10, state)
        self.assertEqual(source.count('reg_col zesu_ram_sys_regs'), 1)
        self.assertNotIn('reg_col zesu_instr_sys_regs', source)

    def test_grouped_coq_locals_remain_separate_values(self):
        coq, _, _ = gen_boundary.sections('H : True\nb8, b9 : bv 64\n====\n')
        self.assertEqual(coq, [('H', 'True'), ('b8', 'bv 64'), ('b9', 'bv 64')])

    def test_context_without_persistent_separator_keeps_spatial_resources(self):
        _, persistent, spatial = gen_boundary.sections(
            'sp : bv 64\n====\n_ : reg_col zesu_ram_sys_regs\n_ : spec_trace tail')
        self.assertEqual(persistent, [])
        self.assertEqual(spatial, ['reg_col zesu_ram_sys_regs', 'spec_trace tail'])

    def test_recorded_register_reduction_preserves_ownership(self):
        registers = '; '.join(f'(KindReg "{r}", BitsShape 64)'
                              for r in gen_boundary.TMP_REGISTERS)
        state = {'binders': BINDERS,
                 'spatial': ['reg_col zesu_ram_sys_regs', 'reg_col Shapes', 'spec_trace tail'],
                 'register_collections': [{'source': 'Shapes', 'value': '[' + registers + ']'}]}
        source = gen_block.state_source(0x10, state)
        self.assertIn('tmp_registers', source)
        self.assertNotIn('reg_col Shapes', source)

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
        self.assertIn("(base, (base) + (8))", memory)
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

    def test_literal_collection_preserves_other_registers(self):
        registers = '; '.join(f'(KindReg "{r}", BitsShape 64)'
                              for r in gen_boundary.TMP_REGISTERS)
        normalized = gen_boundary.normalize_temporaries(
            ['reg_col [' + registers + '; (KindReg "x12", BitsShape 64)]'])
        self.assertIn('tmp_registers', normalized[0])
        self.assertEqual(normalized[1], 'reg_col [(KindReg "x12", BitsShape 64)]')

    def test_partial_literal_collection_does_not_add_temporaries(self):
        normalized = gen_boundary.normalize_temporaries(
            ['reg_col [(KindReg "x5", ExactShape (RVal_Bits value))]'])
        self.assertFalse(any('tmp_registers' in atom for atom in normalized))
        self.assertEqual(normalized, ['"x5" ↦ᵣ (RVal_Bits value)'])

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
    def test_copied_native_instances_use_typeclass_opacity(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactAccessListsCopyWhole.v')
        source, _entry = infer_boundary.entry_source(module, 'access_copy_whole_correct')
        for name in ('accessCopyWholeFrame', 'accessCopyWholePost', 'accessCopyWholeEntry'):
            self.assertIn(f'#[local] Typeclasses Opaque {name}.', source)

    def test_entry_snapshot_keeps_the_canonical_guarded_entry(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/'
                      'WriteSuccessExactTransactionsRecipientOutputValueContinuation.v')
        source, entry = infer_boundary.entry_source(
            module, 'transactions_recipient_output_value_continuation')
        self.assertEqual(entry, '0x15190')
        self.assertIn('transactionRecipientOutputPost sp', source)
        self.assertNotIn('instr_pre 0x15190', source)

    def test_kernel_metadata_preserves_unused_parameters_and_values(self):
        text = ('BOUNDARY-PARAMETERS-BEGIN\n1 goal\nold_ra : bv 64\n'
                '====\nTrue\nBOUNDARY-PARAMETERS-END\n'
                'BOUNDARY-VALUE-BEGIN ("x1" ↦ᵣ RVal_Bits (bv_to_bvn 8))%I '
                'BOUNDARY-VALUE-TERM 8%bv BOUNDARY-VALUE-TYPE (bv 32) '
                'BOUNDARY-VALUE-END\n')
        selected, record = infer_boundary.goal_record(text)
        self.assertNotIn('old_ra : bv 64', selected)
        self.assertEqual(record['parameter_types']['old_ra'], 'bv 64')
        self.assertEqual(record['resource_values'][0]['type'], '(bv 32)')
        self.assertEqual(record['resource_values'][0]['value'], '8%bv')

    def test_stop_probe_uses_the_generated_entry_state(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessHeaderChunk14e28.v')
        source = infer_boundary.probe_source(module, 'write_success_header_chunk_14e28',
            '0x14e38', [], stop='0x14e38',
            entry_state=('Definition StateProbe := True%I.', 'StateProbe'))
        self.assertIn('Definition StateProbe := True%I.', source)
        self.assertIn('instr_body 0x14e28 (StateProbe).', source)
        self.assertIn('□ instr_pre 0x10190 writeOutputExactCallSpec -∗', source)

    def test_stop_marker_requires_the_requested_successor(self):
        self.assertTrue(infer_boundary.reached_stop('BOUNDARY-REACHED BLK_STOP_20', '0x20'))
        self.assertFalse(infer_boundary.reached_stop('BOUNDARY-REACHED BLK_STOP_200', '0x20'))
        self.assertFalse(infer_boundary.reached_stop('No more goals.', '0x20'))

    def test_entry_snapshot_keeps_the_literal_native_predicate(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessHeaderChunk14e28.v')
        source, entry = infer_boundary.entry_source(module, 'write_success_header_chunk_14e28')
        self.assertEqual(entry, '0x14e28')
        self.assertIn('writeSuccessHeaderEventsAfterTag sp tail', source)
        self.assertNotIn('writeSuccessHeaderEventsAfter1184 sp tail', source)
        self.assertNotIn('instr_body 0x14e28', source)
        self.assertIn('try zesu_open_return_bundle "ENTRY".', source)

    def test_record_keeps_rocq_register_reductions(self):
        text = ('BOUNDARY-REGISTERS-BEGIN Shapes BOUNDARY-REGISTERS-VALUE\n'
                '[(KindReg "x5", BitsShape 64)] BOUNDARY-REGISTERS-END')
        self.assertEqual(infer_boundary.goal_record(text)[1]['register_collections'],
                         [{'source': 'Shapes', 'value': '[(KindReg "x5", BitsShape 64)]'}])

    def test_inferred_state_imports_the_constant_definitions(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessHeaderChunk14e28.v')
        self.assertIn('ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec',
                      infer_boundary.native_imports(module))

    def test_probe_replaces_legacy_body_lookup_resources(self):
        source = infer_boundary.with_standard_code([
            'Lemma test ' + BINDERS + ' :',
            'instr_body_lookup_resources Index.body_lookup -∗',
            'instr_body 0x10 True.'])
        self.assertFalse(any('body_lookup_resources' in line for line in source))
        self.assertTrue(any('instr_lookup_resources' in line for line in source))

    def test_probe_calls_cover_stop_beyond_original_handoff(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessPrologueChunk14d30.v')
        source = infer_boundary.probe_source(
            module, 'write_success_prologue_chunk_14d30', '0x14d48', [], stop='0x14d80')
        self.assertIn('□ instr_pre 0x101d4 zesuMemcpyCallSpec -∗', source)
        self.assertIn('Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.', source)
        self.assertNotIn('Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.', source)
        self.assertIn('write_success_prologue_entry sp decoded', source)
        self.assertNotIn('instr_body 0x14d48', source)

    def test_existing_call_premise_is_not_duplicated(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessHeaderChunk14e28.v')
        source = infer_boundary.probe_source(
            module, 'write_success_header_chunk_14e28', '0x14e38', [], stop='0x14e38')
        self.assertEqual(source.count('□ instr_pre 0x10190 zesuWriteOutputCallSpec -∗'), 1)
        self.assertEqual(source.count('□ instr_pre 0x10190 writeOutputExactCallSpec -∗'), 1)
        self.assertIn('instr_pre 0x10190 writeOutputExactCallSpec => iClear Hcallee', source)
        self.assertLess(source.index('□ instr_pre 0x10190 writeOutputExactCallSpec -∗'),
                        source.index('□ instr_pre 0x10190 zesuWriteOutputCallSpec -∗'))
        self.assertNotIn('Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.', source)
        self.assertIn('writeSuccessHeaderEventsAfterTag sp tail', source)

    def test_unknown_probe_callee_is_rejected(self):
        with patch.object(infer_boundary, 'call_premises',
                          side_effect=ValueError('no closed contract for: 0xabc')) as calls:
            with self.assertRaisesRegex(ValueError, '0xabc'):
                infer_boundary.with_call_premises(['instr_body 0x10 True.'], '0x20')
        calls.assert_called_once_with(0x10, 0x20, strict=True)

    def test_stop_record_names_stop_when_it_differs_from_original_exit(self):
        module = Path('ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailFieldsThirdSegment.v')
        lemma = 'write_success_exact_tail_fields_third_segment'
        with patch.object(infer_boundary, 'probe_source', return_value='source'), \
             patch.object(infer_boundary, 'run', return_value=(
                 infer_boundary.probes.BEGIN + '\n' + infer_boundary.REACHED + ' BLK_STOP_20\n'
                 + '1 goal\n=====\nBLK_STOP_20\n' + infer_boundary.probes.END)):
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
