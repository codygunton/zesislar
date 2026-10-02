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

    def test_successor_precision_keeps_known_stack_pointer(self):
        atoms = ['"x2" ↦ᵣ RVal_Bits sp',
                 'reg_col [(KindReg "x8", ExactShape (RVal_Bits value))]']
        self.assertEqual(gen_boundary.preserve_register_precision(atoms, {"x8"}),
                         [atoms[0], 'reg_col [(KindReg "x8", BitsShape 64)]'])

    def test_named_successor_state_uses_its_recorded_name(self):
        state = {"name": "Successor_15118_1513c", "binders": BINDERS, "arguments": "tail"}
        self.assertEqual(gen_block.state_application(0x1513c, state),
                         "Successor_15118_1513c tail")

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
