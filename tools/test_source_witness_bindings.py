import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from join_generalize import witness_plan
from source_witness_bindings import (digest, derive_source_plan, record_trace_origins,
                                     render_source_mapping, derive_runtime_source_plan)
from symbolic_state import Expr, SymbolicState


class SourceWitnessBindingsTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source = self.root / 'Source.v'
        self.target = self.root / 'Target.v'
        body = '(∃ (x y : bv 64) (i : lvar "index" Z), "x11" ↦ᵣ RVal_Bits x ∗ "x12" ↦ᵣ RVal_Bits y ∗ (base) ↦ₘ∗ payload ∗ ⌜0 <= i⌝ ∗ True)%I.'
        self.source.write_text('Definition source_owner : iProp Sigma := ' + body)
        self.target.write_text('Definition target_owner : iProp Sigma := ' + body)
        self.owner = {'block_status': 'completed', 'tree': {'kind': 'exists', 'binders': [
            {'name': 'x', 'type': 'bv 64'}, {'name': 'y', 'type': 'bv 64'},
            {'name': 'i', 'type': 'lvar "index" Z'}]}, 'body': body,
            'components': [{'id': 'left', 'source': '"x11" ↦ᵣ RVal_Bits x'}, {'id': 'right', 'source': '"x12" ↦ᵣ RVal_Bits y'}, {'id': 'array', 'source': '(base) ↦ₘ∗ payload'}]}
        self.row = {'resource_boundary': self.owner, 'state': {'reports': []}}
        self.report = self.root / 'FORWARD.json'
        self.write_report()
        self.context = {'report': self.bind(self.report), 'pointer': '/boundaries/0/alternatives/0',
                        'owner_sha256': digest(self.owner),
                        'source_declaration': dict(self.bind(self.source), declaration='source_owner'),
                        'target_declaration': dict(self.bind(self.target), declaration='target_owner')}
        self.slots = [{'name': 'x', 'type': 'bv 64'}, {'name': 'y', 'type': 'bv 64'},
                      {'name': 'i', 'type': 'lvar "index" Z'}]
        self.bindings = {s['name']: {'kind': 'source_existential', 'pointer': '/declared/' + str(i)}
                         for i, s in enumerate(self.slots)}

    def bind(self, path):
        return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

    def write_report(self):
        self.report.write_text(json.dumps({'schema': 'block-forward-states.v1',
                                          'boundaries': [{'alternatives': [self.row]}]}))

    def plan(self, bindings=None, context=None):
        return witness_plan(self.slots, register_bindings={},
                            source_bindings=self.bindings if bindings is None else bindings,
                            source_context=self.context if context is None else context)

    def test_tagged_source_index_and_order(self):
        plan = self.plan()
        self.assertEqual(plan['ordered_binders'], ['x', 'y', 'i'])
        self.assertEqual(plan['ordered_witnesses'][2]['type'], 'lvar "index" Z')
        self.assertEqual(plan['input_family'], 'authenticated_source')

    def owned_register_fixture(self):
        self.target.write_text(self.target.read_text().replace('(x y : bv 64)', '(next y : bv 64)')
                               .replace('RVal_Bits x', 'RVal_Bits next'))
        self.context['target_declaration'].update(self.bind(self.target))
        self.row['state']['registers'] = {'x11': {'op': 'input', 'width': 64, 'value': 'x'},
                                          'x12': {'op': 'input', 'width': 64, 'value': 'y'}}
        self.write_report()
        self.context['report'] = self.bind(self.report)

    def test_direct_owned_register_uses_existing_constructor(self):
        self.owned_register_fixture()
        plan = derive_source_plan(self.context, allow_owned_registers=True)
        output = render_source_mapping(plan, name='source_mapping',
                                       target_application='target_owner', source_application='source_owner',
                                       parameters=[], source_parameters=[])
        self.assertIn('(ZesuSourceRegister 64%N "x11")', output['source'])
        self.assertEqual(plan['ordered_binders'], ['next', 'y', 'i'])

    def test_owned_register_refuses_wrong_owner_width_and_alias(self):
        self.owned_register_fixture()
        for mutation, message in [
                (lambda text: text.replace('"x11"', '"x10"'), 'does not own'),
                (lambda text: text.replace('RVal_Bits y', 'RVal_Bits next'), 'multiple register owners')]:
            with self.subTest(message=message):
                original = self.target.read_text()
                self.target.write_text(mutation(original))
                self.context['target_declaration'].update(self.bind(self.target))
                with self.assertRaisesRegex(ValueError, message):
                    derive_source_plan(self.context, allow_owned_registers=True)
                self.target.write_text(original)
                self.context['target_declaration'].update(self.bind(self.target))
        self.row['state']['registers']['x11']['width'] = 32
        self.write_report()
        self.context['report'] = self.bind(self.report)
        with self.assertRaisesRegex(ValueError, 'different source width'):
            derive_source_plan(self.context, allow_owned_registers=True)

    def test_source_array_refuses_changed_fraction_address_or_payload(self):
        for source, message in [('(base) ↦ₘ{DfracOwn 2}∗ payload', 'unsupported fraction'),
                                ('(other) ↦ₘ∗ payload', 'address or payload'),
                                ('(base) ↦ₘ∗ other', 'address or payload')]:
            with self.subTest(source=source):
                self.owner['components'][2]['source'] = source
                self.context['owner_sha256'] = digest(self.owner)
                self.write_report()
                self.context['report'] = self.bind(self.report)
                with self.assertRaisesRegex(ValueError, message):
                    self.plan()

    def runtime_fixture(self, kind='bv 64'):
        self.target.write_text(self.target.read_text().replace('(∃ ', '(∃ (unused : ' + kind + ') ', 1))
        self.context['target_declaration'].update(self.bind(self.target))
        authority = self.root / 'AUTHORITY.json'
        authority.write_text(json.dumps({'schema': 'zesu.witness-runtime-slot-correction.v1'}))
        return self.bind(authority)

    def runtime_output(self, plan):
        return render_source_mapping(plan, name='source_mapping', target_application='target_owner',
                                     source_application='source_owner', parameters=[], source_parameters=[])

    def test_full_runtime_keeps_vacuous_slot_and_used_source_identity(self):
        authority = self.runtime_fixture()
        phase = derive_source_plan(self.context)
        plan = derive_runtime_source_plan(self.context, authority)
        output = self.runtime_output(plan)
        self.assertEqual(plan['ordered_binders'], ['unused', 'x', 'y', 'i'])
        self.assertEqual(plan['ordered_witnesses'][1:], phase['ordered_witnesses'])
        self.assertTrue(plan['runtime_slots']['slots'][0]['vacuous'])
        self.assertEqual(output['internal_order'][-1]['name'], 'unused')
        self.assertIn('(BV 64%N 0%Z)', output['source'])
        self.assertIn('let \'(captured_slot_0,', output['source'])
        self.assertIn('ZesuWitnessProfileSlot "unused"', output['source'])
        self.assertEqual(len(output['profile_binding']['source_slots']), 4)
        self.assertEqual(len(output['profile_binding']['data_slots']), 4)
        self.assertEqual(phase['ordered_binders'], ['x', 'y', 'i'])

    def test_full_runtime_refuses_changed_vacuity_or_used_fixed_value(self):
        plan = derive_runtime_source_plan(self.context, self.runtime_fixture())
        changed = copy.deepcopy(plan)
        changed['runtime_slots']['slots'][1]['vacuous'] = True
        with self.assertRaisesRegex(ValueError, 'vacuous flags changed'):
            self.runtime_output(changed)
        changed = copy.deepcopy(plan)
        changed['ordered_witnesses'][1].update(vacuous=True, fixed_inhabitant='BV 64%N 0%Z')
        with self.assertRaisesRegex(ValueError, 'used slot cannot'):
            self.runtime_output(changed)
        changed = copy.deepcopy(plan)
        changed['ordered_witnesses'][0]['fixed_inhabitant'] = 'BV 64%N 1%Z'
        with self.assertRaisesRegex(ValueError, 'changed its authorized'):
            self.runtime_output(changed)

    def test_full_runtime_refuses_unbound_authority_and_unsupported_inhabitant(self):
        authority = self.runtime_fixture('Z')
        with self.assertRaisesRegex(ValueError, 'no authorized fixed'):
            derive_runtime_source_plan(self.context, authority)
        Path(authority['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'bound witness source changed'):
            derive_runtime_source_plan(self.context, authority)

    def test_actual_emitter_uses_only_source_keys(self):
        plan = derive_source_plan(self.context)
        output = render_source_mapping(plan, name='source_mapping',
                                       target_application='target_owner', source_application='source_owner',
                                       parameters=[], source_parameters=[])
        self.assertIn('ZesuEntrySourceWitnessMapping', output['source'])
        self.assertIn('ZesuSourceOwnerSlot (lvar "index" Z)', output['source'])
        self.assertEqual([s['name'] for s in output['internal_order']], ['i', 'y', 'x'])
        self.assertFalse(output['proof_scripts_emitted'])

    def test_profile_metadata_binds_source_names_and_mapping_fragment(self):
        output = render_source_mapping(derive_source_plan(self.context), name='source_mapping',
                                       target_application='target_owner', source_application='source_owner',
                                       parameters=[], source_parameters=[])
        binding = output['profile_binding']
        self.assertEqual(binding['declaration'], self.context['target_declaration'])
        self.assertEqual(binding['source_slots'], binding['data_slots'])
        self.assertTrue(binding['names_from_authenticated_source'])
        self.assertFalse(binding['runtime_names_recovered'])
        fragment = output['source'].split('#[export] Instance source_mapping_source_profile', 1)[0]
        self.assertEqual(hashlib.sha256(fragment.encode()).hexdigest(), binding['mapping_fragment_sha256'])
        self.assertIn('ZesuEntryWitnessSourceProfile', output['source'])
        self.assertIn('ZesuEntryWitnessDataProfile', output['source'])
        self.assertIn('ZesuWitnessProfileSlot "x" (bv 64)', output['source'])

    def test_mapping_module_renders_direct_profile_import(self):
        header = ('Require Import ZesuSsz.Automation.All.\n'
                  'Require Import ZesuSsz.Automation.SourceWitnessInputs.\n')
        args = dict(name='source_mapping', target_application='target_owner',
                    source_application='source_owner', parameters=[], source_parameters=[])
        output = render_source_mapping(derive_source_plan(self.context), module_header=header, **args)
        required = 'Require Import ZesuSsz.Automation.EntryWitnessProfile.\n'
        self.assertEqual(output['module_source'].count(required), 1)
        self.assertTrue(output['module_source'].startswith(header + required))
        self.assertTrue(output['module_source'].endswith(output['source']))
        repeated = render_source_mapping(derive_source_plan(self.context),
                    module_header=header + required, **args)
        self.assertEqual(output['module_source'], repeated['module_source'])
        with self.assertRaisesRegex(ValueError, 'source-reader import'):
            render_source_mapping(derive_source_plan(self.context), module_header='', **args)

    def test_target_wrapper_preserves_telescope_and_continuation(self):
        self.target.write_text(self.target.read_text() + '\nDefinition target_key (K : iProp Sigma) : iProp Sigma := (target_owner ∗ K)%I.\n')
        self.context['target_declaration'].update(self.bind(self.target))
        self.context['target_key_declaration'] = dict(self.bind(self.target), declaration='target_key')
        output = render_source_mapping(derive_source_plan(self.context), name='source_mapping',
                                       target_application='target_key K', source_application='source_owner',
                                       parameters=[{'name': 'K', 'type': 'iProp Sigma'}], source_parameters=[])
        self.assertIn('ZesuEntrySourceWitnessMapping (target_key K)', output['source'])

    def test_changed_target_wrapper_refuses(self):
        self.target.write_text(self.target.read_text() + '\nDefinition target_key (K : iProp Sigma) : iProp Sigma := (target_owner ∗ True)%I.\n')
        self.context['target_declaration'].update(self.bind(self.target))
        self.context['target_key_declaration'] = dict(self.bind(self.target), declaration='target_key')
        with self.assertRaisesRegex(ValueError, 'exact telescope and continuation'):
            render_source_mapping(derive_source_plan(self.context), name='source_mapping',
                                  target_application='target_key K', source_application='source_owner',
                                  parameters=[{'name': 'K', 'type': 'iProp Sigma'}], source_parameters=[])

    def test_conflicting_shared_application_values_refuse(self):
        for path, name in [(self.source, 'source_owner'), (self.target, 'target_owner')]:
            path.write_text(path.read_text().replace('Definition ' + name + ' :',
                                                    'Definition ' + name + ' (argument : Z) :'))
        self.context['source_declaration'].update(self.bind(self.source))
        self.context['target_declaration'].update(self.bind(self.target))
        plan = derive_source_plan(self.context)
        with self.assertRaisesRegex(ValueError, 'conflicting types or values'):
            render_source_mapping(plan, name='source_mapping',
                                  target_application='target_owner right',
                                  source_application='source_owner left',
                                  parameters=[{'name': 'right', 'type': 'Z'}],
                                  source_parameters=[{'name': 'left', 'type': 'Z'}])

    def test_emitter_refuses_reordered_same_type_plan(self):
        plan = self.plan()
        plan['ordered_witnesses'][0], plan['ordered_witnesses'][1] = plan['ordered_witnesses'][1], plan['ordered_witnesses'][0]
        with self.assertRaisesRegex(ValueError, 'witness order, count, or types'):
            render_source_mapping(plan, name='source_mapping',
                                  target_application='target_owner', source_application='source_owner',
                                  parameters=[], source_parameters=[])

    def test_same_typed_swap_refuses(self):
        b = copy.deepcopy(self.bindings)
        b['x'], b['y'] = b['y'], b['x']
        with self.assertRaisesRegex(ValueError, 'different name or type'):
            self.plan(b)

    def test_target_only_provenance_refuses(self):
        c = copy.deepcopy(self.context)
        c['source_declaration'] = c['target_declaration']
        with self.assertRaisesRegex(ValueError, 'target declaration'):
            self.plan(context=c)

    def test_missing_slot_refuses(self):
        b = copy.deepcopy(self.bindings)
        del b['i']
        with self.assertRaisesRegex(ValueError, 'missing or extra'):
            self.plan(b)

    def test_extra_slot_refuses(self):
        b = dict(self.bindings, extra=self.bindings['x'])
        with self.assertRaisesRegex(ValueError, 'extra witness'):
            self.plan(b)

    def test_changed_array_owner_refuses(self):
        self.owner['components'][2]['source'] = 'other ↦ₘ∗ other_payload'
        self.write_report()
        self.context['report'] = self.bind(self.report)
        with self.assertRaisesRegex(ValueError, 'complete source owner differs'):
            self.plan()

    def test_wrong_register_value_refuses_even_with_updated_hashes(self):
        self.owner['components'][0]['source'] = '"x11" ↦ᵣ RVal_Bits y'
        self.write_report()
        self.context['report'] = self.bind(self.report)
        self.context['owner_sha256'] = digest(self.owner)
        with self.assertRaisesRegex(ValueError, 'register value differs'):
            self.plan()

    def test_wrong_array_assertion_refuses_even_with_updated_hash(self):
        self.source.write_text(self.source.read_text().replace('↦ₘ∗ payload', '↦ₘ∗ other_payload'))
        self.context['source_declaration'].update(self.bind(self.source))
        with self.assertRaisesRegex(ValueError, 'array address or payload differs'):
            self.plan()

    def test_pure_source_assertion_refuses(self):
        self.source.write_text('Definition source_owner : Prop := True.')
        self.context['source_declaration'].update(self.bind(self.source))
        with self.assertRaisesRegex(ValueError, 'assertion definition'):
            self.plan()

    def test_changed_source_type_refuses(self):
        self.source.write_text(self.source.read_text().replace('x y : bv 64', 'x y : bv 8'))
        self.context['source_declaration'].update(self.bind(self.source))
        with self.assertRaisesRegex(ValueError, 'different name or type'):
            self.plan()

    def test_changed_bound_bytes_refuse(self):
        self.report.write_text(self.report.read_text() + ' ')
        with self.assertRaisesRegex(ValueError, 'source changed'):
            self.plan()

    def test_target_pure_equality_is_not_a_source(self):
        b = copy.deepcopy(self.bindings)
        b['i'] = {'kind': 'target_equality', 'pointer': '/goal/equality'}
        with self.assertRaisesRegex(ValueError, 'source existential or source declaration'):
            self.plan(b)

    def test_conflicting_reader_refuses(self):
        with self.assertRaisesRegex(ValueError, 'competing source readers'):
            witness_plan(self.slots, register_bindings={'x': ('x11', 64)},
                         source_bindings=self.bindings, source_context=self.context)

    def test_old_register_plan_is_unchanged(self):
        plan = witness_plan([self.slots[0]], register_bindings={'x': ('x11', 64)})
        self.assertEqual(plan['schema'], 'source.join-witness-plan.v1')
        self.assertEqual(plan['input']['left'], {'kind': 'register', 'register': 'x11', 'width': 64})

    def test_trace_origin_records_location_without_changing_facts(self):
        source = '(trace (declare-const v4 (_ BitVec 64)))'
        state = SymbolicState(registers={'PC': Expr('bits', width=64, value=16)}, trace_count=7,
                              conditions=[Expr('=', (Expr('local', width=64, value='7:v4'),
                                                      Expr('bits', width=64, value=0)))])
        facts = list(state.conditions)
        record_trace_origins(state, source, instruction_pc=16, seed_pc=0)
        self.assertEqual(state.conditions, facts)
        origin = state.reports[0]
        self.assertEqual(origin['instruction_pc'], '0x10')
        self.assertEqual(origin['symbol']['value'], '7:v4')
        self.assertEqual(origin['declaration'], 'v4')

    def test_trace_declaration_ambiguity_refuses(self):
        state = SymbolicState(trace_count=7, conditions=[Expr('local', width=64, value='7:v4')])
        with self.assertRaisesRegex(ValueError, 'ambiguous declaration'):
            record_trace_origins(state, '(trace (declare-const v4 (_ BitVec 64)) (declare-const v4 (_ BitVec 64)))',
                                 instruction_pc=16, seed_pc=0)


if __name__ == '__main__':
    unittest.main()
