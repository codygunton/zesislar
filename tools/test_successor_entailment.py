"""Check successor provenance and complete debt retention without proof execution."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import asyncio
import hashlib

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from successor_entailment import (capture_evidence, debt_groups, designed_target,
                                 digest, plan_successor, successor_application,
                                 native_boundary_source, check_boundary, capture_entailment_source)
from successor_entailment import validate_import, successor_root_parameters


class SuccessorValidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        evidence = self.root / 'ZesuSsz/Evidence'
        evidence.mkdir(parents=True)
        hints = self.root / 'ZesuSsz/Compliance/FixtureHints.v'
        hints.parent.mkdir(parents=True)
        hints.write_text('(* Fixture registrations. *)\n')
        (evidence / 'fixture_function_text.json').write_text(json.dumps({
            'function': 'fixture', 'registrations': ['ZesuSsz/Compliance/FixtureHints.v']}))
        self.launch_imports = ('Require Import ZesuSsz.Compliance.FixtureHints.\n'
                               'Require Import ZesuSsz.Automation.Approved.\n')
        contract = self.root / 'Contracts' / 'Entry.v'
        contract.parent.mkdir()
        contract.write_text('Definition successor (args : Args) := resource args.\n')
        self.block = {'entry_pc': '0x20',
                      'entry_definition': 'Contracts.Entry.successor',
                      'resource_predicate': 'Contracts.Entry.successor',
                      'binders': [{'name': 'args', 'type': 'Args'}],
                      'arguments': ['args'],
                      'source_hashes': {'Contracts/Entry.v': digest(contract)}}
        source = self.root / 'Probe.v'
        source.write_text('The unchanged native source')
        source.with_suffix('.mcp.json').write_text('[]')
        goals = self.root / 'state_3.json'
        self.groups = {'goals': [{'ty': 'STOP', 'hyps': []}],
                       'stack': [[[], [{'ty': 'stack debt', 'hyps': []}]]],
                       'shelf': [{'ty': 'shelf debt', 'hyps': []}],
                       'given_up': [{'ty': 'given-up debt', 'hyps': []}]}
        goals.write_text(json.dumps(self.groups))
        self.export = {'success': True, 'checkpoint': 'recorders',
                       'scope': 'native checkpoint', 'owned_pet_pid': 123,
                       'state_id': 3, 'path': str(goals), 'sha256': digest(goals),
                       'source': str(source), 'source_sha256': digest(source),
                       'primary_capture_sha256': digest(source.with_suffix('.mcp.json'))}
        self.provenance = {'entry': '0x10', 'domain': 'unchanged'}
        self.capture = {'outcome': 'reached', 'exit': '0x20',
                        'root_provenance': self.provenance,
                        'binders': '(args : Args)', 'source_sha256': digest(source),
                        'inherited_debts': {'given_up': ['inherited debt']},
                        'pending_goals': ['pure debt'], 'shelved_goals': ['array bound']}

    def plan(self):
        return plan_successor(self.capture, self.block, self.root,
                              self.export, self.provenance, root_parameters=['args'])

    def test_design_application_keeps_order_and_declared_arguments(self):
        self.block['arguments'] = ['(domain returnAddress)', 'args']
        target = designed_target(self.block, self.root)
        self.assertEqual(target['application'],
                         'Contracts.Entry.successor ((domain returnAddress)) (args)')
        self.assertEqual(target['binders'], self.block['binders'])

    def test_valid_evidence_never_claims_closure(self):
        result = self.plan()
        self.assertFalse(result['contract_closed'])
        self.assertEqual(result['proof_status'], 'unproved')
        self.assertEqual(result['evidence']['native_debts']['groups'], self.groups)
        self.assertEqual(result['evidence']['inherited_debts'], self.capture['inherited_debts'])
        self.assertEqual(result['evidence']['pending_goals'], ['pure debt'])
        self.assertEqual(result['evidence']['shelved_goals'], ['array bound'])

    def test_unfolded_target_remains_unproved_and_preserves_native_debts(self):
        fixture = json.loads((Path(__file__).parent / 'block' / 'testdata' /
                              'unfolded_header_target.json').read_text())
        self.groups['goals'] = [{'ty': fixture['target'], 'hyps': []}]
        export_path = Path(self.export['path'])
        export_path.write_text(json.dumps(self.groups))
        self.export['sha256'] = digest(export_path)
        result = self.plan()
        self.assertEqual(result['evidence']['native_debts']['groups'], self.groups)
        self.assertEqual(result['proof_status'], 'unproved')
        self.assertFalse(result['contract_closed'])
        self.assertEqual(result['evidence']['inherited_debts'],
                         self.capture['inherited_debts'])
        self.assertIn('decodeItemByteFoldStringHeader', fixture['target'])
        self.assertNotIn('decodeItemEntryAt800d6a24', fixture['target'])

    def test_source_hash_change_rejects_design(self):
        (self.root / 'Contracts/Entry.v').write_text('Definition changed := True.')
        self.assertRaises(ValueError, self.plan)

    def test_unbound_definition_is_rejected(self):
        self.block['entry_definition'] = 'Other.Module.successor'
        self.assertRaises(ValueError, self.plan)

    def test_different_successor_is_rejected(self):
        self.capture['exit'] = '0x30'
        self.assertRaises(ValueError, self.plan)

    def test_root_domain_change_is_rejected(self):
        self.capture['root_provenance'] = {'entry': '0x10', 'domain': 'different'}
        self.assertRaises(ValueError, self.plan)

    def test_inherited_groups_cannot_be_omitted(self):
        del self.capture['inherited_debts']
        self.assertRaises(ValueError, self.plan)

    def test_post_abort_export_is_rejected(self):
        self.export['checkpoint'] = 'termination'
        self.assertRaises(ValueError, self.plan)

    def test_unavailable_export_is_rejected(self):
        self.export['success'] = False
        self.assertRaises(ValueError, self.plan)

    def test_changed_primary_capture_is_rejected(self):
        Path(self.export['source']).with_suffix('.mcp.json').write_text('[1]')
        self.assertRaises(ValueError, self.plan)

    def test_changed_goal_bytes_are_rejected(self):
        Path(self.export['path']).write_text('{}')
        self.assertRaises(ValueError, self.plan)

    def test_fingerprint_preserves_duplicates_and_stack_sides(self):
        original = debt_groups(self.groups)
        duplicated = deepcopy(self.groups)
        duplicated['shelf'].append(duplicated['shelf'][0])
        self.assertNotEqual(original['sha256'], debt_groups(duplicated)['sha256'])
        swapped = deepcopy(self.groups)
        swapped['stack'][0].reverse()
        self.assertNotEqual(original['sha256'], debt_groups(swapped)['sha256'])
        self.assertEqual(original['stack_sides'], [{'left': 0, 'right': 1}])

    def test_missing_groups_are_unavailable(self):
        for key in self.groups:
            incomplete = deepcopy(self.groups)
            del incomplete[key]
            self.assertRaises(ValueError, debt_groups, incomplete)

    def test_unavailable_null_groups_do_not_equal_verified_empty_groups(self):
        empty = {key: [] for key in self.groups}
        self.assertTrue(debt_groups(empty)['empty'])
        for key in empty:
            with self.subTest(group=key):
                unavailable = deepcopy(empty)
                unavailable[key] = None
                self.assertRaisesRegex(ValueError, 'Unavailable goal group',
                                       debt_groups, unavailable)

    def test_id_only_shelf_is_retained_without_inventing_a_proposition(self):
        groups = deepcopy(self.groups)
        groups['shelf'] = [42]
        self.assertEqual(debt_groups(groups)['groups']['shelf'], [42])
        self.assertFalse(debt_groups(groups)['empty'])

    def test_same_name_register_data_gets_a_new_existential_witness(self):
        target = {'binders': [{'name': 'args', 'type': 'Args'},
                              {'name': 'x13', 'type': 'bv 64'}],
                  'application': 'Target args x13'}
        expression = successor_application(target, '(args : Args) (x13 : bv 64)', ['args'])
        self.assertEqual(expression, '(∃ (successor_x13 : bv 64), Target args successor_x13)%I')

    def test_declared_interface_keeps_successor_registers_and_arrays_existential(self):
        binders = [{'name': 'args', 'type': 'Args'}, {'name': 'x13', 'type': 'bv 64'},
                   {'name': 'bufferBytes', 'type': 'list byte'},
                   {'name': 'listBytes', 'type': 'list byte'},
                   {'name': 'frameBytes', 'type': 'list byte'}]
        design = {'entry_pc': '0x10', 'blocks': [{'entry_pc': '0x10', 'binders': binders[:-1]}],
                  'table_convention': {'successor_root_parameters': ['args']}}
        fixed = successor_root_parameters(design)
        expression = successor_application({'binders': binders,
            'application': 'Target args x13 bufferBytes listBytes frameBytes'},
            '(args : Args) (x13 : bv 64) (bufferBytes listBytes : list byte)', fixed)
        self.assertEqual(fixed, ['args'])
        self.assertEqual(expression,
            '(∃ (successor_x13 : bv 64) (successor_bufferBytes : list byte) '
            '(successor_listBytes : list byte) (successor_frameBytes : list byte), '
            'Target args successor_x13 successor_bufferBytes successor_listBytes successor_frameBytes)%I')

    def test_absent_interface_convention_preserves_existing_root_parameters(self):
        design = {'entry_pc': '0x10', 'blocks': [{'entry_pc': '0x10',
                  'binders': [{'name': 'returnAddress', 'type': 'Z'},
                              {'name': 'args', 'type': 'Args'}]}]}
        self.assertEqual(successor_root_parameters(design), ['returnAddress', 'args'])

    def test_invalid_interface_conventions_reject(self):
        design = {'entry_pc': '0x10', 'blocks': [{'entry_pc': '0x10',
                  'binders': [{'name': 'args', 'type': 'Args'}, {'name': 'x13', 'type': 'bv 64'}]}],
                  'table_convention': {}}
        for selected in ('args', ['missing'], ['args', 'args'], ['x13', 'args'], [True]):
            with self.subTest(selected=selected), self.assertRaisesRegex(ValueError, 'ordered subset'):
                design['table_convention']['successor_root_parameters'] = selected
                successor_root_parameters(design)

    def test_fixed_root_parameter_cannot_change_type(self):
        self.assertRaises(ValueError, successor_application,
                          {'binders': [{'name': 'args', 'type': 'Other'}],
                           'application': 'Target args'}, '(args : Args)', ['args'])

    def test_native_source_keeps_all_successors_and_removes_abstract_stops(self):
        root = dict(self.block, entry_pc='0x10')
        second = dict(self.block, entry_pc='0x30')
        design = {'entry_pc': '0x10', 'blocks': [root, self.block, second],
                  'table_convention': {'existential_binders': "Each row's binders, in their listed order"}}
        state = {'root_provenance': {k: root[k] for k in ('entry_definition', 'resource_predicate', 'binders', 'arguments', 'source_hashes')},
                 'binders': '`{!islaG Sigma} `{!threadG} (args : Args)',
                 'coq': [], 'spatial': ['Contracts.Entry.successor (args)']}
        source = ('Require Import ZesuSsz.Automation.All.\n'
                  'Lemma infer_boundary ' + state['binders'] +
                  ' (BLK_STOP_20 : iProp Sigma) (BLK_STOP_30 : iProp Sigma) :\n'
                  'instr_pre 0x20 BLK_STOP_20 -∗ instr_pre 0x30 BLK_STOP_30 -∗ instr_body 0x10 Entry.\n'
                  'Proof.\ntry zesu_block.\nAbort.\n')
        with patch('successor_entailment.chain_root.render_probe', return_value=source):
            result = native_boundary_source(state, {'start': '0x10', 'successors': ['0x20', '0x30']}, design, self.root)
            off = native_boundary_source(state, {'start': '0x10', 'successors': ['0x20', '0x30']}, design, self.root, enabled=False, historical_target=0x30)
        self.assertEqual(off['source'], source)
        self.assertNotIn('BLK_STOP_', result['source'])
        self.assertNotIn('Abort.', result['source'])
        self.assertEqual(result['successors'], ['0x20', '0x30'])
        self.assertIn('Qed.', result['source'])

    def test_checker_requires_all_kernel_and_debt_evidence(self):
        for defect in (None, 'clamp', 'shelf', 'missing_group', 'compile', 'assumptions', 'inherit', 'export'):
            with self.subTest(defect=defect):
                empty = {'goals': [], 'stack': [], 'shelf': [], 'given_up': []}
                if defect == 'shelf':
                    empty['shelf'] = [{'ty': 'debt'}]
                if defect == 'missing_group':
                    del empty['given_up']
                export_path = self.root / 'checker_goals.json'
                export_path.write_text(json.dumps(empty))
                calls = []
                class Session:
                    async def call_tool(inner, name, arguments):
                        calls.append((name, arguments))
                        if name == 'rocq_start':
                            interactive = Path(arguments['file'])
                            self.assertNotEqual(interactive, self.root / 'Checker.v')
                            self.assertEqual(interactive.read_text(), self.launch_imports + statement + '\nProof.\nAbort.\n')
                            self.assertEqual((self.root / 'Checker.v').read_text(), rendered['source'])
                        if name == 'rocq_health':
                            return {'ok': True}
                        if name == 'rocq_diag':
                            return {'pet': {'pid': 123}}
                        if name == 'rocq_complete_goals':
                            return {'success': defect != 'export', 'path': str(export_path), 'sha256': digest(export_path)}
                        if name == 'rocq_compile_file':
                            return {'success': defect != 'compile'}
                        if name == 'rocq_verify':
                            return {'success': True, 'assumptions': ['axiom'] if defect == 'assumptions' else []}
                        if name == 'rocq_check' and defect == 'clamp':
                            return {'success': True, 'state_id': 3, 'clamped_timeout': 300}
                        return {'success': True, 'state_id': 3}
                statement = 'Lemma boundary : instr_body 0x10 Entry.'
                rendered = {'source': self.launch_imports + statement + '\nProof.\n  try zesu_block.\nQed.\n',
                            'function': 'fixture',
                            'lemma': 'boundary', 'scope': 'unproved native designed boundary',
                            'entry_pc': '0x10', 'entry_definition': 'Contracts.Entry.successor',
                            'statement_sha256': hashlib.sha256(statement.encode()).hexdigest()}
                result = asyncio.run(check_boundary(Session(), rendered, self.root / 'Checker.v',
                                     self.root, inherited_debts={'shelf': ['inherited']} if defect == 'inherit' else {}))
                self.assertEqual(result['block_closed'], defect in (None, 'clamp'))
                self.assertFalse(result['contract_closed'])
                primary = [a for n, a in calls if n == 'rocq_check']
                self.assertEqual(primary, [] if defect in {'missing_group', 'export'} else
                                 [{'from_state': 3, 'body': 'try zesu_block.', 'timeout': 1200}])
                if primary:
                    recorded = next(call for call in result['calls'] if call['tool'] == 'rocq_check')
                    self.assertEqual(recorded['sentence_budgets'][0]['effective_timeout_seconds'],
                                      300 if defect == 'clamp' else 1200)

    def test_session_start_does_not_execute_the_block_body(self):
        executed = []
        export_path = self.root / 'startup_goals.json'
        export_path.write_text(json.dumps({'goals': [{'ty': 'entry'}],
                                          'stack': [], 'shelf': [], 'given_up': []}))
        statement = 'Lemma boundary : instr_body 0x10 Entry.'
        rendered = {'source': self.launch_imports + statement + '\nProof.\ntry zesu_block.\nQed.\n',
                    'function': 'fixture',
                    'lemma': 'boundary', 'scope': 'unproved native designed boundary',
                    'entry_pc': '0x10', 'entry_definition': 'Entry',
                    'statement_sha256': hashlib.sha256(statement.encode()).hexdigest()}

        class Session:
            async def call_tool(inner, name, arguments):
                if name == 'rocq_health':
                    return {'ok': True}
                if name == 'rocq_diag':
                    return {'pet': {'pid': 123}}
                if name == 'rocq_start':
                    # The pinned server checks the complete document before start.
                    loaded = Path(arguments['file']).read_text()
                    if 'try zesu_block.' in loaded:
                        executed.append('document-load')
                    self.assertEqual(executed, [])
                    return {'success': True, 'state_id': 1}
                if name == 'rocq_complete_goals':
                    return {'success': True, 'path': str(export_path), 'sha256': digest(export_path)}
                if name == 'rocq_check':
                    self.assertEqual(arguments['body'], 'try zesu_block.')
                    executed.append('explicit-proof-request')
                    return {'success': False, 'reason': 'tactic_failed'}
                self.fail('An incomplete block must not reach certificate tools')

        result = asyncio.run(check_boundary(Session(), rendered, self.root / 'Startup.v',
                                           self.root, inherited_debts={}))
        self.assertEqual(executed, ['explicit-proof-request'])
        self.assertEqual(result['residual_class'], 'native_automation')
        self.assertEqual((self.root / 'Startup.v').read_text(), rendered['source'])

    def test_checker_rejects_budgets_outside_the_current_policy(self):
        for seconds in (0, 1201):
            with self.subTest(seconds=seconds):
                with self.assertRaisesRegex(ValueError, '1 and 1200 seconds'):
                    asyncio.run(check_boundary(None, {}, self.root / 'Budget.v',
                                self.root, inherited_debts={}, seconds=seconds))

    def test_capture_entailment_cannot_close_a_native_block(self):
        # The same kernel evidence has a different scope for resource entailment.
        # The checker requires native-boundary scope before setting block_closed.
        self.assertFalse(self.plan()['contract_closed'])

    def test_extra_trace_import_requires_its_exact_hash(self):
        path = self.root / 'Contracts/TraceIndex.v'
        path.write_text('Definition traceIdentity := 0.\n')
        bindings = {'Contracts.TraceIndex': {'path': 'Contracts/TraceIndex.v', 'sha256': digest(path)}}
        capture = dict(self.capture, coq=[], spatial=['True'], imports=[])
        source = capture_entailment_source(capture, self.plan(), extra_imports=bindings, root=self.root)
        self.assertIn('Require Import Contracts.TraceIndex.', source['source'])
        self.assertEqual(source['bound_imports'], {'Contracts/TraceIndex.v': digest(path)})
        path.write_text('Definition traceIdentity := 1.\n')
        self.assertRaises(ValueError, capture_entailment_source, capture, self.plan(),
                          extra_imports=bindings, root=self.root)

    def test_generated_import_uses_theory_and_selected_manifest(self):
        directory = self.root / 'generated/traces'
        directory.mkdir(parents=True)
        source = directory / 'index.v'
        source.write_text('Definition traceIndex := 0.\n')
        theory = directory / 'dune'
        theory.write_text('(coq.theory (name Selected.Trace))\n')
        manifest = self.root / 'recipe.json'
        recipe = {'artifact_identity': 'selected', 'project_derived': {
            'generated/traces/index.v': {'path': 'generated/traces/index.v',
                                       'sha256': digest(source), 'artifact_identity': 'selected'}}}
        manifest.write_text(json.dumps(recipe))
        binding = {'path': 'generated/traces/index.v', 'sha256': digest(source),
                   'theory': {'path': 'generated/traces/dune', 'sha256': digest(theory)},
                   'manifest': {'path': 'recipe.json', 'sha256': digest(manifest)}}
        hashes = validate_import('Selected.Trace.index', binding, self.root)
        self.assertEqual(len(hashes), 3)
        self.assertRaises(ValueError, validate_import, 'Wrong.Trace.index', binding, self.root)
        recipe['project_derived']['generated/traces/index.v']['artifact_identity'] = 'other'
        manifest.write_text(json.dumps(recipe))
        binding['manifest']['sha256'] = digest(manifest)
        self.assertRaises(ValueError, validate_import, 'Selected.Trace.index', binding, self.root)

    def test_true_theorem_cannot_claim_native_block_closure(self):
        class Session:
            async def call_tool(inner, name, arguments):
                self.fail('A mismatched native signature must fail before proof execution')
        statement = 'Lemma boundary : True.'
        rendered = {'source': self.launch_imports + statement + '\nProof.\ntry zesu_block.\nQed.\n',
                    'function': 'fixture',
                    'lemma': 'boundary', 'scope': 'unproved native designed boundary',
                    'entry_pc': '0x10', 'entry_definition': 'Contracts.Entry.successor',
                    'statement_sha256': hashlib.sha256(statement.encode()).hexdigest()}
        result = asyncio.run(check_boundary(Session(), rendered, self.root / 'Mismatch.v',
                             self.root, inherited_debts={}))
        self.assertFalse(result['block_closed'])
        self.assertEqual(result['residual_class'], 'evidence_unavailable')


if __name__ == '__main__':
    unittest.main()
