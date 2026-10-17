"""Check resource lookup admission without running Rocq or machine code."""
from contextlib import asynccontextmanager
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import launch_entries as entries
import launch_resources as resources


class ResourceTests(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'ZesuSsz/Evidence').mkdir(parents=True)
        (self.root / 'ZesuSsz/Compliance').mkdir()
        (self.root / 'ZesuSsz/Compliance/TestHints.v').write_text('(* original umbrella *)\n')
        (self.root / 'ZesuSsz/Evidence/test_function_text.json').write_text(json.dumps({
            'function': 'test.function', 'registrations': ['ZesuSsz/Compliance/TestHints.v']}))
        self.modules = ['ZesuSsz.Automation.All', 'ZesuSsz.Automation.Approved',
                        'ZesuSsz.Compliance.TestHints', 'Test.index']
        self.artifacts = {}
        for module in self.modules:
            path = self.root / (module + '.vo')
            path.write_bytes(module.encode())
            self.artifacts[module] = entries.file_reference(path)
        self.source = self.root / 'Boundary.v'
        self.source.write_text(''.join('Require Import ' + module + '.\n' for module in self.modules)
            + 'Lemma entry `{!islaG Sigma} `{!threadG} :\nTest.selectedCode -∗\n'
              'instr_body 0x1000 True.\nProof.\ntry zesu_block.\nQed.\n')
        self.entry = {'id': 'block_1000', 'source': entries.file_reference(self.source),
                      'theorem': 'entry', 'artifacts': self.artifacts}
        self.index = self.root / 'index.v'
        self.index.write_text('Require Export Test.a1000.\nRequire Export Test.a1004.\n'
            'Definition instr_map := [(0x1000%Z, a1000 (* addi *)); (0x1004%Z, a1004)].\n')
        self.resource = {'pc': '0x1000', 'selected_code': 'Test.selectedCode',
                         'index_module': 'Test.index.instr_map', 'index_source': entries.file_reference(self.index)}
        checked = entries.prepare_entries([self.entry], self.root, 'test.function')[0]
        self.declaration = self.root / 'DECLARATIONS.json'
        self.declaration.write_text(json.dumps({'passed': True, 'selected_entries': 1, 'checked_entries': 1,
            'entries': [{'passed': True, 'id': self.entry['id'], 'source': checked['source'],
                         'artifacts': checked['artifacts']}]}))
        self.active = False
        self.calls = []
        self.behavior = {}
        self.opened = []

    def plan(self):
        return resources.make_plan(self.entry, self.resource, self.root, 'test.function')

    def refresh(self):
        self.entry['source'] = entries.file_reference(self.source)
        self.resource['index_source'] = entries.file_reference(self.index)

    def identity(self, pid):
        if not self.active:
            raise FileNotFoundError('The fake owned Pet exited.')
        return {'pid': pid, 'start_ticks': 100, 'state': 'S'}

    @asynccontextmanager
    async def factory(self, directory):
        self.opened.append(directory)
        self.active = True
        owner = self
        class Session:
            def __init__(self):
                self.state = 1
                self.stage = 'entry'
            async def initialize(self):
                owner.calls.append(('initialize', {}))
                return {'structuredContent': {'initialized': True}}
            async def call_tool(self, tool, arguments):
                owner.calls.append((tool, arguments))
                if tool == 'rocq_health':
                    value = {'success': True, 'ok': True}
                elif tool == 'rocq_start':
                    text = Path(arguments['file']).read_text()
                    if 'try zesu_block.' in text or not text.endswith('Proof.\nAbort.\n'):
                        raise AssertionError('The diagnostic contains a primary body.')
                    value = {'success': True, 'state_id': 1}
                    if owner.behavior.get('refuse_start') or owner.behavior.get('refuse_id') == directory.name:
                        value = {'success': False, 'error': 'exact refused entry'}
                elif tool == 'rocq_diag':
                    value = {'success': True, 'pet': {'pid': 44}}
                elif tool == 'rocq_query':
                    module = arguments['command'].removeprefix('Locate Library ').removesuffix('.')
                    value = {'success': True, 'from_state_id': self.state,
                             'output': module + ' has been loaded from file ' + owner.artifacts[module]['path']}
                    if owner.behavior.get('wrong_object'):
                        value['output'] += '.wrong'
                elif tool == 'rocq_check':
                    command = next(row for row in owner.plan()['commands'] if row['body'] == arguments['body'])
                    self.stage = command['stage']
                    self.state += 1
                    value = {'success': True, 'state_id': self.state, 'commands_run': 1,
                             'proof_finished': self.stage == 'closed'}
                    if owner.behavior.get('refuse') == self.stage:
                        value.update(success=False, error='exact resource refusal: ' + self.stage)
                    if owner.behavior.get('boolean_state'):
                        value['state_id'] = True
                elif tool == 'rocq_complete_goals':
                    goals = [] if self.stage == 'closed' else [{'info': {'evar': 1}, 'hyps': [], 'ty': 'exact guarded goal'}]
                    groups = {'goals': goals, 'stack': [], 'shelf': [], 'given_up': []}
                    if owner.behavior.get('unexpected_goals') and self.stage == 'lookup':
                        groups['shelf'] = [{'info': {'evar': 9}, 'hyps': [], 'ty': 'foreign debt'}]
                    value = {**groups, 'kernel_groups': deepcopy(groups),
                             'local_definition_export': {'original_state_preserved': True}}
                    path = directory / ('state_' + str(self.state) + '.json')
                    path.write_text(json.dumps(value))
                    value = {'success': True, 'state_id': self.state, **entries.file_reference(path)}
                else:
                    raise AssertionError('The resource probe requested a forbidden tool: ' + tool)
                return {'structuredContent': value, 'content': [{'type': 'text', 'text': 'retained raw response'}]}
        try:
            yield Session()
        finally:
            self.active = False
            if self.behavior.get('mutate_index'):
                self.index.write_text('changed index')

    async def run_probe(self):
        with patch.object(entries, 'process_identity', side_effect=self.identity):
            return await resources.check_resources([{'entry': self.entry, 'resource': self.resource}],
                entries.file_reference(self.declaration), self.root, 'test.function', self.root / 'output', self.factory)

    def test_plan_keeps_original_prefix_and_primary_bytes(self):
        before = self.source.read_bytes()
        plan = self.plan()
        self.assertEqual(self.source.read_bytes(), before)
        self.assertTrue(plan['source'].startswith(before.decode().split('Lemma entry')[0]))
        self.assertNotIn('try zesu_block.', plan['source'])
        self.assertIn('IKPre _ _ => False', plan['source'])
        self.assertIn('instruction = (Some Test.a1000.a1000)', plan['source'])
        self.assertEqual(plan['expected_instruction'], 'Test.a1000.a1000')

    def test_commands_have_explicit_environment_registration_and_exact_map(self):
        commands = self.plan()['commands']
        self.assertEqual(commands[0]['body'], 'iStartProof.')
        self.assertIn('LithiumUnfold (@Test.selectedCode)', commands[2]['body'])
        self.assertIn('assert_fails (has_evar registered)', commands[2]['body'])
        self.assertIn('idtac "RESOURCE-REGISTRATION" registered', commands[2]['body'])
        self.assertIn('List.filter', commands[1]['body'])
        self.assertIn('4096%Z', commands[1]['body'])
        self.assertIn('Test.a1000.a1000', commands[1]['body'])
        self.assertIn('liFindInContext', commands[5]['body'])
        self.assertIn('constr_eq lookup constr:(ZesuSsz.Contracts.SelectedCodeLookup.selectedCodeLookup Test.index.instr_map)', commands[6]['body'])
        self.assertIn('constr_eq address constr:(4096%Z)', commands[6]['body'])
        self.assertNotIn('try (', commands[6]['body'])
        self.assertIn('liEnsureInvariant; lazymatch goal', commands[4]['body'])
        self.assertIn('Hlocal := @LET_ID _ (find_in_context (FindInstrKind ?address false)', commands[4]['body'])
        self.assertIn('constr_eq Hlocal hidden; constr_eq address constr:(4096%Z); liUnfoldLetGoal', commands[4]['body'])
        for command in commands:
            for forbidden in ('zesu_block', 'liAStep', 'liARun', 'liInst', 'liAAsm', 'liAExp', 'liAOther', 'liStep', 'vm_compute'):
                self.assertNotIn(forbidden, command['body'])
        self.assertFalse(any('unfold Test.selectedCode' in row['body'] for row in commands))

    def test_wrong_pc_rejects_before_session(self):
        self.resource['pc'] = '0x1004'
        with self.assertRaisesRegex(ValueError, 'differs from the primary'):
            self.plan()

    def test_missing_code_premise_rejects(self):
        self.resource['selected_code'] = 'Test.otherCode'
        with self.assertRaisesRegex(ValueError, 'absent or ambiguous'):
            self.plan()

    def test_ambiguous_code_premises_reject(self):
        self.source.write_text(self.source.read_text().replace('Test.selectedCode -∗',
                                                              'Test.otherCode -∗\nTest.selectedCode -∗'))
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'absent or ambiguous'):
            self.plan()

    def test_code_name_cannot_inject_a_tactic(self):
        self.resource['selected_code'] = 'Test.selectedCode); liAStep'
        with self.assertRaisesRegex(ValueError, 'exact names'):
            self.plan()

    def test_duplicate_instruction_pc_rejects(self):
        self.index.write_text(self.index.read_text().replace('(0x1004%Z, a1004)', '(0x1000%Z, a1004)'))
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'duplicate PCs'):
            self.plan()

    def test_missing_instruction_rejects(self):
        self.index.write_text(self.index.read_text().replace('(0x1000%Z, a1000 (* addi *));', ''))
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'omits the entry'):
            self.plan()

    def test_unsupported_map_expression_rejects(self):
        self.index.write_text(self.index.read_text().replace('a1000 (* addi *)', 'None'))
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'exact trace export'):
            self.plan()

    def test_ambiguous_trace_export_rejects(self):
        self.index.write_text('Require Export Other.a1000.\n' + self.index.read_text())
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'exact trace export'):
            self.plan()

    def test_missing_index_artifact_rejects(self):
        self.source.write_text(self.source.read_text().replace('Require Import Test.index.\n', ''))
        self.entry['artifacts'].pop('Test.index')
        self.refresh()
        with self.assertRaisesRegex(ValueError, 'exact import binding'):
            self.plan()

    async def test_separate_declaration_receipt_is_required(self):
        self.declaration.write_text(json.dumps({'passed': False}))
        with self.assertRaisesRegex(ValueError, 'All selected declarations'):
            await self.run_probe()
        self.assertEqual(self.opened, [])

    async def test_substituted_declaration_source_rejects(self):
        value = json.loads(self.declaration.read_bytes())
        value['entries'][0]['source']['binding']['sha256'] = '0' * 64
        self.declaration.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, 'differs from the resource'):
            await self.run_probe()
        self.assertEqual(self.opened, [])

    async def test_complete_resource_probe_keeps_original_and_owned_closure(self):
        before = self.source.read_bytes()
        result = await self.run_probe()
        self.assertTrue(result['passed'])
        self.assertEqual(self.source.read_bytes(), before)
        self.assertEqual(result['machine_instructions'], 0)
        self.assertEqual(result['primary_calls'], 0)
        self.assertTrue(result['entries'][0]['owned_pet_exited'])
        self.assertEqual(len(result['entries'][0]['exports']), 10)
        self.assertNotIn('rocq_compile_file', [tool for tool, _ in self.calls])
        self.assertNotIn('rocq_verify', [tool for tool, _ in self.calls])

    async def test_missing_registration_refusal_is_retained(self):
        self.behavior['refuse'] = 'registration'
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        raw = sorted((self.root / 'output/block_1000/calls').glob('*-rocq_check-raw.json'))
        self.assertEqual(json.loads(raw[-1].read_bytes())['structuredContent']['error'],
                         'exact resource refusal: registration')
        self.assertEqual(len(result['entries'][0]['exports']), 3)

    async def test_lookup_refusal_prevents_release(self):
        self.behavior['refuse'] = 'lookup'
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        self.assertIn('lookup', result['entries'][0]['error']['message'])

    async def test_foreign_lookup_map_refusal_prevents_release(self):
        self.behavior['refuse'] = 'lookup-bound'
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        self.assertIn('lookup-bound', result['entries'][0]['error']['message'])

    async def test_IKPre_or_missing_instruction_refuses_selected_guard(self):
        self.behavior['refuse'] = 'selected'
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        self.assertIn('selected', result['entries'][0]['error']['message'])

    async def test_unexpected_goal_group_prevents_release(self):
        self.behavior['unexpected_goals'] = True
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        self.assertIn('unexpected goal group', result['entries'][0]['error']['message'])

    async def test_boolean_state_rejects(self):
        self.behavior['boolean_state'] = True
        result = await self.run_probe()
        self.assertFalse(result['passed'])

    async def test_index_mutation_prevents_release(self):
        self.behavior['mutate_index'] = True
        result = await self.run_probe()
        self.assertFalse(result['passed'])
        self.assertIsNotNone(result['input_error'])

    async def test_existing_output_rejects(self):
        (self.root / 'output').mkdir()
        with self.assertRaisesRegex(ValueError, 'fresh workspace'):
            await self.run_probe()
        self.assertEqual(self.opened, [])


if __name__ == '__main__':
    unittest.main()
