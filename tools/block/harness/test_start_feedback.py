"""Exercise the public start adapter without a PET process or proof command."""
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import start_feedback_mcp as F


class FeedbackSchema(unittest.TestCase):
    def result(self, messages, finished=False, **changes):
        from pytanque.protocol import State
        state = State(st=7, proof_finished=finished, feedback=messages)
        result = dict(success=True, state_id=7, goals='', proof_finished=finished)
        result.update(changes)
        return F.retain_feedback(result, SimpleNamespace(state=state))

    def test_exact_sdk_severities_preserve_all_messages(self):
        messages = [(1, 'syntax fixture'), (2, 'warning fixture'),
                    (3, 'information fixture'), (4, 'hint fixture')]
        result = self.result(messages)
        self.assertFalse(result['success'])
        self.assertEqual(result['reason'], 'document_error')
        self.assertEqual([row['severity'] for row in result['start_feedback']['messages']], [1, 2, 3, 4])
        self.assertEqual([row['message'] for row in result['start_feedback']['messages']],
                         [message for _, message in messages])
        self.assertEqual(result['state_id'], 7)

    def test_warning_information_and_hint_keep_success(self):
        result = self.result([(2, 'warning'), (3, 'information'), (4, 'hint')])
        self.assertTrue(result['success'])

    def test_empty_goals_do_not_override_reported_document_error(self):
        result = self.result([(1, 'parse fixture')], finished=True)
        self.assertFalse(result['success'])
        self.assertTrue(result['proof_finished'])
        self.assertEqual(result['goals'], '')

    def test_empty_goals_do_not_change_proof_finished(self):
        self.assertFalse(self.result([])['proof_finished'])
        self.assertTrue(self.result([], finished=True)['proof_finished'])

    def test_unknown_severity_and_malformed_messages_refuse(self):
        for messages in [[(0, 'unknown')], [(True, 'invalid')], [(1, 17)], [('1', 'invalid')]]:
            with self.subTest(messages=messages), self.assertRaisesRegex(ValueError, 'unsupported schema'):
                self.result(messages)

    def test_original_failure_preserves_its_reason_and_error(self):
        original = dict(success=False, reason='not_found', error='original fixture', state_id=9)
        result = F.retain_feedback(original, None)
        self.assertEqual({key: result[key] for key in original}, original)

    def test_missing_state_and_changed_finished_refuse(self):
        with self.assertRaisesRegex(ValueError, 'lacks its returned PET state'):
            F.retain_feedback(dict(success=True), None)
        with self.assertRaisesRegex(ValueError, 'disagree'):
            self.result([], finished=False, proof_finished=True)

    def test_actual_sdk_interface_and_state_schema_match(self):
        import inspect
        from rocq_mcp import server
        run_start = server.run_start
        self.assertEqual(tuple(inspect.signature(run_start).parameters), F.START_PARAMETERS)
        from pytanque.protocol import State
        self.assertEqual(set(State.__dataclass_fields__),
                         {'st', 'proof_finished', 'feedback', 'hash', 'generation'})


class AdapterControls(unittest.IsolatedAsyncioTestCase):
    async def test_adapter_preserves_exact_arguments_and_executes_no_pet_command(self):
        calls = []
        async def original(file, theorem, workspace, lifespan_state, line=None,
                           character=None, preamble='', force_restart=False, timeout=None):
            calls.append((file, theorem, workspace, lifespan_state, line, character,
                          preamble, force_restart, timeout))
            return dict(success=True, state_id=7, proof_finished=False, goals='unchanged')
        class NoCommands:
            def __getattr__(self, name):
                raise AssertionError('The feedback adapter accessed a PET command: ' + name)
        async def locked(callback, context, tool, timeout=None):
            self.assertIs(context, context_value)
            self.assertEqual(tool, 'rocq_start')
            return callback(NoCommands())
        context_value = object()
        server = SimpleNamespace(run_start=original, _run_with_pet=locked)
        entry = SimpleNamespace(state=SimpleNamespace(proof_finished=False, feedback=[(3, 'notice')]))
        interactive = SimpleNamespace(_state_get=lambda state_id: entry if state_id == 7 else None)
        F.install_start_feedback(server, interactive)
        result = await server.run_start('exact.v', '', 'exact-workspace', context_value,
                                        line=29, character=5, timeout=None)
        self.assertEqual(calls, [('exact.v', '', 'exact-workspace', context_value, 29, 5, '', False, None)])
        self.assertTrue(result['success'])
        self.assertEqual(result['goals'], 'unchanged')
        wrapped = server.run_start
        F.install_start_feedback(server, interactive)
        self.assertIs(server.run_start, wrapped)

    async def test_incompatible_sdk_interface_refuses(self):
        async def wrong(file):
            raise AssertionError('The incompatible handler ran.')
        with self.assertRaisesRegex(ValueError, 'unsupported interface'):
            F.install_start_feedback(SimpleNamespace(run_start=wrong), SimpleNamespace(_state_get=lambda _: None))


if __name__ == '__main__':
    unittest.main()
