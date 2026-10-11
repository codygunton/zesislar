"""Exercise the actual primary driver through a fake MCP session."""
import asyncio
from contextlib import asynccontextmanager
import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent/'block'))
import discovery


class PrimaryTimeoutTests(unittest.TestCase):
    def test_primary_has_one_sentence_and_the_full_300_second_budget(self):
        self.exercise_primary()

    def test_export_exception_keeps_the_primary_outcome_and_marks_missing_groups(self):
        self.exercise_primary('exception')

    def test_failed_export_response_marks_group_coverage_incomplete(self):
        self.exercise_primary('response')

    def test_primary_rpc_exception_cannot_claim_complete_native_coverage(self):
        self.exercise_primary('primary-rpc')

    def exercise_primary(self, export_failure=None):
        if importlib.util.find_spec('rocq_mcp') is None:
            # Use the installed MCP interpreter, not a copied SDK implementation.
            executable = shutil.which('rocq-mcp')
            self.assertIsNotNone(executable, 'The declared rocq-mcp tool is required')
            header = Path(executable).resolve().read_text().splitlines()[0]
            self.assertTrue(header.startswith('#!') and 'python' in header)
            result = subprocess.run([header[2:], str(Path(__file__).resolve())],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return
        from rocq_mcp import server
        from rocq_mcp import interactive
        events = []
        returned_states = []

        class Session:
            def __init__(self, *args):
                self.state = 0

            async def __aenter__(self):
                return self

            async def __aexit__(self, *args):
                pass

            async def initialize(self):
                pass

            async def call_tool(self, name, arguments):
                events.append((name, arguments))
                if name == 'rocq_check' and arguments.get('body') == 'try zesu_block.' and export_failure == 'primary-rpc':
                    raise RuntimeError('The primary transport failed')
                if name == 'rocq_health':
                    value = {'ok': True, 'toolchain': {'pet': {'path': 'pinned-pet'}}}
                elif name == 'rocq_complete_goals':
                    if export_failure == 'exception':
                        raise RuntimeError('The capture transport failed')
                    if export_failure == 'response':
                        return SimpleNamespace(structuredContent={'success': False, 'error': 'The capture export failed'})
                    from complete_goals_mcp import write_export
                    class Complete:
                        def to_json(self):
                            return {'goals': [{'ty': 'True', 'hyps': []}], 'stack': [[[], [{'ty': 'stack debt'}]]],
                                    'shelf': [{'ty': 'shelved debt'}], 'given_up': [{'ty': 'given-up debt'}]}
                    value = write_export(Complete(), options['complete_dir'], arguments['from_state'])
                elif name == 'rocq_diag':
                    value = {}
                else:
                    self.state += 1
                    returned_states.append(self.state)
                    value = {'success': True, 'state_id': self.state, 'goals': '|- True'}
                return SimpleNamespace(structuredContent=value)

        @asynccontextmanager
        async def stdio(parameters):
            yield None, None

        source = 'Lemma infer_boundary : True.\nProof.\nidtac.\ntry zesu_block.\nidtac.\nAbort.\n'
        with tempfile.TemporaryDirectory() as temporary:
            modules = {'mcp': SimpleNamespace(ClientSession=Session,
                StdioServerParameters=lambda **kwargs: kwargs),
                'mcp.client': SimpleNamespace(),
                'mcp.client.stdio': SimpleNamespace(stdio_client=stdio)}
            options = {'mcp_command': 'fake', 'workspace': temporary, 'out': temporary,
                       'seconds': 300, 'terminal': '0x20', 'secondary_enabled': False,
                       'complete_dir': str(Path(temporary)/'complete')}
            original_state = {'marker': 'entry resources'}
            with patch.dict(sys.modules, modules), \
                    patch.object(discovery, 'time', SimpleNamespace(monotonic=lambda: 10)), \
                    patch.object(discovery.chain_root, 'render_probe', return_value=source), \
                    patch.object(discovery.chain_root, 'parse_probe', return_value=[{
                        'outcome': 'reached', 'pending_goals': [], 'shelved_goals': []}]) as parse:
                result = asyncio.run(discovery.probe_block(
                    {'entry_pc': '0x10', 'entry_class': 'root'},
                    {'successors': ['0x20']}, original_state, options))
                self.assertIs(parse.call_args.args[1], original_state)
            opened = next(arguments for name, arguments in events if name == 'rocq_start')
            interactive_source = Path(opened['file'])
            self.assertEqual(interactive_source.read_text(), 'Lemma infer_boundary : True.\nProof.\nAbort.\n')
            self.assertEqual(next(path for path in Path(temporary).glob('probes/*.v')
                                  if path != interactive_source).read_text(), source)
            calls = [arguments for name, arguments in events if name == 'rocq_check']
            heavy = [call for call in calls if 'try zesu_block.' in call['body']]
            self.assertEqual(len(heavy), 1)
            self.assertEqual(interactive._split_rocq_sentences(heavy[0]['body']), ['try zesu_block.'])
            self.assertEqual(heavy[0]['timeout'], 300)
            self.assertEqual(calls[0]['body'], 'idtac.')
            self.assertEqual(calls[0]['timeout'], 60)
            self.assertEqual(heavy[0]['from_state'], returned_states[1])
            if export_failure == 'primary-rpc':
                self.assertEqual(result['captures'][0]['outcome'], 'mcp-error')
                self.assertFalse(result['captures'][0]['complete_native_coverage'])
                self.assertEqual([value['checkpoint'] for value in result['captures'][0]['complete_exports']], ['entry', 'preparation'])
                self.assertEqual(len(calls), 2)
                return
            self.assertEqual(calls[2]['from_state'], returned_states[2])
            step = next(row for row in result['captures'][0]['primary_steps']
                        if row['label'] == 'primary-unchanged-zesu_block')
            self.assertEqual([row['timeout_seconds'] for row in step['sentence_budgets']], [300])
            self.assertEqual(len(step['sdk']['sha256']), 64)
            exports = result['captures'][0]['complete_exports']
            self.assertEqual([value['checkpoint'] for value in exports], ['entry', 'preparation', 'primary', 'recorders', 'termination'])
            self.assertEqual(result['captures'][0]['outcome'], 'reached')
            self.assertEqual(result['captures'][0]['complete_native_coverage'], not bool(export_failure))
            self.assertIn('post-Abort', exports[-1]['scope'])
            for value in exports:
                self.assertEqual(value['coverage'], 'unavailable' if export_failure else 'complete')
                if not export_failure:
                    self.assertEqual(value['stack_frame_goal_counts'], [{'left': 0, 'right': 1}])
                    self.assertEqual(value['shelved_goals'], 1)
                    self.assertEqual(value['given_up_goals'], 1)
                self.assertEqual(value['primary_capture_sha256'], discovery.digest(next(Path(temporary).glob('probes/*.mcp.json'))))
                self.assertEqual(value['source_sha256'], discovery.digest(next(Path(temporary).glob('probes/*_interactive.v'))))
            if not export_failure:
                self.assertEqual([value['state_id'] for value in exports], returned_states)
            self.observed_calls = events
            self.probe_result = result


if __name__ == '__main__':
    unittest.main()
