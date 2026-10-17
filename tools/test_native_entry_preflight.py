"""Check discovery's entry barrier without a Rocq server or primary tactic."""
import asyncio
import ast
from contextlib import asynccontextmanager
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import AsyncMock, patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import discovery
import launch_entries
import successor_entailment
from tools import test_launch_resources as entry_fixtures
from tools import test_native_boundary_discovery as discovery_fixtures


class NativeEntryPreflightTests(unittest.TestCase):
    def setUp(self):
        self.fixture = entry_fixtures.ResourceTests('test_complete_resource_probe_keeps_original_and_owned_closure')
        self.fixture.setUp()
        self.addCleanup(self.fixture.temporary.cleanup)
        self.root = self.fixture.root
        self.source = self.fixture.source.read_text()
        self.fixture.index.write_text(self.fixture.index.read_text().replace('0x1000', '0x10').replace('a1000', 'a10').replace('0x1004', '0x20').replace('a1004', 'a20'))
        self.fixture.resource['index_source'] = launch_entries.file_reference(self.fixture.index)
        self.mapping = self.root/'artifact-map.json'
        self.mapping.write_text(json.dumps({'schema': 2, 'function': 'test.function',
                                           'objects': self.fixture.artifacts,
                                           'lookup': {key: value for key, value in self.fixture.resource.items() if key != 'pc'}}))
        self.design = {'function': 'test.function'}
        self.design_path = self.root/'design.json'
        self.design_path.write_text(json.dumps(self.design))
        self.options = {'workspace': str(self.root), 'out': str(self.root/'discovery'),
                        'mcp_command': 'not-executed', 'entry_artifacts': str(self.mapping),
                        'design': str(self.design_path), 'seconds': 300}
        self.ready = [({'entry_pc': pc}, {'start': pc, 'successors': ['0x30']}, {})
                      for pc in ['0x10', '0x20']]

    def rendered(self, state, block, *args, **kwargs):
        return {'source': self.source.replace('0x1000', block['start']), 'lemma': 'entry', 'entry_pc': block['start'],
                'scope': 'unproved native designed boundary'}

    @asynccontextmanager
    async def factory(self, directory):
        fixture = self.fixture
        old_entry, old_resource = fixture.entry, fixture.resource
        source = Path(self.options['out'])/'entry-preflight-sources'/(directory.name + '.v')
        fixture.entry = {**old_entry, 'id': directory.name, 'source': launch_entries.file_reference(source)}
        fixture.resource = {**old_resource, 'pc': directory.name}
        try:
            async with fixture.factory(directory) as session:
                yield session
        finally:
            fixture.entry, fixture.resource = old_entry, old_resource

    def preflight(self):
        with patch.object(successor_entailment, 'native_boundary_source', side_effect=self.rendered), \
                patch.object(launch_entries, 'owned_sessions', return_value=self.factory), \
                patch.object(launch_entries, 'process_identity', side_effect=self.fixture.identity):
            return discovery.preflight_native_entries(self.ready, self.design, self.options)

    def test_every_selected_entry_reaches_the_barrier_before_worker_admission(self):
        gate = self.preflight()
        self.assertEqual(set(gate['source_hashes']), {'0x10', '0x20'})
        self.assertEqual(len(self.fixture.opened), 4)
        receipt = json.loads(Path(gate['report']['path']).read_bytes())
        self.assertTrue(receipt['passed'])
        for row, block, state in self.ready:
            discovery.require_native_entry_preflight(self.rendered(state, block),
                {**self.options, 'entry_preflight': gate})
        self.assertFalse({'rocq_compile_file', 'rocq_verify'} &
                         {tool for tool, _ in self.fixture.calls})
        self.assertFalse(any(tool == 'rocq_check' and 'zesu_block' in arguments['body']
                             for tool, arguments in self.fixture.calls))

    def test_second_entry_failure_retains_the_refusal_and_prevents_admission(self):
        self.fixture.behavior['refuse_id'] = '0x20'
        with self.assertRaisesRegex(ValueError, 'No native worker can start'):
            self.preflight()
        receipt = json.loads((self.root/'discovery/entry-preflight/REPORT.json').read_bytes())
        self.assertFalse(receipt['passed'])
        self.assertTrue(receipt['entries'][0]['passed'])
        self.assertFalse(receipt['entries'][1]['passed'])
        raw = next((self.root/'discovery/entry-preflight/declarations/0x20/calls').glob('*-rocq_start-raw.json'))
        self.assertEqual(json.loads(raw.read_bytes())['structuredContent']['error'], 'exact refused entry')

    def test_missing_artifact_rejects_before_a_session_starts(self):
        mapping = json.loads(self.mapping.read_bytes())
        mapping['objects'].pop(next(iter(mapping['objects'])))
        self.mapping.write_text(json.dumps(mapping))
        with self.assertRaisesRegex(ValueError, 'omits direct entry imports'):
            self.preflight()
        self.assertEqual(self.fixture.opened, [])

    def test_output_outside_the_workspace_rejects_before_writing(self):
        self.options['out'] = str(self.root.parent/'outside-admission')
        with self.assertRaisesRegex(ValueError, 'leaves its workspace'):
            self.preflight()
        self.assertFalse(Path(self.options['out']).exists())
        self.assertEqual(self.fixture.opened, [])

    def test_missing_receipt_rejects_the_worker(self):
        with self.assertRaisesRegex(ValueError, 'needs the completed entry preflight'):
            discovery.require_native_entry_preflight(self.rendered({}, self.ready[0][1]), self.options)

    def test_changed_primary_source_rejects_the_worker(self):
        gate = self.preflight()
        rendered = self.rendered({}, self.ready[0][1])
        rendered['source'] += '\n'
        with self.assertRaisesRegex(ValueError, 'source differs'):
            discovery.require_native_entry_preflight(rendered, {**self.options, 'entry_preflight': gate})

    def test_changed_artifact_rejects_the_worker(self):
        gate = self.preflight()
        Path(next(iter(self.fixture.artifacts.values()))['path']).write_bytes(b'substitution')
        with self.assertRaises(ValueError):
            discovery.require_native_entry_preflight(self.rendered({}, self.ready[0][1]),
                {**self.options, 'entry_preflight': gate})

    def test_changed_receipt_rejects_the_worker(self):
        gate = self.preflight()
        Path(gate['report']['path']).write_text('{}')
        with self.assertRaises(ValueError):
            discovery.require_native_entry_preflight(self.rendered({}, self.ready[0][1]),
                {**self.options, 'entry_preflight': gate})

    def test_main_does_not_create_a_pool_after_entry_failure(self):
        fixture = discovery_fixtures.FirstNativeRunTests('test_first_native_valid')
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        with self.assertRaisesRegex(ValueError, 'entry barrier refused'):
            fixture.invoke(fixture.first_arguments(), preflight_error=ValueError('entry barrier refused'))
        fixture.last_pool.assert_not_called()

    def test_main_requires_an_explicit_artifact_map(self):
        fixture = discovery_fixtures.FirstNativeRunTests('test_first_native_valid')
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        with self.assertRaises(SystemExit):
            fixture.invoke(fixture.first_arguments(), entry_artifacts=False)
        fixture.last_pool.assert_not_called()

    def test_primary_renderer_and_checker_stay_byte_equivalent(self):
        path = Path(successor_entailment.__file__)
        original = subprocess.check_output(['git', 'show', 'ccd89437:tools/block/successor_entailment.py'],
                                           cwd=path.parents[2], text=True)
        old, new = ast.parse(original), ast.parse(path.read_text())
        for name in ('native_boundary_source', 'check_boundary'):
            def function(tree):
                return next(row for row in tree.body if isinstance(row, (ast.FunctionDef, ast.AsyncFunctionDef))
                            and row.name == name)
            self.assertEqual(ast.dump(function(old)), ast.dump(function(new)))

    def test_existing_class_values_remain_exact(self):
        self.assertEqual(discovery.report_entry_class({'entry_class': 'propagate-only'}),
                         {'entry_class': 'propagate-only'})
        row = {'entry_pc': '0x10'}
        result = discovery.summarize(row, [{'outcome': 'setup-error', 'error': 'exact original failure',
                                           'proof_phase_entered': False}])
        self.assertEqual(row, {'entry_pc': '0x10'})
        self.assertEqual(result['setup_error'], 'exact original failure')
        self.assertEqual(result['entry_class'], 'unclassified-design-entry')

    def test_entry_refusal_survives_the_forbidden_fallback(self):
        gate = self.preflight()
        class Response:
            structuredContent = {'success': False, 'error': 'exact early refusal'}
            def model_dump(self, mode):
                return {'structuredContent': self.structuredContent,
                        'content': [{'type': 'text', 'text': 'full raw response'}]}
        class Session:
            async def __aenter__(self): return self
            async def __aexit__(self, *args): return False
            async def initialize(self): return Response()
            async def call_tool(self, tool, arguments): return Response()
        @asynccontextmanager
        async def transport(*args, **kwargs):
            yield (None, None)
        async def checker(session, *args, **kwargs):
            raw = await session.call_tool('rocq_start', {'theorem': 'entry'})
            return {'residual_class': 'entry_unavailable', 'failed_start': discovery.data(raw)}
        modules = {'mcp': SimpleNamespace(ClientSession=lambda *args: Session(),
                                         StdioServerParameters=lambda **kwargs: object()),
                   'mcp.client': SimpleNamespace(),
                   'mcp.client.stdio': SimpleNamespace(stdio_client=transport)}
        with patch.dict(sys.modules, modules), \
                patch.object(successor_entailment, 'native_boundary_source', side_effect=self.rendered), \
                patch.object(successor_entailment, 'check_boundary', side_effect=checker), \
                patch.object(discovery.chain_root, 'inherited_debts', return_value={}), \
                patch.object(discovery, 'fallback_designed_block', new=AsyncMock(side_effect=RuntimeError('fallback forbidden'))):
            with self.assertRaisesRegex(RuntimeError, 'fallback forbidden'):
                asyncio.run(discovery.probe_designed_block(*self.ready[0],
                    {**self.options, 'entry_preflight': gate}))
        base = self.root/'discovery/native/block_0x10'
        evidence = json.loads((base/'early-evidence.json').read_bytes())
        self.assertEqual(evidence['evidence']['failed_start']['error'], 'exact early refusal')
        raw = next((base/'early-calls').glob('*-rocq_start-raw.json'))
        self.assertEqual(json.loads(raw.read_bytes())['structuredContent']['error'], 'exact early refusal')


if __name__ == '__main__':
    unittest.main()
