"""Verify the authorized LOAD and single fresh-start boundary."""
import asyncio
from contextlib import asynccontextmanager
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
import discovery


class LoadedEntryRetryTests(unittest.TestCase):
    def run_probe(self, load_outcome):
        events = []

        class Session:
            def __init__(self, *args):
                pass

            async def __aenter__(self):
                return self

            async def __aexit__(self, *args):
                pass

            async def initialize(self):
                pass

            async def call_tool(self, name, arguments):
                events.append(name)
                value = ({'ok': True, 'toolchain': {'pet': {'path': 'pinned-pet'}}}
                         if name == 'rocq_health' else
                         {'success': False, 'reason': 'timeout', 'error': 'start timeout'})
                return SimpleNamespace(structuredContent=value)

        @asynccontextmanager
        async def stdio(parameters):
            yield None, None

        def load(*args):
            events.append('LOAD')
            return {'outcome': load_outcome}

        with tempfile.TemporaryDirectory() as temporary:
            modules = {'mcp': SimpleNamespace(ClientSession=Session,
                StdioServerParameters=lambda **kwargs: kwargs),
                'mcp.client': SimpleNamespace(),
                'mcp.client.stdio': SimpleNamespace(stdio_client=stdio)}
            options = {'mcp_command': 'owned-server', 'workspace': temporary,
                       'out': temporary, 'build_dir': temporary, 'seconds': 300,
                       'terminal': '0x30', 'load_before_start': True,
                       'secondary_enabled': False, 'probe_targets': ['0x20']}
            record = {'outcome': 'setup-error', 'pending_goals': [], 'shelved_goals': []}
            with patch.dict(sys.modules, modules), \
                    patch.object(discovery.setup_fallback, 'run_one', side_effect=load), \
                    patch.object(discovery.chain_root, 'render_probe', return_value='Lemma infer_boundary : True.\nProof.\ntry zesu_block.\nAbort.\n'), \
                    patch.object(discovery.chain_root, 'parse_probe', return_value=[record]):
                result = asyncio.run(discovery.probe_block(
                    {'entry_pc': '0x10', 'entry_class': 'join'},
                    {'successors': ['0x20', '0x30']}, {}, options))
        return events, result

    def test_successful_load_permits_only_one_fresh_start(self):
        events, result = self.run_probe('entry-elaborated')
        self.assertEqual(events, ['rocq_health', 'LOAD', 'rocq_start'])
        self.assertEqual(result['outcomes'], ['primary-unavailable'])
        self.assertFalse(result['executed'])
        self.assertFalse(result['captures'][0]['contract_closed'])
        self.assertEqual(result['captures'][0]['setup_path'], 'coqc-scratch-LOAD/fresh-owned-Pet')
        self.assertEqual(result['secondary_diagnostics'], [])

    def test_failed_load_prevents_fresh_start(self):
        events, result = self.run_probe('load-failed')
        self.assertEqual(events, ['rocq_health', 'LOAD'])
        self.assertEqual(result['outcomes'], ['setup-error'])
        self.assertFalse(result['executed'])


if __name__ == '__main__':
    unittest.main()
