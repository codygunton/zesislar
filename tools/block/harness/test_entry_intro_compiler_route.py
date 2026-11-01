"""Exercise the bounded compiler route without running a compiler."""
import asyncio
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'code'))
import entry_chain_provider as provider


PLUGIN = 'Declare ML Module "zesu-signature-gates.plugin".\n'
ENTRY = 'ZesuSsz.Automation.EntryIntro'
HOOKS = 'ZesuSsz.Automation.Hooks'
REFUSAL = dict(success=False, reason='validation',
               error=provider.ENTRYINTRO_MCP_REFUSAL, state_capture_status='no_position')


class EntryIntroCompilerRoute(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.workspace = Path(temporary.name)
        self.output = self.workspace / 'native'
        self.output.mkdir()
        self.source = self.workspace / 'EntryIntro.v'
        self.source.write_text(PLUGIN)
        self.runtime = dict(coqc_wrapper='tools/coqc.sh',
                            expected_mcp_flags=['-Q', str(self.workspace), 'Fixture'])
        self.environment = {'PATH': '/reviewed/bin'}
        self.recheck = Mock()
        self.call = AsyncMock(side_effect=provider.ToolFailure('MCP refused', dict(REFUSAL)))
        self.child = Mock()
        self.child.wait = AsyncMock(return_value=0)
        self.spawn = AsyncMock(return_value=self.child)
        patched = patch.object(asyncio, 'create_subprocess_exec', self.spawn)
        patched.start()
        self.addCleanup(patched.stop)

    async def compile(self, module=ENTRY):
        return await provider.compile_dependency(module, self.source, self.workspace,
            self.workspace / self.runtime['coqc_wrapper'], self.runtime['expected_mcp_flags'],
            self.output, self.environment, self.call, self.recheck, 100)

    async def test_exact_refusal_uses_the_existing_guarded_vector(self):
        value = await self.compile()
        self.call.assert_awaited_once_with('rocq_compile_file', dict(
            workspace=str(self.workspace), file=str(self.source), timeout=100,
            keep_vo=True, include_warnings=True))
        argv = [str(self.workspace / 'tools/coqc.sh'),
                *self.runtime['expected_mcp_flags'], str(self.source)]
        self.assertEqual(list(self.spawn.call_args.args), argv)
        self.assertEqual(self.spawn.call_args.kwargs['cwd'], self.workspace)
        self.assertIs(self.spawn.call_args.kwargs['env'], self.environment)
        self.assertEqual(self.recheck.call_count, 2)
        self.assertEqual(value['MCP_refusal_result'], REFUSAL)
        self.assertEqual(value, json.loads((self.output / 'ENTRYINTRO-COMPILE.json').read_text()))
        self.assertFalse((self.output / 'HOOKS-COMPILE.json').exists())

    async def test_mcp_success_never_uses_fallback(self):
        self.call = AsyncMock(return_value=dict(success=True))
        self.assertEqual(await self.compile(), dict(success=True))
        self.spawn.assert_not_called()
        self.assertFalse((self.output / 'ENTRYINTRO-COMPILE.json').exists())

    async def test_other_module_cannot_use_the_exact_refusal(self):
        with self.assertRaises(provider.ToolFailure):
            await self.compile('Other.Module')
        self.spawn.assert_not_called()

    async def test_every_different_refusal_stops_before_the_compiler(self):
        for changed in [dict(error='another error'), dict(reason='compile_error'),
                        dict(success=True), dict(state_capture_status='captured'),
                        dict(pet_restarted=True), dict(restarted=True)]:
            with self.subTest(changed=changed):
                self.call = AsyncMock(side_effect=provider.ToolFailure(
                    'MCP refused', dict(REFUSAL, **changed)))
                with self.assertRaises(provider.ToolFailure):
                    await self.compile()
        self.spawn.assert_not_called()

    async def test_wrong_or_duplicate_plugin_stops_before_mcp(self):
        for text in ['Declare ML Module "another.plugin".\n', PLUGIN * 2]:
            self.source.write_text(text)
            with self.assertRaisesRegex(ValueError, 'plugin declaration changed'):
                await self.compile()
        self.call.assert_not_called()
        self.spawn.assert_not_called()

    async def test_entry_without_plugin_keeps_mcp(self):
        self.source.write_text('Definition ordinary := 0.\n')
        self.call = AsyncMock(return_value=dict(success=True))
        self.assertEqual(await self.compile(), dict(success=True))
        self.spawn.assert_not_called()

    async def test_failed_binding_recheck_blocks_fallback(self):
        self.recheck.side_effect = ValueError('A source binding changed.')
        with self.assertRaisesRegex(ValueError, 'source binding changed'):
            await self.compile()
        self.spawn.assert_not_called()

    async def test_failed_compiler_preserves_its_distinct_receipt(self):
        self.child.wait.return_value = 1
        with self.assertRaises(provider.ToolFailure):
            await self.compile()
        receipt = json.loads((self.output / 'ENTRYINTRO-COMPILE.json').read_text())
        self.assertFalse(receipt['success'])
        self.assertEqual(receipt['returncode'], 1)
        self.assertEqual(receipt['MCP_refusal_result'], REFUSAL)

    async def test_hooks_and_entryintro_receipts_do_not_overwrite(self):
        await self.compile(HOOKS)
        hooks = (self.output / 'HOOKS-COMPILE.json').read_bytes()
        self.call.assert_not_called()
        await self.compile()
        self.assertEqual((self.output / 'HOOKS-COMPILE.json').read_bytes(), hooks)
        self.assertTrue((self.output / 'ENTRYINTRO-COMPILE.json').is_file())


if __name__ == '__main__':
    unittest.main()
