"""Retain raw SDK responses before parsing, cancellation, or worker failure."""
import asyncio
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import AsyncMock, patch

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from call_journal import ToolJournal


class CallJournalTests(unittest.IsolatedAsyncioTestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)/'calls'
        self.journal = ToolJournal(self.directory)

    async def test_request_precedes_transport_and_raw_content_remains_exact(self):
        response = {'structuredContent': {'success': False},
                    'content': [{'type': 'text', 'text': 'full raw refusal α'}]}
        async def operation(tool, arguments):
            request = json.loads((self.directory/'0001-rocq_start-request.json').read_bytes())
            self.assertEqual(request['arguments'], arguments)
            return response
        session = type('Session', (), {})()
        session.call_tool = operation
        returned = await self.journal.call_tool(session, 'rocq_start', {'theorem': 'exact'})
        self.assertIs(returned, response)
        self.assertEqual(json.loads((self.directory/'0001-rocq_start-raw.json').read_bytes()), response)

    async def test_transport_exception_retains_request_without_a_fabricated_response(self):
        session = type('Session', (), {'call_tool': AsyncMock(side_effect=ConnectionError('exact transport'))})()
        with self.assertRaisesRegex(ConnectionError, 'exact transport'):
            await self.journal.call_tool(session, 'rocq_start', {})
        self.assertTrue((self.directory/'0001-rocq_start-request.json').is_file())
        self.assertFalse((self.directory/'0001-rocq_start-raw.json').exists())
        self.assertEqual(json.loads((self.directory/'0001-rocq_start-exception.json').read_bytes())['error'], 'exact transport')

    async def test_cancelled_call_remains_recorded(self):
        session = type('Session', (), {'call_tool': AsyncMock(side_effect=asyncio.CancelledError())})()
        with self.assertRaises(asyncio.CancelledError):
            await self.journal.call_tool(session, 'rocq_start', {})
        value = json.loads((self.directory/'0001-rocq_start-exception.json').read_bytes())
        self.assertEqual(value['type'], 'CancelledError')

    async def test_retention_failure_blocks_later_external_calls(self):
        session = type('Session', (), {'call_tool': AsyncMock(return_value={'success': True})})()
        with patch('call_journal.os.fsync', side_effect=OSError('disk failure')):
            with self.assertRaisesRegex(OSError, 'disk failure'):
                await self.journal.call_tool(session, 'rocq_start', {})
        with self.assertRaisesRegex(RuntimeError, 'No further MCP call'):
            await self.journal.call_tool(session, 'rocq_diag', {})
        session.call_tool.assert_not_called()

    async def test_response_files_cannot_be_overwritten(self):
        session = type('Session', (), {'call_tool': AsyncMock(return_value={'success': False})})()
        await self.journal.call_tool(session, 'rocq_start', {})
        before = (self.directory/'0001-rocq_start-raw.json').read_bytes()
        with self.assertRaises(FileExistsError):
            self.journal._write('0001-rocq_start-raw.json', {'changed': True})
        self.assertEqual((self.directory/'0001-rocq_start-raw.json').read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
