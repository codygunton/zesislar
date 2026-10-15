"""Check streamed text validation and exact JSON/Markdown rendering."""

import copy
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
import trace_block
from trace_block_stream import json_document, markdown_chunks
from trace_block_text import StreamText, chunk_string, iter_json_string
import test_trace_block_chunks as fixtures
from test_trace_block import fixture


class TextTests(unittest.TestCase):
    setUp = fixtures.ChunkTests.setUp
    write = fixtures.ChunkTests.write
    leaf = fixtures.ChunkTests.leaf
    index = fixtures.ChunkTests.index
    envelope = fixtures.ChunkTests.envelope

    def test_chunk_json_string_decodes_losslessly(self):
        envelope = self.envelope(['"a\\n\\uD83D', '\\uDC08\\t', 'λ\\\\\\\"b"'])
        value = chunk_string(self.root, envelope, self.event)
        expected = 'a\n🐈\tλ\\"b'
        self.assertEqual(value, expected)
        self.assertEqual("".join(value.iter_text()), expected)
        self.assertEqual("".join(json_document({"text": value})),
                         json.dumps({"text": expected}, sort_keys=True, indent=2, ensure_ascii=False) + "\n")

    def test_invalid_string_and_surrogates_reject(self):
        for raw in ('null', '"\\ud800"', '"\\udc00"', '"\\ud800\\u0000"', '"x" false', '"\\q"', '"unterminated'):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                list(iter_json_string(io.StringIO(raw)))

    def test_truncation_crosses_fragment_boundaries(self):
        for parts in (('a.', '..b'), ('a', '…', 'b'), (' ', 'HID', 'DEN', '\n')):
            self.assertFalse(StreamText(lambda: iter(parts)).complete_text())
        for parts in (('complete',), ('HID ', 'DEN'), ('', ''), ('HID\u00a0', 'DEN')):
            self.assertTrue(StreamText(lambda: iter(parts)).complete_text())

    def test_equality_ignores_fragment_boundaries(self):
        left = StreamText(lambda: iter(('ab', '', 'cd')))
        right = StreamText(lambda: iter(('a', 'bcd')))
        self.assertEqual(left, right)
        self.assertNotEqual(left, 'abcde')
        self.assertEqual(copy.deepcopy(left), left)

    def test_streamed_goal_matches_fixture_bytes(self):
        request, result = fixture('return')
        original = trace_block.build_trace(request, result)
        streamed = copy.deepcopy(original)
        text = original['points'][0]['goal']
        streamed['points'][0]['goal'] = StreamText(lambda: iter((text[:3], text[3:])))
        self.assertEqual("".join(json_document(streamed)).encode(), trace_block.json_bytes(original))
        self.assertEqual("".join(markdown_chunks(streamed)), trace_block.render_markdown(original))

    def test_full_text_validator_reads_all_fragments(self):
        errors = []
        trace_block._full_text(StreamText(lambda: iter(('prefix', '...', 'tail'))), 'goal', errors)
        self.assertEqual(errors, ['goal contains truncated or hidden text.'])
        errors = []
        trace_block._all_text({'message': StreamText(lambda: iter(('HID', 'DEN')))}, 'feedback', errors)
        self.assertEqual(errors, ['feedback/message contains truncated or hidden text.'])

    def test_string_decoder_reads_complete_chunk_totals(self):
        envelope = self.envelope(['"ok"', ''])
        envelope['logical_bytes'] += 1
        with self.assertRaisesRegex(ValueError, 'total'):
            list(chunk_string(self.root, envelope, self.event).iter_text())


if __name__ == '__main__':
    unittest.main()
