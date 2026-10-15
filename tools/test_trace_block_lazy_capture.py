"""Check disk indexes and lazy values against exact capture bytes."""

import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_chunks import ChunkReader
from trace_block_lazy_capture import LazyCapture
from trace_block_stream import json_document
from trace_block_text import StreamText
import test_trace_block_chunks as fixtures


class LazyCaptureTests(unittest.TestCase):
    setUp = fixtures.ChunkTests.setUp
    write = fixtures.ChunkTests.write
    leaf = fixtures.ChunkTests.leaf
    index = fixtures.ChunkTests.index
    envelope = fixtures.ChunkTests.envelope

    def capture(self, envelope, name='index.sqlite'):
        return LazyCapture(self.root, envelope, self.event, self.root / name)

    def test_nested_object_array_and_scalar_values(self):
        value = {'notation': {'goals': [{'evar': 7, 'hyps': [{'names': ['Hλ'], 'body': None}],
                                          'conclusion': 'P λ'}]}, 'defined': True, 'empty': []}
        raw = json.dumps(value, ensure_ascii=False)
        envelope = self.envelope([raw[:21], raw[21:55], raw[55:]])
        with self.capture(envelope) as capture:
            self.assertEqual(capture.root, value)
            self.assertEqual(capture.root['notation']['goals'][0]['evar'], 7)
            self.assertEqual(list(capture.root.keys()), list(value))
            self.assertEqual("".join(json_document(capture.root)),
                             json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n')

    def test_large_text_remains_lazy_and_renders_exactly(self):
        text = ('λ🦉\\"\n' * 17000)
        raw = json.dumps({'goal': text}, ensure_ascii=False)
        envelope = self.envelope([raw[i:i+50000] for i in range(0, len(raw), 50000)])
        with self.capture(envelope) as capture:
            field = capture.root['goal']
            self.assertIsInstance(field, StreamText)
            self.assertEqual(field, text)
            self.assertEqual("".join(json_document(capture.root)),
                             json.dumps({'goal': text}, ensure_ascii=False, sort_keys=True, indent=2) + '\n')

    def test_escaped_and_literal_unicode_keys(self):
        envelope = self.envelope(['{"\\u03bb":1,"🦉":2}'])
        with self.capture(envelope) as capture:
            self.assertEqual(capture.root['λ'], 1)
            self.assertEqual(capture.root['🦉'], 2)

    def test_duplicate_key_rejects(self):
        envelope = self.envelope(['{"same":1,"same":2}'])
        with self.assertRaisesRegex(ValueError, 'duplicate object key'):
            self.capture(envelope)

    def test_existing_index_cannot_substitute_structure(self):
        envelope = self.envelope(['{"a":1}'])
        with self.capture(envelope):
            pass
        with self.assertRaisesRegex(ValueError, 'already exists'):
            self.capture(self.envelope(['{"b":2}']))

    def test_chunk_change_after_index_is_detected(self):
        envelope = self.envelope(['{"goal":"before"}'])
        with self.capture(envelope) as capture:
            path = self.root / 'node-001.json'
            path.write_bytes(path.read_bytes() + b' ')
            with self.assertRaisesRegex(ValueError, 'reference'):
                capture.root['goal']

    def test_keys_and_array_bounds(self):
        envelope = self.envelope(['{"list":[1,2]}'])
        with self.capture(envelope) as capture:
            root = capture.root
            self.assertEqual(root.get('missing', 9), 9)
            self.assertNotIn('missing', root)
            with self.assertRaises(KeyError):
                root['missing']
            with self.assertRaises(IndexError):
                root['list'][2]
            self.assertEqual(root['list'][-1], 2)
            self.assertEqual(list(root['list'][::-1]), [2, 1])

    def test_readonly_protocols_never_hide_values(self):
        from collections.abc import Mapping, Sequence
        with self.capture(self.envelope(['{"a":[1,2],"b":true}'])) as capture:
            root = capture.root
            self.assertIsInstance(root, Mapping)
            self.assertIsInstance(root['a'], Sequence)
            self.assertIn(1, root['a'])
            self.assertEqual(root['a'].index(2), 1)
            self.assertEqual(root['a'].count(1), 1)
            self.assertEqual(dict(root), {'a': [1, 2], 'b': True})
            self.assertEqual(list(root['a']), [1, 2])
            with self.assertRaises(TypeError):
                json.dumps(root)
            with self.assertRaises(TypeError):
                json.dumps(root['a'])
            with self.assertRaises(AttributeError):
                root.copy()
            with self.assertRaises(AttributeError):
                root['a'].copy()
            with self.assertRaises(TypeError):
                root['new'] = 4
            with self.assertRaises(TypeError):
                root['a'][0] = 4

    def test_lazy_capture_uses_the_real_validator_and_renderers(self):
        import trace_block
        from trace_block_stream import build_stream_trace, markdown_chunks
        from test_trace_block import fixture
        request, result = fixture('return')
        ordinary = trace_block.build_trace(request, result)
        raw = json.dumps(result, ensure_ascii=False)
        envelope = self.envelope([raw[i:i+50000] for i in range(0, len(raw), 50000)])
        with self.capture(envelope) as capture:
            root = capture.root
            class View:
                header = {key: root[key] for key in root
                          if key not in ('points', 'snapshots', 'instruction_visits', 'residual')}
                header['coverage'] = dict(header['coverage'])
                snapshot_keys = tuple(root['snapshots'])
                residual = root['residual']

                def iter_points(self):
                    return iter(root['points'])

                def iter_instruction_visits(self):
                    return iter(root['instruction_visits'])

                def get_snapshot(self, key):
                    return root['snapshots'][key]

            trace = build_stream_trace(request, View())
            self.assertTrue(trace['completion']['trace_complete'])
            self.assertEqual(''.join(json_document(trace)).encode(), trace_block.json_bytes(ordinary))
            self.assertEqual(''.join(markdown_chunks(trace)), trace_block.render_markdown(ordinary))

    def test_byte_ranges_cross_unicode_leaf_boundary(self):
        envelope = self.envelope(['["λ', '🦉",12]'])
        reader = ChunkReader(self.root)
        reader.validate(envelope, self.event)
        expected = '["λ🦉",12]'.encode()
        for start in range(len(expected)):
            for stop in range(start, len(expected) + 1):
                self.assertEqual(b''.join(reader.iter_bytes_range(envelope, self.event, start, stop)), expected[start:stop])


if __name__ == '__main__':
    unittest.main()
