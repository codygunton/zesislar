"""Check exact text rendering from bounded capture chunks."""

import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_chunk_render import write_capture_documents
import test_trace_block_chunks as fixtures


class RenderTests(unittest.TestCase):
    setUp = fixtures.ChunkTests.setUp
    write = fixtures.ChunkTests.write
    leaf = fixtures.ChunkTests.leaf
    index = fixtures.ChunkTests.index
    envelope = fixtures.ChunkTests.envelope
    def test_render_exact_json_and_full_fence(self):
        texts = ['{"goal":"', '``` λ', '","evars":[]}']
        envelope = self.envelope(texts)
        output = self.root / "output"
        result = write_capture_documents(self.root, envelope, self.event, output)
        raw = "".join(texts).encode()
        self.assertEqual((output / "CAPTURE.json").read_bytes(), raw)
        self.assertEqual((output / "CAPTURE.md").read_bytes(), b"````\n" + raw + b"\n````\n")
        self.assertEqual(result["CAPTURE.json"]["sha256"], hashlib.sha256(raw).hexdigest())

    def test_invalid_capture_publishes_no_documents(self):
        envelope = self.envelope(['{"broken":}'])
        output = self.root / "output"
        with self.assertRaises(ValueError):
            write_capture_documents(self.root, envelope, self.event, output)
        self.assertFalse((output / "CAPTURE.json").exists())
        self.assertFalse((output / "CAPTURE.md").exists())

    def test_render_is_deterministic(self):
        envelope = self.envelope(['{"a":"λ"}'])
        first, second = self.root / "first", self.root / "second"
        self.assertEqual(write_capture_documents(self.root, envelope, self.event, first),
                         write_capture_documents(self.root, envelope, self.event, second))
        for name in ("CAPTURE.json", "CAPTURE.md"):
            self.assertEqual((first / name).read_bytes(), (second / name).read_bytes())


if __name__ == "__main__":
    unittest.main()
