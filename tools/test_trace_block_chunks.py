"""Exercise the bounded, lossless capture reader with portable files."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_chunks import ChunkReader, MAX_RECORD_BYTES, MAX_TEXT_BYTES


class ChunkTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.event = "fixture-entry-1"
        self.serial = 0

    def write(self, node):
        self.serial += 1
        path = self.root / ("node-%03d.json" % self.serial)
        raw = (json.dumps(node, ensure_ascii=False, sort_keys=True) + "\n").encode()
        path.write_bytes(raw)
        return {"path": path.name, "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}

    def leaf(self, text, ordinal):
        raw = text.encode()
        return self.write({"schema": 2, "kind": "capture-leaf", "logical_event": self.event,
                           "ordinal": ordinal, "encoding": "utf-8", "text": text,
                           "text_bytes": len(raw), "payload_sha256": hashlib.sha256(raw).hexdigest()})

    def index(self, children, level=1):
        return self.write({"schema": 2, "kind": "capture-index", "logical_event": self.event,
                           "level": level, "children": children,
                           "logical_bytes": sum(child["logical_bytes"] for child in children)})

    def envelope(self, texts):
        children = [dict(self.leaf(text, index), logical_bytes=len(text.encode()))
                    for index, text in enumerate(texts)]
        return {"encoding": "json-chunks-v1", "root": self.index(children),
                "logical_bytes": sum(child["logical_bytes"] for child in children)}

    def reject(self, envelope, message=None):
        with self.assertRaisesRegex(ValueError, message or "."):
            ChunkReader(self.root).validate(envelope, self.event)

    def mutate(self, reference, update):
        node = json.loads((self.root / reference["path"]).read_text())
        update(node)
        return self.write(node)

    def test_lossless_unicode_escaping_and_boundaries(self):
        texts = ['{"message":"', 'λ\\n\\u263a', '","body":[true,null,1.25]}']
        envelope = self.envelope(texts)
        reader = ChunkReader(self.root)
        reader.validate(envelope, self.event)
        self.assertEqual("".join(reader.iter_text(envelope, self.event)), "".join(texts))
        with reader.open_text(envelope, self.event) as stream:
            self.assertEqual("".join(iter(lambda: stream.read(3), "")), "".join(texts))

    def test_two_index_levels(self):
        children = [dict(self.leaf(text, i), logical_bytes=len(text)) for i, text in enumerate(['[', '0', ']'])]
        branches = [dict(self.index(children[:1]), logical_bytes=1),
                    dict(self.index(children[1:]), logical_bytes=2)]
        envelope = {"encoding": "json-chunks-v1", "root": self.index(branches, 2), "logical_bytes": 3}
        ChunkReader(self.root).validate(envelope, self.event)

    def test_deterministic_bytes(self):
        envelope = self.envelope(['{"x":', '1}'])
        reader = ChunkReader(self.root)
        first = "".join(reader.iter_text(envelope, self.event)).encode()
        self.assertEqual(first, "".join(reader.iter_text(envelope, self.event)).encode())
        self.assertEqual(first, b'{"x":1}')

    def test_corrupt_file(self):
        envelope = self.envelope(['null'])
        path = self.root / envelope["root"]["path"]
        path.write_bytes(path.read_bytes() + b" ")
        self.reject(envelope, "reference")

    def test_missing_chunk(self):
        envelope = self.envelope(['null'])
        (self.root / "node-001.json").unlink()
        self.reject(envelope, "missing")

    def test_reordered_leaves(self):
        envelope = self.envelope(['[', '1]'])
        envelope["root"] = self.mutate(envelope["root"], lambda node: node["children"].reverse())
        self.reject(envelope, "ordinals")

    def test_payload_hash(self):
        reference = self.leaf('null', 0)
        reference = self.mutate(reference, lambda node: node.update(payload_sha256="0" * 64))
        self.reject({"encoding": "json-chunks-v1", "root": reference, "logical_bytes": 4}, "payload hash")

    def test_wrong_logical_event(self):
        envelope = self.envelope(['null'])
        with self.assertRaisesRegex(ValueError, "different logical event"):
            list(ChunkReader(self.root).iter_text(envelope, "other"))

    def test_wrong_total_and_child_counts(self):
        envelope = self.envelope(['null'])
        wrong = copy.deepcopy(envelope)
        wrong["logical_bytes"] += 1
        self.reject(wrong, "total")
        envelope["root"] = self.mutate(envelope["root"],
                                       lambda node: node["children"][0].update(logical_bytes=3))
        self.reject(envelope, "child reference")

    def test_oversized_text(self):
        reference = self.leaf('"' + 'x' * MAX_TEXT_BYTES + '"', 0)
        self.reject({"encoding": "json-chunks-v1", "root": reference,
                     "logical_bytes": MAX_TEXT_BYTES + 2}, "text byte limit")

    def test_oversized_serialized_metadata(self):
        envelope = self.envelope(['null'])
        path = self.root / envelope["root"]["path"]
        path.write_bytes(b" " * (MAX_RECORD_BYTES + 1))
        self.reject(envelope, "serialized byte limit")

    def test_child_limit(self):
        leaf = dict(self.leaf('null', 0), logical_bytes=4)
        root = self.index([leaf] * 257)
        self.reject({"encoding": "json-chunks-v1", "root": root, "logical_bytes": 1028}, "child limit")

    def test_unknown_fields_and_encoding(self):
        envelope = self.envelope(['null'])
        bad = dict(envelope, invented=True)
        self.reject(bad, "unsupported fields")
        envelope["encoding"] = "gzip"
        self.reject(envelope, "unsupported")

    def test_invalid_json_and_trailing_value(self):
        for texts in (['{"x":}'], ['null true'], ['"\\q"'], ['[1,]']):
            with self.subTest(texts=texts):
                self.reject(self.envelope(texts))

    def test_path_escape_and_symlink(self):
        envelope = self.envelope(['null'])
        envelope["root"]["path"] = "../outside.json"
        self.reject(envelope, "leaves")
        envelope = self.envelope(['null'])
        target = self.root / envelope["root"]["path"]
        link = self.root / "link.json"
        link.symlink_to(target)
        envelope["root"]["path"] = link.name
        self.reject(envelope, "symlink")

    def test_level_mismatch_and_boolean_integer(self):
        envelope = self.envelope(['null'])
        envelope["root"] = self.mutate(envelope["root"], lambda node: node.update(level=2))
        self.reject(envelope, "level")
        envelope = self.envelope(['null'])
        envelope["logical_bytes"] = True
        self.reject(envelope, "integer")

    def test_unbounded_read_rejects(self):
        envelope = self.envelope(['null'])
        with ChunkReader(self.root).open_text(envelope, self.event) as stream:
            with self.assertRaisesRegex(ValueError, "bounded"):
                stream.read()

    def test_empty_leaf_does_not_hide_tail_validation(self):
        envelope = self.envelope(['', 'null', ''])
        ChunkReader(self.root).validate(envelope, self.event)
        envelope['logical_bytes'] = 3
        self.reject(envelope, 'total')


if __name__ == "__main__":
    unittest.main()
