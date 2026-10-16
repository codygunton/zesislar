"""Distinguish exact inline catalogs from reserved chunk wrappers."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_kernel_artifacts import ArtifactReader
from trace_block_kernel_display import _exact


class ArtifactDispatchTests(unittest.TestCase):
    def catalog(self):
        return {'schema': 2, 'complete_sidecar': {'path': 'complete.marshal',
                'sha256': 'a' * 64, 'bytes': 10}, 'selected_ids': [1], 'entries': [{'id': 1}]}

    def read(self, value, wrapper=False, edit=None):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'evidence'; root.mkdir()
            def save(name, row):
                payload = json.dumps(row, sort_keys=True).encode(); (root / name).write_bytes(payload)
                return {'path': name, 'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': len(payload)}
            record = deepcopy(value)
            if wrapper:
                event = 'kernel-json/catalog.json'; text = json.dumps(value, sort_keys=True)
                raw = text.encode()
                leaf = save('leaf.json', {'schema': 2, 'kind': 'capture-leaf', 'logical_event': event,
                    'ordinal': 0, 'encoding': 'utf-8', 'text': text, 'text_bytes': len(raw),
                    'payload_sha256': hashlib.sha256(raw).hexdigest()})
                index = save('index.json', {'schema': 2, 'kind': 'capture-index', 'logical_event': event,
                    'level': 1, 'logical_bytes': len(raw), 'children': [dict(leaf, logical_bytes=len(raw))]})
                record = {'schema': 2, 'kind': 'kernel-json-artifact', 'logical_event': event,
                    'logical_sha256': hashlib.sha256(raw).hexdigest(),
                    'payload': {'encoding': 'json-chunks-v1', 'root': index, 'logical_bytes': len(raw)}}
            if edit: edit(record)
            reference = save('catalog.json', record)
            with ArtifactReader(root, Path(temporary) / 'index') as reader:
                return _exact(reader.read(reference), value)

    def test_exact_inline_catalog(self):
        self.assertTrue(self.read(self.catalog()))

    def test_legacy_inline_catalog(self):
        value = self.catalog(); value['schema'] = 1; value.pop('selected_ids')
        self.assertTrue(self.read(value))

    def test_chunked_compact_catalog(self):
        self.assertTrue(self.read(self.catalog(), wrapper=True))

    def test_unknown_inline_catalog_field_rejects(self):
        with self.assertRaises(ValueError): self.read(self.catalog(), edit=lambda r: r.update(extra=True))

    def test_missing_inline_catalog_field_rejects(self):
        with self.assertRaises(ValueError): self.read(self.catalog(), edit=lambda r: r.pop('selected_ids'))

    def test_missing_wrapper_kind_rejects(self):
        with self.assertRaises(ValueError): self.read(self.catalog(), wrapper=True, edit=lambda r: r.pop('kind'))

    def test_wrong_wrapper_kind_rejects(self):
        with self.assertRaises(ValueError):
            self.read(self.catalog(), wrapper=True, edit=lambda r: r.update(kind='foreign'))

    def test_unknown_wrapper_field_rejects(self):
        with self.assertRaises(ValueError):
            self.read(self.catalog(), wrapper=True, edit=lambda r: r.update(selected_ids=[1]))

    def test_changed_wrapper_identity_rejects(self):
        with self.assertRaises(ValueError):
            self.read(self.catalog(), wrapper=True, edit=lambda r: r.update(logical_event='foreign'))

    def test_changed_wrapper_logical_hash_rejects(self):
        with self.assertRaises(ValueError):
            self.read(self.catalog(), wrapper=True, edit=lambda r: r.update(logical_sha256='f' * 64))


if __name__ == '__main__':
    unittest.main()
