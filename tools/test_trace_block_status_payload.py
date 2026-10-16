"""Bind selected feedback to exact owned status bytes."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / 'block'))
from trace_block_selected_feedback import raw_policy, checked_status_payload


class StatusPayloadTests(unittest.TestCase):
    def test_legacy_absent_policy(self):
        self.assertIsNone(raw_policy({}))
        self.assertIsNone(raw_policy({'observer_runtime': {}}))

    def test_new_policy(self):
        self.assertEqual(raw_policy({'observer_runtime': {'raw_policy': 'trigger-selected-raw-v2'}}),
                         'trigger-selected-raw-v2')

    def test_malformed_runtime_rejects(self):
        for value in (None, [], 'bounded'):
            with self.assertRaises(ValueError):
                raw_policy({'observer_runtime': value})

    def test_unsupported_policy_rejects(self):
        for value in (None, '', 'trigger-selected-raw-v3'):
            with self.assertRaises(ValueError):
                raw_policy({'observer_runtime': {'raw_policy': value}})

    def payload(self, root, content=b'{"accepted":true}'):
        path = root / 'capture.json'
        path.write_bytes(content)
        return {'path': str(path), 'sha256': hashlib.sha256(content).hexdigest()}

    def test_exact_payload(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            response = self.payload(root)
            self.assertEqual(checked_status_payload(root, response), {'accepted': True})

    def test_substituted_bytes_reject(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            response = self.payload(root)
            Path(response['path']).write_text('{"accepted":false}')
            with self.assertRaises(ValueError):
                checked_status_payload(root, response)

    def test_foreign_path_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owned = root / 'evidence'
            owned.mkdir()
            response = self.payload(root)
            with self.assertRaises(ValueError):
                checked_status_payload(owned, response)

    def test_symlink_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            response = self.payload(root)
            alias = root / 'alias.json'
            alias.symlink_to(response['path'])
            response['path'] = str(alias)
            with self.assertRaises(ValueError):
                checked_status_payload(root, response)

    def test_duplicate_field_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            response = self.payload(root, b'{"accepted":true,"accepted":false}')
            with self.assertRaises(ValueError):
                checked_status_payload(root, response)

    def test_oversized_payload_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            response = self.payload(root, b' ' * (2 * 1024 * 1024 + 1))
            with self.assertRaises(ValueError):
                checked_status_payload(root, response)


if __name__ == '__main__':
    unittest.main()
