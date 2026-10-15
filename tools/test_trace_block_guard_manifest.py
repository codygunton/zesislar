"""Check exact guard bindings before build and transport startup."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_prepare import install_guard_manifest, guard_manifest_environment


class GuardManifestTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.workspace = Path(self.directory.name)
        self.descriptors = {"ReturnRoute.normalize": {"rule": "ReturnRoute", "commands": {}}}

    def test_install_and_repeat_are_exact(self):
        ref = install_guard_manifest(self.workspace, self.descriptors)
        self.assertEqual(ref, install_guard_manifest(self.workspace, self.descriptors))
        self.assertEqual(guard_manifest_environment(self.workspace, self.descriptors, ref),
                         {"ZESU_TRACE_GUARD_MANIFEST": ref["path"]})
        value = json.loads(Path(ref['path']).read_text())
        self.assertEqual(value['schema'], 2)
        self.assertEqual(set(value['clients']), {'ReturnRoute.normalize'})

    def test_changed_bytes_reject(self):
        ref = install_guard_manifest(self.workspace, self.descriptors)
        Path(ref['path']).write_text('{}')
        with self.assertRaisesRegex(ValueError, 'does not match'):
            guard_manifest_environment(self.workspace, self.descriptors, ref)
        with self.assertRaisesRegex(ValueError, 'immutable'):
            install_guard_manifest(self.workspace, self.descriptors)

    def test_changed_client_set_rejects(self):
        ref = install_guard_manifest(self.workspace, self.descriptors)
        other = {'ReturnRoute.fault': {'rule': 'ReturnRoute', 'commands': {}}}
        with self.assertRaisesRegex(ValueError, 'descriptors'):
            guard_manifest_environment(self.workspace, other, ref)

    def test_external_path_rejects(self):
        with tempfile.TemporaryDirectory() as other:
            ref = install_guard_manifest(Path(other), self.descriptors)
            with self.assertRaisesRegex(ValueError, 'leaves'):
                guard_manifest_environment(self.workspace, self.descriptors, ref)

    def test_symlink_rejects(self):
        ref = install_guard_manifest(self.workspace, self.descriptors)
        link = self.workspace / 'link.json'
        link.symlink_to(ref['path'])
        with self.assertRaisesRegex(ValueError, 'leaves'):
            guard_manifest_environment(self.workspace, self.descriptors, dict(ref, path=str(link)))


if __name__ == '__main__':
    unittest.main()
