import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import recover_native_inputs as recovery
import retry_unavailable
from archive_discovery import store


class RecoveryTests(unittest.TestCase):
    def test_cache_symlink_is_replaced_without_writing_target(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            owned = root/'owned'
            owned.mkdir()
            shared = root/'shared'
            shared.write_bytes(b'current')
            local = owned/'test.vo'
            local.symlink_to(shared)
            frozen = store(str(root/'archive'), b'frozen')
            result = recovery.recover(local, frozen, owned, str(root/'archive'))
            self.assertFalse(local.is_symlink())
            self.assertEqual(local.read_bytes(), b'frozen')
            self.assertEqual(shared.read_bytes(), b'current')
            self.assertEqual(Path(result['previous']['archive_path']).read_bytes(), b'current')

    def test_shared_inode_is_replaced_without_writing_other_link(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            owned = root/'owned'
            owned.mkdir()
            shared = root/'shared'
            shared.write_bytes(b'current')
            local = owned/'test.vo'
            os.link(shared, local)
            frozen = store(str(root/'archive'), b'frozen')
            recovery.recover(local, frozen, owned, str(root/'archive'))
            self.assertNotEqual(local.stat().st_ino, shared.stat().st_ino)
            self.assertEqual(local.read_bytes(), b'frozen')
            self.assertEqual(shared.read_bytes(), b'current')

    def test_wrong_archive_hash_and_unowned_path_are_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            root = Path(root)
            owned = root/'owned'
            owned.mkdir()
            local = owned/'test.vo'
            local.write_bytes(b'current')
            record = store(str(root/'archive'), b'frozen')
            with self.assertRaisesRegex(ValueError, 'archive hash'):
                recovery.recover(local, {**record, 'sha256': '0'*64}, owned, str(root/'archive'))
            with self.assertRaisesRegex(ValueError, 'outside'):
                recovery.recover(local, record, owned/'other', str(root/'archive'))
            self.assertEqual(local.read_bytes(), b'current')

    def test_retry_excludes_entered_baseline_entries(self):
        baseline = {'blocks': [{'arm': 'switch-on', 'entry': 'A', 'outcomes': ['primary-unavailable']},
                               {'arm': 'switch-on', 'entry': 'B', 'outcomes': ['reached']},
                               {'arm': 'switch-off', 'entry': 'C', 'outcomes': ['primary-unavailable']}]}
        self.assertEqual(retry_unavailable.selected_entries(baseline, 'switch-on'), {'A'})
