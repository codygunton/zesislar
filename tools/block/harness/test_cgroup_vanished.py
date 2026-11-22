"""Nonproof tests: a control group removed while it is sampled counts as closed, not as a read failure."""
import errno
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M


class VanishingReader(M.ScopeReader):
    """Removes the sampled group right after its identity is read (the compile's scope ends meanwhile)."""
    def directory(self, path):
        identity = super().directory(path)
        shutil.rmtree(path)
        return identity


class CgroupVanishedTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp()).resolve()
        self.addCleanup(shutil.rmtree, self.root, ignore_errors=True)
        self.reader = VanishingReader(cgroup_root=self.root, uid=1000)
        self.reader.parent.mkdir(parents=True)

    def group(self, name):
        path = self.reader.parent / name
        path.mkdir()
        (path / 'cgroup.events').write_text('populated 1\nfrozen 0\n')
        (path / 'memory.current').write_text('4096\n')
        info = path.stat()
        return dict(scope=str(path), device=info.st_dev, inode=info.st_ino)

    def test_leaf_removed_during_sampling_is_closed(self):
        bound = self.group('leaf.scope')
        self.assertIs(M.leaf_closed(self.reader, bound), True)
        self.assertFalse(Path(bound['scope']).exists())

    def test_leaf_reporting_enodev_is_closed(self):
        bound = self.group('leaf.scope')
        reader = M.ScopeReader(cgroup_root=self.root, uid=1000)
        with patch.object(Path, 'read_text', side_effect=OSError(errno.ENODEV, 'No such device')):
            self.assertIs(M.leaf_closed(reader, bound), True)

    def test_leaf_other_read_error_still_raises(self):
        bound = self.group('leaf.scope')
        reader = M.ScopeReader(cgroup_root=self.root, uid=1000)
        with patch.object(Path, 'read_text', side_effect=OSError(errno.EACCES, 'Permission denied')):
            with self.assertRaises(PermissionError):
                M.leaf_closed(reader, bound)

    def test_populated_leaf_stays_open(self):
        bound = self.group('leaf.scope')
        reader = M.ScopeReader(cgroup_root=self.root, uid=1000)
        self.assertIs(M.leaf_closed(reader, bound), False)

    def test_aggregate_removed_during_sampling_is_closed(self):
        bound = self.group('zesuworkloads-aggregate1000p1r1.slice')
        row = self.reader.residual(bound)
        self.assertEqual(row, {'verified': True, 'closed': True, 'live_bytes': 0})

    def test_aggregate_reporting_enodev_is_closed(self):
        bound = self.group('zesuworkloads-aggregate1000p1r1.slice')
        reader = M.ScopeReader(cgroup_root=self.root, uid=1000)
        with patch.object(Path, 'read_text', side_effect=OSError(errno.ENODEV, os.strerror(errno.ENODEV))):
            self.assertEqual(reader.residual(bound), {'verified': True, 'closed': True, 'live_bytes': 0})


if __name__ == '__main__':
    unittest.main()
