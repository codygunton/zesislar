"""Check reflink copies on the repository filesystem and refusal without a full copy."""

import errno
import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_janitor
import reflink_copy as R

TOOLS = Path(__file__).resolve().parent


def shared(path):
    descriptor = os.open(path, os.O_RDONLY)
    try:
        return any(flags & build_janitor.EXTENT_SHARED
                   for _, _, flags in build_janitor.extents(descriptor))
    finally:
        os.close(descriptor)


class ReflinkCopy(unittest.TestCase):
    def setUp(self):
        # /tmp may not support reflinks; the repository's _build is on /home (XFS).
        parent = TOOLS.parent / '_build'
        parent.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix='reflink-copy-', dir=parent)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / 'RUNTIME.json'
        self.source.write_bytes(os.urandom(2 << 20))
        self.source.chmod(0o640)
        os.utime(self.source, ns=(1700000000000000000, 1700000001000000000))

    def test_copy_shares_extents_and_keeps_metadata(self):
        try:
            target = R.reflink_copy(self.source, self.root / 'copy.json')
        except R.ReflinkError as error:
            self.skipTest(f'no reflink support: {error}')
        self.assertEqual(target.read_bytes(), self.source.read_bytes())
        self.assertNotEqual(target.stat().st_ino, self.source.stat().st_ino)
        self.assertEqual(target.stat().st_mtime_ns, self.source.stat().st_mtime_ns)
        self.assertEqual(target.stat().st_mode, self.source.stat().st_mode)
        self.assertTrue(shared(self.source))
        self.assertTrue(shared(target))
        with target.open('r+b') as stream:
            stream.write(b'CHANGED')
        self.assertNotEqual(target.read_bytes()[:7], self.source.read_bytes()[:7])

    def test_copy_into_a_directory_uses_the_source_name(self):
        (self.root / 'run').mkdir()
        try:
            target = R.reflink_copy(self.source, self.root / 'run')
        except R.ReflinkError as error:
            self.skipTest(f'no reflink support: {error}')
        self.assertEqual(target, self.root / 'run/RUNTIME.json')

    def test_refusal_is_clear_and_leaves_no_copy(self):
        target = self.root / 'copy.json'
        target.write_bytes(b'old')
        with patch.object(R.fcntl, 'ioctl', side_effect=OSError(errno.EOPNOTSUPP, 'unsupported')), \
                patch.object(R.shutil, 'copyfile') as full_copy:
            with self.assertRaises(R.ReflinkError) as raised:
                R.reflink_copy(self.source, target)
        full_copy.assert_not_called()
        self.assertIn('No full copy was made', str(raised.exception))
        self.assertEqual(raised.exception.errno, errno.EOPNOTSUPP)
        self.assertEqual(target.read_bytes(), b'old')
        self.assertEqual(list(self.root.glob('.*.reflink-*')), [])

    def test_symbolic_destination_and_missing_source_refuse(self):
        link = self.root / 'link.json'
        link.symlink_to(self.source)
        with self.assertRaises(R.ReflinkError):
            R.reflink_copy(self.source, link)
        with self.assertRaises(R.ReflinkError):
            R.reflink_copy(self.root / 'missing.json', self.root / 'copy.json')

    def test_reference_names_the_path_and_digest(self):
        value = R.reference(self.source)
        self.assertEqual(value['path'], str(self.source.resolve()))
        self.assertEqual(value['sha256'], hashlib.sha256(self.source.read_bytes()).hexdigest())


if __name__ == '__main__':
    unittest.main()
