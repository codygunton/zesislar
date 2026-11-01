"""Exercise validation reuse with nonproof supplier evidence."""
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import supplier_ready as supplier
from binding_cache import force_hashing
from test_supplier_ready import SupplierReady


class SupplierMemo(unittest.TestCase):
    def setUp(self):
        self.fixture = SupplierReady()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        supplier._MEMO.clear()
        self.binding = self.fixture.freeze()
        self.full = patch.object(supplier, '_validate', wraps=supplier._validate).start()
        self.addCleanup(patch.stopall)

    def test_unchanged_and_result_isolation(self):
        result = supplier.validate(self.binding)
        result['ready']['bindings'].clear()
        self.assertTrue(supplier.validate(self.binding)['ready']['bindings'])
        self.assertEqual(self.full.call_count, 1)

    def test_packet_source_object_and_lineage_mutations_refuse(self):
        for path in [Path(self.binding['path']),
                     Path(self.fixture.modules[0]['source']['path']),
                     Path(self.fixture.modules[0]['object']['path']),
                     Path(self.fixture.manifest['closure']['path'])]:
            with self.subTest(path=path):
                supplier._MEMO.clear()
                original = path.read_bytes()
                supplier.validate(self.binding)
                before = path.stat()
                path.write_bytes(original + b' ')
                os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                with self.assertRaises(ValueError):
                    supplier.validate(self.binding)
                path.write_bytes(original)

    def test_atomic_replacement_revalidates_matching_bytes(self):
        supplier.validate(self.binding)
        path = Path(self.fixture.modules[0]['object']['path'])
        replacement = path.with_suffix('.replacement')
        replacement.write_bytes(path.read_bytes())
        replacement.replace(path)
        supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, 2)

    def test_chmod_revalidates(self):
        supplier.validate(self.binding)
        path = Path(self.fixture.modules[0]['source']['path'])
        path.chmod(path.stat().st_mode ^ 0o100)
        supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, 2)

    def test_final_symlink_retarget_refuses(self):
        supplier.validate(self.binding)
        path = Path(self.fixture.modules[0]['object']['path'])
        target = path.with_suffix('.original')
        path.rename(target)
        path.symlink_to(target)
        other = target.with_suffix('.other')
        other.write_bytes(b'changed')
        path.unlink()
        path.symlink_to(other)
        with self.assertRaises(ValueError):
            supplier.validate(self.binding)

    def test_parent_alias_retarget_refuses(self):
        fixture = self.fixture
        supplier.validate(self.binding)
        directory = fixture.workspace / 'Library'
        original = fixture.root / 'original-library'
        directory.rename(original)
        directory.symlink_to(original, target_is_directory=True)
        other = fixture.root / 'other-library'
        other.mkdir()
        (other / 'Dependency.v').write_text('changed')
        (other / 'Dependency.vo').write_bytes(b'changed')
        directory.unlink()
        directory.symlink_to(other, target_is_directory=True)
        with self.assertRaises(ValueError):
            supplier.validate(self.binding)

    def test_forced_validation_bypasses_memo(self):
        supplier.validate(self.binding)
        with force_hashing(True):
            supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, 2)

    def test_failure_is_not_cached(self):
        path = Path(self.fixture.modules[0]['object']['path'])
        original = path.read_bytes()
        path.write_bytes(b'changed')
        with self.assertRaises(ValueError):
            supplier.validate(self.binding)
        path.write_bytes(original)
        supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, 2)

    def test_change_during_hit_discards_result(self):
        supplier.validate(self.binding)
        original = supplier.deepcopy
        path = Path(self.fixture.modules[0]['object']['path'])
        def raced(value):
            result = original(value)
            path.write_bytes(b'changed')
            return result
        with patch.object(supplier, 'deepcopy', side_effect=raced):
            with self.assertRaises(ValueError):
                supplier.validate(self.binding)

    def test_process_change_drops_cache_before_lock(self):
        supplier.validate(self.binding)
        with patch.object(supplier.os, 'getpid', return_value=os.getpid() + 1):
            supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, 2)

    def test_raw_mapping_alias_retarget_revalidates_and_refuses(self):
        fixture = self.fixture
        row = fixture.external_installation()
        alias = fixture.root / 'installed-alias'
        alias.symlink_to(Path(row['source']['path']).parents[1], target_is_directory=True)
        fixture.flags[-2] = str(alias)
        fixture.manifest['ready'] = fixture.save('READY-RUNTIME.json', fixture.ready)
        fixture.manifest['runtime'] = fixture.save('jobs/prerequisites/RUNTIME.json', fixture.inner)
        self.binding = fixture.freeze()
        for _ in range(3):
            supplier.validate(self.binding)
            if supplier._MEMO:
                break
        self.assertTrue(supplier._MEMO)
        before = self.full.call_count
        supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, before)
        other = fixture.root / 'empty-installation'
        other.mkdir()
        alias.unlink()
        alias.symlink_to(other, target_is_directory=True)
        with self.assertRaises(ValueError):
            supplier.validate(self.binding)
        self.assertEqual(self.full.call_count, before + 1)
