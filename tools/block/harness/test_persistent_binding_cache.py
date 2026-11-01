"""Check full-identity digest reuse across independent nonproof processes."""
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import binding_cache as cache


class PersistentBindingCache(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.file = self.root / 'source.v'
        self.file.write_bytes(b'first')
        self.cache = self.root / 'cache'
        self.addCleanup(patch.stopall)
        patch.object(cache, 'CACHE_ROOT', self.cache).start()
        cache._DIGESTS.clear()
        for key in cache.COUNTERS:
            cache.COUNTERS[key] = 0

    def cold_process(self, *, force=False):
        code = '''import json,sys
from pathlib import Path
import binding_cache as c
c.CACHE_ROOT=Path(sys.argv[1])
with c.force_hashing(sys.argv[3]=='True'):
 value=c.digest(Path(sys.argv[2]))
print(json.dumps(dict(value=value,counters=c.COUNTERS)))
'''
        result = subprocess.run([sys.executable, '-B', '-c', code, str(self.cache),
                                 str(self.file), str(force)], capture_output=True, text=True,
                                env=dict(os.environ, PYTHONPATH=str(HERE / 'code')), timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def record(self):
        return next(self.cache.glob('*.json'))

    def test_independent_process_reuses_exact_full_key(self):
        first = self.cold_process()
        second = self.cold_process()
        self.assertEqual(first['value'], second['value'])
        self.assertEqual(first['counters']['hashes'], 1)
        self.assertEqual(second['counters']['hashes'], 0)
        self.assertEqual(second['counters']['persistent_hits'], 1)

    def test_same_size_write_with_restored_mtime_invalidates(self):
        before = self.file.stat()
        first = self.cold_process()
        self.file.write_bytes(b'other')
        os.utime(self.file, ns=(before.st_atime_ns, before.st_mtime_ns))
        second = self.cold_process()
        self.assertNotEqual(first['value'], second['value'])
        self.assertEqual(second['counters']['hashes'], 1)

    def test_inode_replacement_invalidates(self):
        self.cold_process()
        replacement = self.root / 'replacement'
        replacement.write_bytes(b'first')
        replacement.replace(self.file)
        self.assertEqual(self.cold_process()['counters']['hashes'], 1)

    def test_mode_change_invalidates(self):
        self.cold_process()
        self.file.chmod(0o400)
        self.assertEqual(self.cold_process()['counters']['hashes'], 1)

    def test_final_symlink_retarget_invalidates(self):
        other = self.root / 'other'
        other.write_bytes(b'other')
        link = self.root / 'link'
        link.symlink_to(self.file)
        first = cache.digest(link)
        cache._DIGESTS.clear()
        link.unlink()
        link.symlink_to(other)
        self.assertNotEqual(cache.digest(link), first)
        self.assertEqual(cache.COUNTERS['persistent_hits'], 0)

    def test_parent_alias_resolution_stays_fresh(self):
        second = self.root / 'second'
        second.mkdir()
        (second / 'source.v').write_bytes(b'other')
        alias = self.root / 'alias'
        alias.symlink_to(self.root)
        first = cache.digest(cache.resolve_input(alias / 'source.v', {}))
        alias.unlink()
        alias.symlink_to(second)
        self.assertNotEqual(cache.digest(cache.resolve_input(alias / 'source.v', {})), first)

    def test_force_hashing_bypasses_both_caches(self):
        cache.digest(self.file)
        with patch.object(cache.hashlib, 'file_digest', wraps=cache.hashlib.file_digest) as hashed:
            with cache.force_hashing(True):
                cache.digest(self.file)
            self.assertEqual(hashed.call_count, 1)
        forced = self.cold_process(force=True)
        self.assertEqual(forced['counters']['hashes'], 1)
        self.assertEqual(forced['counters']['persistent_hits'], 0)

    def test_corrupt_record_is_not_a_hit(self):
        cache.digest(self.file)
        record = self.record()
        original = json.loads(record.read_text())
        for value in [[], {}, dict(original, schema='wrong'),
                      dict(original, context={}), dict(original, sha256='bad'),
                      dict(original, extra=True)]:
            with self.subTest(value=value):
                cache._DIGESTS.clear()
                record.write_text(json.dumps(value))
                with patch.object(cache.hashlib, 'file_digest', wraps=cache.hashlib.file_digest) as hashed:
                    self.assertEqual(cache.digest(self.file), hashlib.sha256(b'first').hexdigest())
                    self.assertEqual(hashed.call_count, 1)

    def test_nonprivate_record_is_not_a_hit(self):
        cache.digest(self.file)
        cache._DIGESTS.clear()
        self.record().chmod(0o644)
        cache.digest(self.file)
        self.assertEqual(cache.COUNTERS['persistent_hits'], 0)
        self.assertEqual(cache.COUNTERS['hashes'], 2)

    def test_symlink_record_is_not_a_hit(self):
        cache.digest(self.file)
        cache._DIGESTS.clear()
        record = self.record()
        target = self.root / 'record'
        record.rename(target)
        record.symlink_to(target)
        cache.digest(self.file)
        self.assertFalse(record.is_symlink())
        self.assertEqual(cache.COUNTERS['persistent_hits'], 0)

    def test_nonprivate_cache_falls_back_to_hashing(self):
        self.cache.mkdir(mode=0o755)
        cache.digest(self.file)
        self.assertEqual(cache.COUNTERS['persistent_unavailable'], 1)
        self.assertEqual(cache.COUNTERS['hashes'], 1)
        self.assertFalse(list(self.cache.iterdir()))

    def test_symlink_cache_falls_back_to_hashing(self):
        target = self.root / 'target'
        target.mkdir(mode=0o700)
        self.cache.symlink_to(target, target_is_directory=True)
        cache.digest(self.file)
        self.assertEqual(cache.COUNTERS['persistent_unavailable'], 1)
        self.assertFalse(list(target.iterdir()))

    def test_lookup_race_refuses(self):
        cache.digest(self.file)
        cache._DIGESTS.clear()
        original = cache._read_persistent
        def raced(*args):
            result = original(*args)
            self.file.write_bytes(b'other')
            return result
        with patch.object(cache, '_read_persistent', side_effect=raced):
            with self.assertRaisesRegex(ValueError, 'changed during validation'):
                cache.digest(self.file)

    def test_hash_race_refuses_without_publication(self):
        original = cache.hashlib.file_digest
        def raced(*args):
            result = original(*args)
            self.file.write_bytes(b'other')
            return result
        with patch.object(cache.hashlib, 'file_digest', side_effect=raced):
            with self.assertRaisesRegex(ValueError, 'changed during validation'):
                cache.digest(self.file)
        self.assertFalse(list(self.cache.glob('*.json')))

    def test_lock_wait_race_refuses(self):
        @contextmanager
        def waited(context):
            self.file.write_bytes(b'other')
            yield None
        with patch.object(cache, '_persistent', side_effect=waited):
            with self.assertRaisesRegex(ValueError, 'changed during validation'):
                cache.digest(self.file)

    def test_two_processes_serialize_one_hash(self):
        code = '''import json,sys,time
from pathlib import Path
import binding_cache as c
c.CACHE_ROOT=Path(sys.argv[1])
original=c.hashlib.file_digest
def measured(*args):
 with open(sys.argv[3],'a') as stream:stream.write('hash\\n')
 time.sleep(.1)
 return original(*args)
c.hashlib.file_digest=measured
print(c.digest(Path(sys.argv[2])))
'''
        commands = [sys.executable, '-B', '-c', code, str(self.cache), str(self.file), str(self.root / 'hashes')]
        processes = [subprocess.Popen(commands, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                        env=dict(os.environ, PYTHONPATH=str(HERE / 'code'))) for _ in range(2)]
        results = [process.communicate(timeout=15) for process in processes]
        for process, (_, errors) in zip(processes, results):
            self.assertEqual(process.returncode, 0, errors)
        self.assertEqual(results[0][0], results[1][0])
        self.assertEqual((self.root / 'hashes').read_text(), 'hash\n')
        row = json.loads(self.record().read_text())
        self.assertEqual(row['schema'], cache._SCHEMA)
        self.assertEqual(set(row['context']), {'path', 'lstat', 'stat'})
        self.assertEqual(len(row['context']['lstat']), 6)
        self.assertEqual(len(row['context']['stat']), 6)

    def test_forced_hashing_never_opens_persistent_storage(self):
        cache.digest(self.file)
        with patch.object(cache, '_persistent', side_effect=AssertionError('persistent lock')) as locked, \
                patch.object(cache, '_read_persistent', side_effect=AssertionError('persistent lookup')) as lookup, \
                patch.object(cache, '_publish', side_effect=AssertionError('persistent publication')) as publish, \
                patch.object(cache.hashlib, 'file_digest', wraps=cache.hashlib.file_digest) as hashed:
            with cache.force_hashing(True):
                value = cache.digest(self.file)
            self.assertEqual(hashed.call_count, 1)
            self.assertEqual(cache.digest(self.file), value)
            self.assertEqual(hashed.call_count, 1)
        locked.assert_not_called()
        lookup.assert_not_called()
        publish.assert_not_called()

    def test_cache_publication_never_requests_durability(self):
        with patch.object(cache.os, 'fsync', side_effect=AssertionError('durability call')) as sync:
            self.assertEqual(cache.digest(self.file), hashlib.sha256(b'first').hexdigest())
        sync.assert_not_called()
        self.assertEqual(json.loads(self.record().read_text())['sha256'],
                         hashlib.sha256(b'first').hexdigest())

    def test_atomic_publication_exposes_only_complete_records(self):
        cache.digest(self.file)
        record = self.record()
        previous = record.read_bytes()
        context = json.loads(previous)['context']
        value = hashlib.sha256(b'first').hexdigest()
        replace = cache.os.replace
        observed = []
        def checked_replace(source, target):
            self.assertEqual(Path(target), record)
            self.assertEqual(record.read_bytes(), previous)
            temporary = Path(source)
            complete = json.loads(temporary.read_bytes())
            self.assertEqual(complete, dict(schema=cache._SCHEMA, context=context, sha256=value))
            self.assertEqual(temporary.stat().st_mode & 0o777, 0o600)
            observed.append(temporary)
            replace(source, target)
            self.assertEqual(json.loads(record.read_bytes()), complete)
        with patch.object(cache.os, 'replace', side_effect=checked_replace) as published:
            cache._publish(record, context, value)
        published.assert_called_once()
        self.assertEqual(len(observed), 1)
        self.assertFalse(observed[0].exists())
        self.assertFalse(list(self.cache.glob('.digest-*')))

    def test_failed_publication_cleans_temporary_and_preserves_record(self):
        cache.digest(self.file)
        record = self.record()
        previous = record.read_bytes()
        row = json.loads(previous)
        with patch.object(cache.os, 'replace', side_effect=OSError('publication refused')):
            with self.assertRaisesRegex(OSError, 'publication refused'):
                cache._publish(record, row['context'], row['sha256'])
        self.assertEqual(record.read_bytes(), previous)
        self.assertFalse(list(self.cache.glob('.digest-*')))

    def test_failed_publication_keeps_hash_and_input_checks(self):
        with patch.object(cache, '_publish', side_effect=OSError('publication refused')):
            self.assertEqual(cache.digest(self.file), hashlib.sha256(b'first').hexdigest())
        self.assertEqual(cache.COUNTERS['persistent_unavailable'], 1)
        cache._DIGESTS.clear()
        def changed_input(*args):
            self.file.write_bytes(b'other')
            raise OSError('publication refused')
        with patch.object(cache, '_publish', side_effect=changed_input):
            with self.assertRaisesRegex(ValueError, 'changed during validation'):
                cache.digest(self.file)
