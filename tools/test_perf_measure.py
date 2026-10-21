import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / 'block'))
import perf_measure


class PerfMeasureTests(unittest.TestCase):
    def test_exact_integer_count_and_complete_runtime(self):
        result = perf_measure.parse_stat('# started on date\n\n123456789,,instructions:u,1000000,100.00,,\n')
        self.assertEqual(result['user_instructions'], 123456789)
        self.assertEqual(result['running_percent'], 100)

    def test_refused_missing_duplicate_and_partial_events_are_rejected(self):
        valid = '123,,instructions:u,1000,100.00,,\n'
        invalid = ['', valid + valid, valid.replace('123', '<not counted>'),
                   valid.replace('123', '<not supported>'), valid.replace('123', '0'),
                   valid.replace('instructions:u', 'instructions'), valid.replace('100.00', '99.99'),
                   valid.replace('1000', 'nan'), valid.replace('1000', '0'),
                   valid + 'unexpected row\n']
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(ValueError):
                perf_measure.parse_stat(text)

    def test_only_three_owned_caches_are_retained_and_removed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cwd, output = root / 'cwd', root / 'output'
            cwd.mkdir()
            output.mkdir()
            for name in perf_measure.CACHE_NAMES:
                (cwd / name).write_bytes(name.encode())
            unrelated = cwd / '.other.cache'
            unrelated.write_bytes(b'preserve')
            rows = perf_measure.clear_caches(cwd, output)
            self.assertEqual(len(rows), 3)
            for row in rows:
                self.assertTrue(row['removed'])
                self.assertFalse(Path(row['path']).exists())
                data = Path(row['retained']).read_bytes()
                self.assertEqual(data, Path(row['path']).name.encode())
                self.assertEqual(row['sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(unrelated.read_bytes(), b'preserve')

    def test_absent_cache_and_external_symlink_do_not_remove_another_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cwd, output = root / 'cwd', root / 'output'
            cwd.mkdir()
            output.mkdir()
            rows = perf_measure.clear_caches(cwd, output)
            self.assertTrue(all(not row['present'] for row in rows))
            external = root / 'external'
            external.write_bytes(b'keep')
            (cwd / '.lia.cache').symlink_to(external)
            with self.assertRaisesRegex(ValueError, 'regular file'):
                perf_measure.clear_caches(cwd, output)
            self.assertEqual(external.read_bytes(), b'keep')

    def test_workload_telemetry_selects_only_the_exact_direct_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            proc = Path(directory)
            children = proc / '100/task/100/children'
            children.parent.mkdir(parents=True)
            children.write_text('101 102')
            for pid, command in [('101', '/other/compiler'), ('102', '/pinned/coqc')]:
                (proc / pid).mkdir()
                (proc / pid / 'cmdline').write_bytes(command.encode() + b'\0-q\0')
            self.assertEqual(perf_measure.workload_pid(100, ['/pinned/coqc'], proc), 102)
            (proc / '102/cmdline').unlink()
            self.assertIsNone(perf_measure.workload_pid(100, ['/pinned/coqc'], proc))

    def test_exact_command_has_no_shell_or_inner_wrapper(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command = ['/pinned/coqc', '-q', 'source with spaces.v']
            with patch.object(perf_measure.shutil, 'which', return_value='/usr/bin/perf'):
                measurement = perf_measure.prepare(command, root / 'output', root)
            self.assertEqual(measurement['command'][-4:], ['--', *command])
            self.assertIn('-x,', measurement['command'])
            self.assertIn('instructions:u', measurement['command'])
            self.assertEqual(measurement['workload_command'], command)
            output = Path(measurement['perf_stat'])
            output.write_text('456,,instructions:u,2000,100.00,,\n')
            result = perf_measure.finish(measurement)
            self.assertEqual(result['user_instructions'], 456)
            self.assertTrue(result['instruction_measurement_complete'])
            with self.assertRaisesRegex(ValueError, 'already exists'):
                perf_measure.prepare(command, root / 'output', root)


if __name__ == '__main__':
    unittest.main()
