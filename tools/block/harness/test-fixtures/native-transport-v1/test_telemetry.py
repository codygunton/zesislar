"""Nonproof telemetry controls. These tests do not execute perf or workloads."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
BASELINE = HERE
sys.path[:0] = [str(HERE), str(HERE / 'code'),
                str(BASELINE), str(BASELINE / 'code')]
import instruction_checkpoints as checkpoints
import native_instruction_profile as profile
import perf_measure
import port_native_policy
from test_production_port_memory import ProductionPortMemory


def interval(end=1, count=100, event='instructions:u', percent=100):
    return f'{end},{count},,{event},1000000000,{percent},\n'


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        authority = ProductionPortMemory('test_authorized_stock_job_claim8_fence32')
        authority.setUp()
        self.addCleanup(authority.doCleanups)
        self.job = authority.job()
        self.case = port_native_policy.port_case(self.job)
        self.output = self.root / 'job'
        self.directory = self.output / 'native/instruction-profile'
        self.directory.mkdir(parents=True)
        self.csv = self.directory / 'perf-stat.csv'

    def observer(self):
        (self.directory / 'PROFILE-ACTIVE.json').write_text(json.dumps(
            dict(case=self.case, block=self.case['block'], interval_ms=1000)))
        return checkpoints.Observer(self.output, self.job)

    def sample(self, observer, cpu, active=True, origin=1, now=200):
        observer.sample(dict(origin_cpu=origin, search_CPU_seconds=cpu,
                             search_active=active), now_ns=now)

    def report(self):
        return json.loads((self.directory / 'CHECKPOINTS.json').read_text())


class CounterTests(Fixture):
    def test_sums_intervals_and_zero_without_duplicate_poll(self):
        self.csv.write_text(interval() + interval(2, 0) + interval(3, 23))
        counter = checkpoints.Counter(self.csv)
        counter.poll(10)
        counter.poll(20)
        self.assertEqual(counter.snapshot()['instructions'], 123)
        self.assertEqual(len(counter.records), 3)
        self.assertEqual(counter.records[1]['user_instructions'], 0)
        self.assertIn('raw_line', counter.records[0])

    def test_partial_line_refuses_count_then_recovers(self):
        self.csv.write_text(interval() + interval(2, 20).rstrip('\n'))
        counter = checkpoints.Counter(self.csv)
        counter.poll(10)
        self.assertIsNone(counter.snapshot()['instructions'])
        self.assertEqual(counter.snapshot()['validated_prefix_instructions'], 100)
        self.assertEqual(counter.snapshot()['failure'], 'counter_partial_line')
        with self.csv.open('a') as stream:
            stream.write('\n')
        counter.poll(20)
        self.assertEqual(counter.snapshot()['instructions'], 120)

    def test_missing_and_empty_are_explicit(self):
        counter = checkpoints.Counter(self.csv)
        counter.poll(10)
        self.assertEqual(counter.snapshot()['failure'], 'counter_file_missing')
        self.csv.write_text('')
        counter.poll(20)
        self.assertEqual(counter.snapshot()['failure'], 'counter_unavailable')

    def test_removed_file_does_not_reuse_last_count(self):
        self.csv.write_text(interval())
        counter = checkpoints.Counter(self.csv)
        counter.poll(10)
        self.csv.unlink()
        counter.poll(20)
        self.assertIsNone(counter.snapshot()['instructions'])
        self.assertEqual(counter.snapshot()['validated_prefix_instructions'], 100)

    def test_repeated_and_decreasing_intervals_refuse(self):
        for end in [1, 0.5, 'nan', 'inf', -1]:
            with self.subTest(end=end):
                self.csv.write_text(interval() + interval(end))
                counter = checkpoints.Counter(self.csv)
                counter.poll(10)
                self.assertIsNone(counter.snapshot()['instructions'])
                self.assertEqual(counter.snapshot()['failure'], 'counter_measurement_failed')

    def test_bad_counter_rows_refuse(self):
        for line in [interval(count='<not counted>'), interval(event='cycles:u'),
                     interval(percent=99.9), '1,100\n', interval(count=-1),
                     '1,100,,instructions:u,nan,100,\n', '\N{SNOWMAN}\n', 'x' * 8193 + '\n']:
            with self.subTest(line=line[:50]):
                self.csv.write_text(line)
                counter = checkpoints.Counter(self.csv)
                counter.poll(10)
                self.assertIsNone(counter.snapshot()['instructions'])
                self.assertIsNotNone(counter.snapshot()['failure_detail'])

    def test_replacement_and_shrink_refuse(self):
        for replace in [False, True]:
            self.csv.write_text(interval())
            counter = checkpoints.Counter(self.csv)
            counter.poll(10)
            if replace:
                other = self.csv.with_suffix('.new')
                other.write_text(interval(2))
                other.replace(self.csv)
            else:
                self.csv.write_text('')
            counter.poll(20)
            self.assertEqual(counter.snapshot()['failure'], 'counter_measurement_failed')

    def test_chunk_backlog_does_not_report_incomplete_total(self):
        self.csv.write_text(''.join(interval(i) for i in range(1, 4001)))
        counter = checkpoints.Counter(self.csv)
        counter.poll(10)
        self.assertIsNone(counter.snapshot()['instructions'])
        while counter.offset < self.csv.stat().st_size:
            counter.poll(20)
        self.assertEqual(counter.snapshot()['instructions'], 400000)


class ObserverTests(Fixture):
    def test_dynamic_thresholds_beyond_7200_and_21600(self):
        observer = self.observer()
        self.csv.write_text(interval())
        self.sample(observer, 24605)
        rows = self.report()['checkpoints']
        self.assertEqual([r['threshold_search_CPU_seconds'] for r in rows], list(range(600, 24601, 600)))
        self.assertEqual(rows[-1]['threshold_overshoot_CPU_seconds'], 5)
        self.assertFalse(rows[-1]['exact_threshold_sample'])
        self.sample(observer, 24605)
        self.assertEqual(len(self.report()['checkpoints']), 41)

    def test_qualified_pre_origin_baseline_and_raw_interval(self):
        observer = self.observer()
        self.csv.write_text(interval())
        observer.sample(dict(origin_cpu=None, search_CPU_seconds=0, search_active=False), now_ns=100)
        (self.output / 'SEARCH-CPU-ORIGIN.json').write_text(json.dumps(dict(operation_started_ns=150)))
        with self.csv.open('a') as stream:
            stream.write(interval(2, 20))
        self.sample(observer, 605)
        row = self.report()['checkpoints'][0]
        self.assertEqual(row['instructions_since_observed_baseline'], 20)
        self.assertEqual(row['baseline_gap_ns'], 50)
        self.assertIn('not exact search-only', row['baseline_qualification'])

    def test_post_origin_baseline_is_not_qualified(self):
        observer = self.observer()
        self.csv.write_text(interval())
        observer.sample(dict(origin_cpu=None, search_CPU_seconds=0), now_ns=200)
        (self.output / 'SEARCH-CPU-ORIGIN.json').write_text(json.dumps(dict(operation_started_ns=100)))
        self.sample(observer, 600)
        row = self.report()['checkpoints'][0]
        self.assertIsNone(row['instructions_since_observed_baseline'])
        self.assertIsNotNone(row['baseline_failure'])

    def test_long_marker_requires_active_search_and_is_once_only(self):
        observer = self.observer()
        self.csv.write_text(interval())
        marker = self.directory / 'LONG-SEARCH.json'
        self.sample(observer, 21600, active=False)
        self.assertFalse(marker.exists())
        self.sample(observer, 21601, active=True)
        original = marker.read_bytes()
        self.sample(observer, 22200, active=True)
        self.assertEqual(marker.read_bytes(), original)
        self.sample(self.observer(), 23000, active=True)
        self.assertEqual(marker.read_bytes(), original)
        self.assertEqual(json.loads(original)['signals_sent'], 0)

    def test_origin_alone_never_creates_long_marker(self):
        observer = self.observer()
        self.sample(observer, None)
        self.assertFalse((self.directory / 'LONG-SEARCH.json').exists())
        self.assertEqual(self.report()['failure'], 'search_CPU_unavailable')

    def test_final_cpu_without_origin_continues_rows_not_long_marker(self):
        observer = self.observer()
        self.sample(observer, 22200, active=False, origin=None)
        self.assertEqual(len(self.report()['checkpoints']), 37)
        self.assertFalse((self.directory / 'LONG-SEARCH.json').exists())
        for row in self.report()['checkpoints']:
            self.assertEqual(row['sample_phase'], 'inactive_or_final')
            self.assertTrue(row['may_include_post_search_instructions'])
            self.assertIn('may include post-search work', row['instruction_qualification'])

    def test_active_checkpoint_has_active_sample_qualification(self):
        observer = self.observer()
        self.csv.write_text(interval())
        self.sample(observer, 600)
        row = self.report()['checkpoints'][0]
        self.assertEqual(row['sample_phase'], 'active_search')
        self.assertFalse(row['may_include_post_search_instructions'])
        self.assertIn('full MCP-session', row['instruction_qualification'])

    def test_completed_search_with_later_session_count_is_qualified(self):
        observer = self.observer()
        self.csv.write_text(interval())
        self.sample(observer, 599)
        with self.csv.open('a') as stream:
            stream.write(interval(2, 900))
        self.sample(observer, 601, active=False)
        row = self.report()['checkpoints'][0]
        self.assertEqual(row['counter']['instructions'], 1000)
        self.assertFalse(row['search_active'])
        self.assertTrue(row['may_include_post_search_instructions'])
        self.assertFalse((self.directory / 'LONG-SEARCH.json').exists())

    def test_invalid_or_partial_counter_at_completion_stays_unavailable(self):
        for text in [interval(percent=99), interval().rstrip('\n')]:
            observer = self.observer()
            self.csv.write_text(text)
            self.sample(observer, 22200, active=False)
            row = self.report()['checkpoints'][-1]
            self.assertIsNone(row['counter']['instructions'])
            self.assertIsNotNone(row['counter']['failure'])
            self.assertTrue(row['may_include_post_search_instructions'])
            self.assertFalse((self.directory / 'LONG-SEARCH.json').exists())

    def test_missing_counter_is_nonfatal_at_long_threshold(self):
        observer = self.observer()
        self.sample(observer, 21601)
        row = self.report()['checkpoints'][-1]
        self.assertIsNone(row['counter']['instructions'])
        self.assertEqual(row['counter']['failure'], 'counter_file_missing')
        self.assertTrue((self.directory / 'LONG-SEARCH.json').exists())

    def test_wrong_or_missing_marker_never_reads_counter(self):
        for missing in [False, True]:
            observer = self.observer()
            marker = self.directory / 'PROFILE-ACTIVE.json'
            marker.unlink() if missing else marker.write_text('{}')
            self.csv.write_text(interval())
            self.sample(observer, 600)
            self.assertEqual(observer.counter.offset, 0)
            self.assertIsNone(self.report()['checkpoints'][0]['counter']['instructions'])

    def test_preparation_failure_disables_old_marker(self):
        observer = self.observer()
        (self.directory / 'PROFILE-UNAVAILABLE.json').write_text('{}')
        self.csv.write_text(interval())
        self.sample(observer, 600)
        self.assertEqual(observer.counter.offset, 0)
        self.assertEqual(self.report()['failure'], 'profile_preparation_failed')

    def test_array_profile_marker_is_nonfatal_and_never_reads_counter(self):
        observer = self.observer()
        (self.directory / 'PROFILE-ACTIVE.json').write_text('[]')
        self.csv.write_text(interval())
        self.sample(observer, 600)
        self.assertEqual(observer.counter.offset, 0)
        self.assertEqual(self.report()['failure'], 'profile_marker_invalid')
        self.assertIsNone(self.report()['checkpoints'][0]['counter']['instructions'])

    def test_array_long_marker_is_nonfatal_and_never_replaced(self):
        observer = self.observer()
        marker = self.directory / 'LONG-SEARCH.json'
        marker.write_text('[]')
        self.sample(observer, 21600)
        self.assertEqual(marker.read_text(), '[]')
        self.assertEqual(self.report()['failure'], 'checkpoint_observer_failed')
        self.assertEqual(len(self.report()['checkpoints']), 36)

    def test_invalid_cpu_and_active_flag_are_explicit(self):
        observer = self.observer()
        for cpu in [True, -1, float('nan'), float('inf'), '600']:
            self.sample(observer, cpu)
            self.assertEqual(self.report()['failure'], 'search_CPU_unavailable')
        self.sample(observer, 600, active=1)
        self.assertEqual(self.report()['failure'], 'search_active_unavailable')

    def test_reporting_io_failure_is_nonfatal(self):
        observer = self.observer()
        with patch.object(checkpoints, 'atomic', side_effect=OSError('full')):
            self.sample(observer, 600)

    def test_non_port_and_non_native_do_nothing(self):
        for job in [None, {'phase': 'native', 'workload': {'kind': 'focused_check'}},
                    {'phase': 'prerequisites'}]:
            observer = checkpoints.Observer(self.root / 'unused', job)
            self.sample(observer, 99999)
            self.assertFalse((self.root / 'unused').exists())

    def test_invalid_port_refuses_before_reporting(self):
        job = deepcopy(self.job)
        job['key'] = '8009c354'
        with self.assertRaises(ValueError):
            checkpoints.Observer(self.output, job)


class LauncherTests(Fixture):
    def launch(self, job=None, target=None):
        runtime = dict(canonical_admission=dict(memory_job=self.job if job is None else job))
        return profile.profile_launcher(runtime['canonical_admission']['memory_job'], {'block': self.case if target is None else target},
                                        self.root, self.output / 'native', ['mcp', '--exact'])

    def fake_perf(self):
        binary = self.root / 'perf'
        binary.write_bytes(b'not an executable; tests never run it')
        return dict(path=str(binary), sha256=hashlib.sha256(binary.read_bytes()).hexdigest())

    def test_non_port_launcher_is_unchanged(self):
        launcher = ['mcp']
        result = profile.profile_launcher({}, {}, self.root, self.output, launcher)
        self.assertIs(result[0], launcher)
        self.assertIsNone(result[1])

    def test_wrong_authorized_target_refuses_before_prepare(self):
        with patch.object(profile, 'prepare') as prepare:
            with self.assertRaises(ValueError):
                self.launch(target=dict(self.case, module='wrong'))
            prepare.assert_not_called()

    def test_invalid_port_does_not_silently_fall_back(self):
        job = deepcopy(self.job)
        job['key'] = 'wrong'
        with self.assertRaises(ValueError):
            self.launch(job=job)

    def test_pinned_wrap_preserves_command_and_cache_evidence(self):
        binding = self.fake_perf()
        cache = self.root / '.lia.cache'
        cache.write_bytes(b'cache')
        with patch.object(profile, 'PERF', binding), patch.object(perf_measure.shutil, 'which', return_value=binding['path']):
            command, measurement = self.launch()
        self.assertEqual(command[-3:], ['--', 'mcp', '--exact'])
        self.assertEqual(command[command.index('--') - 2:command.index('--')], ['--interval-print', '1000'])
        self.assertEqual(measurement['perf_executable'], binding)
        self.assertFalse(cache.exists())
        retained = next(r for r in measurement['cache_removals'] if r['present'])
        self.assertEqual(Path(retained['retained']).read_bytes(), b'cache')
        self.assertEqual(measurement['port_case'], self.case)

    def test_changed_or_missing_pinned_perf_is_nonfatal_and_explicit(self):
        for missing in [False, True]:
            binding = self.fake_perf()
            if missing:
                Path(binding['path']).unlink()
            else:
                binding['sha256'] = '0' * 64
            with patch.object(profile, 'PERF', binding):
                command, measurement = self.launch()
            self.assertEqual(command, ['mcp', '--exact'])
            self.assertIsNone(measurement)
            result = json.loads((self.output / 'native/INSTRUCTION-PROFILE.json').read_text())
            self.assertEqual(result['failure'], 'profile_preparation_failed')

    def test_unpinned_selected_perf_is_not_returned(self):
        binding = self.fake_perf()
        other = self.root / 'other-perf'
        other.write_bytes(Path(binding['path']).read_bytes())
        with patch.object(profile, 'PERF', binding), patch.object(perf_measure.shutil, 'which', return_value=str(other)):
            command, measurement = self.launch()
        self.assertEqual(command, ['mcp', '--exact'])
        self.assertIsNone(measurement)

    def test_completed_profile_retains_raw_intervals_and_hash(self):
        self.csv.write_text(interval() + interval(2, 20))
        measurement = dict(port_case=self.case, perf_stat=str(self.csv))
        profile.complete_profile(measurement, self.output)
        result = json.loads((self.output / 'INSTRUCTION-PROFILE.json').read_text())
        self.assertTrue(result['instruction_measurement_complete'])
        self.assertEqual(result['counter']['instructions'], 120)
        self.assertEqual(len(result['interval_records']), 2)
        self.assertEqual(result['perf_stat_sha256'], hashlib.sha256(self.csv.read_bytes()).hexdigest())
        self.assertFalse(result['search_only'])

    def test_final_missing_partial_and_bad_counters_are_unavailable(self):
        for text in [None, interval().rstrip('\n'), interval(percent=0)]:
            if text is None:
                self.csv.unlink(missing_ok=True)
            else:
                self.csv.write_text(text)
            profile.complete_profile(dict(port_case=self.case, perf_stat=str(self.csv)), self.output)
            result = json.loads((self.output / 'INSTRUCTION-PROFILE.json').read_text())
            self.assertFalse(result['instruction_measurement_complete'])
            self.assertIsNone(result['counter']['instructions'])

    def test_final_report_failure_does_not_raise(self):
        self.csv.write_text(interval())
        with patch.object(Path, 'write_text', side_effect=OSError('full')):
            profile.complete_profile(dict(port_case=self.case, perf_stat=str(self.csv)), self.output)

    def test_reviewed_perf_helper_remains_byte_identical(self):
        self.assertEqual((HERE / 'perf_measure.py').read_bytes(),
                         Path('/home/cody/zesislar/_build/agents/worker-build-2/native-port-policy-v1/telemetry/upstream/perf_measure.py').read_bytes())


if __name__ == '__main__':
    unittest.main()
