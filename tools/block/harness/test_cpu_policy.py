"""Check the PORT CPU exception without a compiler, proof, claim, or signal."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
BASELINE = HERE
sys.path[:0] = [str(BASELINE), str(BASELINE / 'code')]
from test_production_port_memory import ProductionPortMemory
import memory_policy
sys.path.insert(0, str(HERE / 'code'))
import port_native_policy
spec = importlib.util.spec_from_file_location('port_limits_test', HERE / 'code/scratch_limits.py')
limits = importlib.util.module_from_spec(spec)
spec.loader.exec_module(limits)


class PortCpuPolicy(unittest.TestCase):
    def setUp(self):
        self.fixture = ProductionPortMemory('test_authorized_stock_job_claim8_fence32')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.job = self.fixture.job()
        self.root = self.fixture.root

    def test_exact_authorized_case_is_returned(self):
        self.assertEqual(port_native_policy.port_case(self.job), self.fixture.case)
        self.assertEqual(port_native_policy.cpu_budgets(self.job), (None, None))

    def test_setup_and_search_continue_beyond_six_hours(self):
        for cpu, origin, end in [(10**9, None, None), (21601, 1, None),
                                 (10**9, 1, 100)]:
            self.assertIsNone(limits.stop_reason(cpu, 1024, 8 * memory_policy.GIB,
                origin_cpu=origin, end_cpu=end, memory_job=self.job))

    def test_memory_fence_remains_32_gib(self):
        self.assertEqual(limits.stop_reason(10**9, 32 * memory_policy.GIB,
            8 * memory_policy.GIB, memory_job=self.job), 'external_memory_stop')

    def test_other_routes_keep_both_cpu_stops(self):
        for job in [None, {'phase': 'prerequisites'},
                    {'phase': 'native', 'workload': {'kind': 'stock_pass_spec_bundle'}},
                    {'phase': 'native', 'workload': {'kind': 'focused_check'}}]:
            self.assertIsNone(port_native_policy.port_case(job))
            self.assertEqual(port_native_policy.cpu_budgets(job), (7200, None))
        self.assertIsNone(limits.stop_reason(7200, 0, 1))
        self.assertEqual(limits.stop_reason(7201, 0, 1, origin_cpu=1), 'external_CPU_stop')

    def test_unlisted_block_does_not_receive_the_exception(self):
        job = deepcopy(self.job)
        job['key'] = '8009c354'
        with self.assertRaises(ValueError):
            port_native_policy.port_case(job)

    def test_wrong_claim_does_not_receive_the_exception(self):
        job = deepcopy(self.job)
        job['claim_bytes'] = 16 * memory_policy.GIB
        with self.assertRaises(ValueError):
            port_native_policy.port_case(job)

    def aggregate_fixture(self):
        parent = self.root / 'zesuworkloads.slice'
        parent.mkdir()
        (parent / 'memory.max').write_text(str(175 * memory_policy.GIB))
        (parent / 'memory.swap.max').write_text('0')
        group = parent / 'zesuworkloads-aggregate1000p1r2.slice'
        group.mkdir()
        for name, text in {'memory.max': str(32 * memory_policy.GIB),
                           'memory.swap.max': '0', 'memory.current': '100',
                           'memory.peak': '200', 'memory.events': 'oom 0\noom_kill 0\n',
                           'cpu.stat': 'usage_usec 1000000000\n'}.items():
            (group / name).write_text(text)
        st = group.stat()
        identity = dict(aggregate_path=str(group), aggregate_device=st.st_dev,
                        aggregate_inode=st.st_ino, inside_pid=1, inside_startticks=2)
        output = self.root / 'job'
        output.mkdir()
        (output / 'BATCH-IDENTITY.json').write_text(json.dumps(identity))
        (output / 'RUNTIME.json').write_text(json.dumps(
            {'canonical_admission': {'memory_job': self.job}}))
        return output, identity

    def test_origin_records_unrestricted_budgets(self):
        output, _ = self.aggregate_fixture()
        row = limits.record_search_origin(output, 123, {'body': 'zesu_block.'})
        self.assertIsNone(row['search_budget_CPU_seconds'])
        self.assertIsNone(row['setup_budget_CPU_seconds'])

    def test_search_activity_excludes_completion_and_failure(self):
        output, identity = self.aggregate_fixture()
        self.assertFalse(limits.search_accounting(output, identity, 1000)['search_active'])
        limits.record_search_origin(output, 123, {'body': 'zesu_block.'})
        self.assertTrue(limits.search_accounting(output, identity, 1001)['search_active'])
        native = output / 'native'
        native.mkdir()
        failure = native / 'WORKER-FAILURE.json'
        failure.write_text('{}')
        self.assertFalse(limits.search_accounting(output, identity, 1001)['search_active'])
        failure.unlink()
        limits.record_search_end(output)
        self.assertFalse(limits.search_accounting(output, identity, 1001)['search_active'])

    def test_final_sample_records_completion_without_long_search(self):
        output, identity = self.aggregate_fixture()
        limits.record_search_origin(output, 123, {'body': 'zesu_block.'})
        (output / 'SEARCH-CPU-END.json').write_text(json.dumps(
            {'aggregate': identity, 'CPU_seconds': 22601}))
        (output / 'CPU-FINAL.json').write_text(json.dumps(
            {'cpu_seconds': 22602, 'final_memory_accounting_available': True}))
        class Recorder:
            rows = []
            def sample(self, row): self.rows.append(row)
        recorder = Recorder()
        self.assertEqual(limits.finish_growth(output, 0, 0, None, 0,
            memory_job=self.job, instruction_checkpoints=recorder), 0)
        self.assertEqual(len(recorder.rows), 1)
        self.assertFalse(recorder.rows[0]['search_active'])
        self.assertEqual(recorder.rows[0]['search_CPU_seconds'], 21601)

    def test_prepare_and_refresh_metadata_use_the_same_policy(self):
        runtime = {'cache_attempt': {'limits': {'cpu_seconds': 7200}}}
        port_native_policy.configure_cpu(runtime, self.job)
        self.assertIsNone(runtime['search_CPU_policy']['window_seconds'])
        self.assertIsNone(runtime['search_CPU_policy']['setup_budget_seconds'])
        self.assertIsNone(runtime['cache_attempt']['limits']['cpu_seconds'])
        self.assertEqual(runtime['search_CPU_policy']['perf_executable'], port_native_policy.PERF)
        port_native_policy.configure_cpu(runtime, None)
        self.assertEqual(runtime['search_CPU_policy']['window_seconds'], 7200)
        self.assertEqual(runtime['search_CPU_policy']['setup_budget_seconds'], None)
        self.assertEqual(runtime['cache_attempt']['limits']['cpu_seconds'], 7200)
        self.assertNotIn('perf_executable', runtime['search_CPU_policy'])


if __name__ == '__main__':
    unittest.main()
