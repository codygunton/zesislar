"""Keep repeated monitoring independent of expensive supplier validation."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE / 'code'), str(HERE)]
import scratch_limits as limits
import memory_policy
from test_search_window import SearchWindowControls


class MonitorSampling(unittest.TestCase):
    def setUp(self):
        self.fixture = SearchWindowControls()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def test_real_polling_validates_once_and_checks_cgroups_each_time(self):
        fixture = self.fixture
        class Child:
            calls = 0
            def poll(self):
                self.calls += 1
                return None if self.calls <= 3 else 0
            def wait(self):
                return 0
        with patch.object(memory_policy, 'validate_job', wraps=memory_policy.validate_job) as validate, \
                patch.object(limits, 'exact_aggregate', wraps=limits.exact_aggregate) as aggregate, \
                patch.object(limits, 'finish_growth', return_value=0), patch.object(limits.time, 'sleep'):
            self.assertEqual(limits.wait_with_limits(Child(), fixture.out, 64 * 1024**3,
                                                    memory_job=fixture.memory_job), 0)
        self.assertEqual(validate.call_count, 1)
        self.assertEqual(aggregate.call_count, 3)

    def test_invalid_job_refuses_before_sampling(self):
        fixture = self.fixture
        fixture.memory_job['claim_bytes'] = 1
        with patch.object(limits, 'sample_aggregate') as sample:
            with self.assertRaises(ValueError):
                limits.wait_with_limits(None, fixture.out, 1, memory_job=fixture.memory_job)
        sample.assert_not_called()

    def test_policy_mutation_and_fork_refuse(self):
        fixture = self.fixture
        policy = limits._MonitorPolicy(fixture.memory_job, 'native')
        token = limits._MONITOR_POLICY.set(policy)
        try:
            with patch.object(limits.os, 'getpid', return_value=policy.pid + 1):
                with self.assertRaisesRegex(ValueError, 'monitor job changed'):
                    limits.stop_reason(0, 0, 1, memory_job=fixture.memory_job)
            fixture.memory_job['claim_bytes'] += 1
            with self.assertRaisesRegex(ValueError, 'monitor job changed'):
                limits.stop_reason(0, 0, 1, memory_job=fixture.memory_job)
        finally:
            limits._MONITOR_POLICY.reset(token)

    def test_fence_swap_and_inode_checks_remain_per_poll(self):
        fixture = self.fixture
        policy = limits._MonitorPolicy(fixture.memory_job, 'native')
        token = limits._MONITOR_POLICY.set(policy)
        try:
            self.assertEqual(limits.exact_aggregate(fixture.identity, policy.physical,
                                                   memory_job=fixture.memory_job), fixture.group)
            for name, value in [('memory.max', '1'), ('memory.swap.max', '1')]:
                path = fixture.group / name
                original = path.read_text()
                path.write_text(value)
                with self.assertRaises(ValueError):
                    limits.exact_aggregate(fixture.identity, policy.physical, memory_job=fixture.memory_job)
                path.write_text(original)
            changed = dict(fixture.identity, aggregate_inode=-1)
            with self.assertRaises(ValueError):
                limits.exact_aggregate(changed, policy.physical, memory_job=fixture.memory_job)
            self.assertEqual(limits.stop_reason(1, policy.physical, 1, memory_job=fixture.memory_job),
                             'external_memory_stop')
            self.assertEqual(limits.stop_reason(7201, 0, 1, origin_cpu=1, memory_job=fixture.memory_job),
                             'external_CPU_stop')
        finally:
            limits._MONITOR_POLICY.reset(token)
