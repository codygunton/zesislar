"""Check that sweep outcomes count fence and backstop kills as killed, not open."""

from pathlib import Path
import json
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sweep_outcome as S


class OutcomeTest(unittest.TestCase):
    def test_closed(self):
        self.assertEqual(S.outcome(0, True), 'closed')

    def test_open_block_is_measured(self):
        self.assertEqual(S.outcome(1, True), 'open')

    def test_kill_without_measure_is_killed(self):
        self.assertEqual(S.outcome(143, False), 'killed')
        self.assertEqual(S.outcome(137, False), 'killed')

    def test_fence_kill_mark_is_killed(self):
        self.assertEqual(S.outcome(1, True, log_text='resource guard: memory fence kill: x reached its 16 GiB fence'), 'killed')

    def test_shared_slice_kill_is_not_a_fence_kill(self):
        log = 'resource guard: shared-slice memory kill: x did not reach its 16 GiB fence (own peak 3.2 GiB)'
        self.assertEqual(S.outcome(137, False, log_text=log), 'shared-kill')

    def test_measured_signal_exit_is_open(self):
        self.assertEqual(S.outcome(143, True), 'open')

    def test_stall_wins(self):
        self.assertEqual(S.outcome(None, False, stalled=True), 'stopped')

    def test_recount_uses_latest_row(self):
        rows = [dict(case='a', returncode=137, cpu_seconds=None, stall=None),
                dict(case='a', returncode=0, cpu_seconds=5.0, stall=None),
                dict(case='b', returncode=143, cpu_seconds=None, stall=None, status='open'),
                dict(case='c', returncode=1, cpu_seconds=9.0, stall=None),
                dict(case='d', returncode=None, cpu_seconds=None, stall={'seconds': 7200})]
        self.assertEqual(S.recount(json.dumps(r) for r in rows), {'closed': 1, 'open': 1, 'killed': 1, 'shared-kill': 0, 'stopped': 1})


if __name__ == '__main__':
    unittest.main()
