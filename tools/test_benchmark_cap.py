"""Tests for arm width changes without running an arm."""

import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "residual"))
import benchmark  # noqa: E402


class BenchmarkCapTest(unittest.TestCase):
    def test_guard_failure_stops_launch(self):
        with patch.object(benchmark.subprocess, "run",
                          side_effect=subprocess.CalledProcessError(7, "guard")):
            with self.assertRaises(subprocess.CalledProcessError):
                benchmark.launch_width(Path("."), 2)

    def test_probe_width_holds_new_launches_when_other_jobs_rise(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            current = {"slots": 2}
            with patch.object(benchmark.coqc_slots, "width",
                              side_effect=lambda *_: (current["slots"], 0, 0)):
                limiter = benchmark.ProbeWidth(2, root)
                limiter.acquire()
                current["slots"] = 0
                entered = threading.Event()
                thread = threading.Thread(target=lambda: (limiter.acquire(),
                                                           entered.set()))
                thread.start()
                time.sleep(0.05)
                self.assertFalse(entered.is_set())
                limiter.release()
                time.sleep(0.05)
                self.assertFalse(entered.is_set())
                current["slots"] = 1
                with limiter.condition:
                    limiter.condition.notify_all()
                self.assertTrue(entered.wait(1))
                limiter.release()
                thread.join(1)

    def test_build_stops_when_fixed_dune_width_exceeds_live_cap(self):
        class Process:
            pid = 12345

            def __init__(self):
                self.calls = 0

            def wait(self, timeout=None):
                self.calls += 1
                if self.calls == 1:
                    raise subprocess.TimeoutExpired("make", timeout)
                return -15

        process = Process()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(benchmark, "launch_width", return_value=24), \
                 patch.object(benchmark.subprocess, "Popen", return_value=process), \
                 patch.object(benchmark.coqc_slots, "width",
                              return_value=(23, 1, 25)), \
                 patch.object(benchmark.os, "killpg") as kill:
                with self.assertRaisesRegex(SystemExit, "width 24 exceeds 23 slots"):
                    benchmark.build(root, 48)
                kill.assert_called_once()


if __name__ == "__main__":
    unittest.main()
