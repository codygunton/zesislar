"""Tests for the resource guard's gate lock and ramp, and for prom.py."""

import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
GUARD = TOOLS / "resource_guard.sh"
sys.path.insert(0, str(TOOLS / "det"))

import prom  # noqa: E402


class GuardLockTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        base = Path(self.directory.name)
        self.lock = base / "lock"
        self.environment = {**os.environ,
                            "ZESU_GATE_LOCK": str(self.lock),
                            "ZESU_GUARD_STATE": str(base / "state"),
                            "ZESU_RAMP_FILE": str(base / "ramp")}
        for name in ("ZESU_IN_GATE", "ZESU_ARM"):
            self.environment.pop(name, None)

    def tearDown(self):
        self.directory.cleanup()

    def guard(self, *arguments):
        return subprocess.run([str(GUARD), *arguments], capture_output=True,
                              text=True, env=self.environment)

    def test_stale_lock_is_removed_and_reported(self):
        self.lock.write_text("holder=gone pid=999999999 start=x\n")
        done = self.guard("lock-status")
        self.assertIn("stale gate lock removed", done.stderr)
        self.assertFalse(self.lock.exists())

    def test_live_lock_holds_launches_and_refuses_a_second_gate(self):
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.lock.write_text(f"holder=t pid={holder.pid} start=x\n")
            self.assertIn("gate lock", self.guard("hold").stdout)
            self.assertEqual(self.guard("locked", "t", "--", "true").returncode,
                             3)
            self.environment["ZESU_IN_GATE"] = "1"
            self.assertNotIn("gate lock", self.guard("hold").stdout)
        finally:
            holder.kill()
            holder.wait()

    def test_locked_releases_its_lock(self):
        done = self.guard("locked", "t", "--", "cat", str(self.lock))
        self.assertEqual(done.returncode, 0)
        self.assertIn("holder=", done.stdout)
        self.assertFalse(self.lock.exists())

    def test_gate_jobs_caps(self):
        self.assertLessEqual(int(self.guard("gate-jobs").stdout), 24)
        self.assertLessEqual(int(self.guard("gate-jobs", "check-fast").stdout),
                             48)


class PromTest(unittest.TestCase):
    def test_window_renders_peak_and_p90(self):
        def fetch(_path, parameters):
            text = parameters["query"]
            value = "2" if text.startswith("quantile") else "4"
            if "MemTotal_bytes{" in text and "over_time" not in text:
                value = str(251 * prom.GIB)
            elif "filesystem" in text:
                value = str(400 * prom.GIB)
            elif "Mem" in text:
                value = str(int(value) * 10 * prom.GIB)
            return {"status": "success",
                    "data": {"result": [{"value": [0, value]}]}}

        end = time.time()
        line = prom.render(end - 3600, end, prom.window(end - 3600, end, fetch))
        self.assertIn("memory used peak 40.0 p90 20.0 of 251 GiB", line)
        self.assertIn("load5 peak 4 p90 2", line)
        self.assertIn("/home free 400 GiB", line)

    def test_error_reply_raises(self):
        with self.assertRaises(RuntimeError):
            prom.query("x", 0, lambda *_: {"status": "error", "error": "bad"})


if __name__ == "__main__":
    unittest.main()
