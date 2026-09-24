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
                            "ZESU_RAMP_FILE": str(base / "ramp"),
                            "ZESU_POPULATING_PREFIX": str(base / "pop"),
                            # No live job scope carries this prefix.
                            "ZESU_SCOPE_PREFIX": f"zesutest{os.getpid()}",
                            "ZESU_GUARD_POLL": "0.1",
                            # The live machine must not hold or kill here.
                            "ZESU_LAUNCH_GIB": "100000",
                            "ZESU_HOLD_GIB": "100000",
                            "ZESU_KILL_GIB": "100000",
                            "ZESU_MAX_COQC": "100000",
                            "ZESU_MAX_LOAD": "100000",
                            "ZESU_MAX_BLOCKED": "100000"}
        for name in ("ZESU_IN_GATE", "ZESU_IN_BATCH", "ZESU_ARM"):
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

    def test_locked_holds_the_lock_while_it_runs(self):
        done = self.guard("locked", "t", "--", "cat", str(self.lock))
        self.assertTrue(done.stdout.startswith("state=held "))

    def test_wanted_lock_holds_new_launches_not_running_batches(self):
        holder = subprocess.Popen(["sleep", "30"])
        try:
            done = self.guard("lock-want", str(holder.pid), "t")
            self.assertEqual(done.returncode, 0)
            self.assertTrue(self.lock.read_text().startswith("state=wanted "))
            self.assertIn("gate lock", self.guard("hold").stdout)
            waited = subprocess.run(
                ["timeout", "0.5", str(GUARD), "batch", "t", "--", "true"],
                capture_output=True, text=True, env=self.environment)
            self.assertEqual(waited.returncode, 124)
            self.environment["ZESU_IN_BATCH"] = "1"
            self.assertNotIn("gate lock", self.guard("hold").stdout)
            del self.environment["ZESU_IN_BATCH"]
            self.assertEqual(self.guard("lock-want", "1", "u").returncode, 3)
            self.assertEqual(self.guard("lock-hold", str(holder.pid)).returncode,
                             0)
            self.assertTrue(self.lock.read_text().startswith("state=held "))
        finally:
            holder.kill()
            holder.wait()

    def test_lock_hold_waits_for_running_scopes(self):
        fake = Path(self.directory.name) / "bin"
        fake.mkdir()
        (fake / "systemctl").write_text("#!/bin/sh\necho arm.scope\n")
        (fake / "systemctl").chmod(0o755)
        self.environment["PATH"] = f"{fake}:{os.environ['PATH']}"
        self.environment["ZESU_GATE_SCOPE_WAIT"] = "0"
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.guard("lock-want", str(holder.pid), "t")
            done = self.guard("lock-hold", str(holder.pid))
            self.assertEqual(done.returncode, 3)
            self.assertIn("job scopes still alive", done.stderr)
            self.assertFalse(self.lock.exists())
        finally:
            holder.kill()
            holder.wait()

    def test_memory_lines_are_absolute(self):
        self.environment["ZESU_LAUNCH_GIB"] = "0"
        self.assertIn("launch line 0", self.guard("hold").stdout)
        self.environment["ZESU_HOLD_GIB"] = "0"
        self.assertIn("at the 0 GiB hold", self.guard("hold").stdout)

    def test_direct_batch_waits_at_the_launch_line(self):
        self.environment["ZESU_LAUNCH_GIB"] = "0"
        done = subprocess.run(
            ["timeout", "0.3", str(GUARD), "batch", "t", "--", "true"],
            capture_output=True, text=True, env=self.environment)
        self.assertEqual(done.returncode, 124)

    def test_ramp_only_while_populating(self):
        def six_launches():
            started = time.monotonic()
            waits = [subprocess.Popen([str(GUARD), "wait"],
                                      env=self.environment)
                     for _ in range(6)]
            for process in waits:
                process.wait()
            return time.monotonic() - started

        self.environment["ZESU_DISK_BUSY_PERCENT"] = "1000"
        self.assertLess(six_launches(), 2.0)
        holder = subprocess.Popen(["sleep", "30"])
        marker = Path(self.directory.name) / f"pop.{holder.pid}"
        try:
            marker.write_text("x")
            self.assertGreaterEqual(six_launches(), 2.4)
        finally:
            holder.kill()
            holder.wait()
        self.guard("wait")
        self.assertFalse(marker.exists())

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
