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
        self.bin = base / "bin"
        self.bin.mkdir()
        fake_free = self.bin / "free"
        fake_free.write_text(
            "#!/bin/sh\n"
            "printf 'Mem: %s %s 0 0 0 %s\\n' "
            "\"$((251 * 1073741824))\" "
            "\"$((GUARD_TEST_USED_GIB * 1073741824))\" "
            "\"$(((251 - GUARD_TEST_USED_GIB) * 1073741824))\"\n"
        )
        fake_free.chmod(0o755)
        fake_systemd = self.bin / "systemd-run"
        fake_systemd.write_text("#!/bin/sh\nprintf '%s\\n' \"$@\"\n")
        fake_systemd.chmod(0o755)
        fake_systemctl = self.bin / "systemctl"
        fake_systemctl.write_text(
            "#!/bin/sh\n"
            "case \"$*\" in\n"
            "  *is-active*) exit 0 ;;\n"
            "  *kill*|*stop*) printf '%s\\n' \"$*\" >> \"$GUARD_TEST_SYSTEMCTL_LOG\" ;;\n"
            "esac\n"
        )
        fake_systemctl.chmod(0o755)
        self.environment["PATH"] = f"{self.bin}:{os.environ['PATH']}"
        self.environment["GUARD_TEST_USED_GIB"] = "40"
        self.environment["GUARD_TEST_SYSTEMCTL_LOG"] = str(base / "systemctl.log")
        for name in ("ZESU_GUARD", "ZESU_IN_GATE", "ZESU_IN_BATCH", "ZESU_ARM",
                     "ZESU_BATCH_LIMIT"):
            self.environment.pop(name, None)

    def tearDown(self):
        self.directory.cleanup()

    def guard(self, *arguments):
        return subprocess.run([str(GUARD), *arguments], capture_output=True,
                              text=True, env=self.environment)

    def test_subprocesses_do_not_inherit_guard_bypass_flags(self):
        for name in ("ZESU_GUARD", "ZESU_IN_GATE", "ZESU_IN_BATCH", "ZESU_ARM",
                     "ZESU_BATCH_LIMIT"):
            with self.subTest(name=name):
                self.assertNotIn(name, self.environment)

    def test_batch_fence_under_gate_environment(self):
        environment = {**os.environ, "ZESU_GUARD": "0", "ZESU_IN_GATE": "1",
                       "ZESU_IN_BATCH": "1", "ZESU_ARM": "1",
                       "ZESU_BATCH_LIMIT": "120G"}
        result = subprocess.run(
            [sys.executable, "-m", "unittest",
             "tools.test_guard.GuardLockTest.test_scope_and_batch_memory_fences"],
            capture_output=True, text=True, env=environment, cwd=TOOLS.parent)
        self.assertEqual(result.returncode, 0, result.stderr)

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

    def test_absolute_memory_thresholds(self):
        for used, expected in ((149, None), (150, "memory launch 150 GiB"),
                               (179, "memory launch 179 GiB"),
                               (180, "memory hold 180 GiB"),
                               (200, "memory hold 200 GiB")):
            with self.subTest(used=used):
                self.environment["GUARD_TEST_USED_GIB"] = str(used)
                result = self.guard("hold")
                self.assertEqual(result.returncode, 0)
                if expected:
                    self.assertIn(expected, result.stdout)
                else:
                    self.assertNotIn("memory", result.stdout)

    def test_scope_and_batch_memory_fences(self):
        for arguments, fence in (("scope", "MemoryMax=6G"),
                                 ("batch", "MemoryMax=150G")):
            with self.subTest(arguments=arguments):
                result = self.guard(arguments, "test", "--", "true")
                self.assertEqual(result.returncode, 0)
                self.assertIn(fence, result.stdout)
                self.assertIn("MemorySwapMax=0", result.stdout)

    def test_direct_batch_waits_at_launch_limit(self):
        self.environment["GUARD_TEST_USED_GIB"] = "150"
        result = subprocess.run(
            ["timeout", "0.2", str(GUARD), "batch", "test", "--", "true"],
            capture_output=True, text=True, env=self.environment)
        self.assertEqual(result.returncode, 124)
        self.assertNotIn("MemoryMax=150G", result.stdout)
        self.environment["GUARD_TEST_USED_GIB"] = "149"
        self.assertIn("MemoryMax=150G", self.guard("batch", "test", "--", "true").stdout)

    def test_gate_uses_120_gib_batch_fence(self):
        gate = (TOOLS / "det" / "gate.sh").read_text()
        self.assertIn("ZESU_BATCH_LIMIT=120G $guard batch", gate)

    def test_watch_kills_youngest_scope_at_200_gib(self):
        state = Path(self.environment["ZESU_GUARD_STATE"])
        state.mkdir()
        (state / "scopes").write_text("old.scope\nyoung.scope\n")
        log = Path(self.environment["GUARD_TEST_SYSTEMCTL_LOG"])
        self.environment["ZESU_GUARD_POLL"] = "0.05"
        self.environment["GUARD_TEST_USED_GIB"] = "199"
        subprocess.run(["timeout", "0.2", str(GUARD), "watch"],
                       capture_output=True, env=self.environment)
        self.assertFalse(log.exists())
        self.environment["GUARD_TEST_USED_GIB"] = "200"
        subprocess.run(["timeout", "0.2", str(GUARD), "watch"],
                       capture_output=True, env=self.environment)
        self.assertIn("young.scope", log.read_text())
        self.assertNotIn("old.scope", log.read_text())


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
