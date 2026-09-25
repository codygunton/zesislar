"""Gate launch checks with a fake guard and no project build."""

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


GATE = Path(__file__).resolve().parent / "det" / "gate.sh"


class GateCapTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        tools = self.root / "tools"
        (tools / "det").mkdir(parents=True)
        shutil.copy2(GATE, tools / "det" / "gate.sh")
        (self.root / "ZesuSsz/Evidence").mkdir(parents=True)
        checker = self.root / "ZesuSsz/Evidence/check_write_success_decoder.sh"
        checker.write_text("#!/bin/sh\nexit 0\n")
        guard = tools / "resource_guard.sh"
        guard.write_text(
            "#!/bin/sh\n"
            "case \"$1\" in\n"
            "  lock-status) echo 'no gate lock' ;;\n"
            "  gate-jobs) echo 24 ;;\n"
            "  reset-peak|window) : ;;\n"
            "  watch) sleep 100 ;;\n"
            "  report) echo fake ;;\n"
            "  peak) echo 0 ;;\n"
            "  batch) echo batch >> \"$GATE_TEST_BATCH_LOG\"; "
            "sleep \"${GATE_TEST_BATCH_SLEEP:-10}\" ;;\n"
            "esac\n")
        guard.chmod(0o755)
        binary = self.root / "bin"
        binary.mkdir()
        for name, body in {
            "systemctl": "#!/bin/sh\nexit 0\n",
            "pgrep": "#!/bin/sh\necho \"${GATE_TEST_COQC:-0}\"\n",
            "python3": (
                "#!/bin/sh\n"
                "if [ \"$1\" = tools/det/coqc_slots.py ]; then\n"
                "  if [ \"${GATE_TEST_DRAIN_FAIL:-0}\" = 1 ]; then\n"
                "    echo 'drain incomplete' >&2; exit 3\n"
                "  fi\n"
                "  if [ -e \"$GATE_TEST_SLOT_STATE\" ]; then\n"
                "    if [ \"${GATE_TEST_LIVE_FAIL:-0}\" = 1 ]; then\n"
                "      echo 'slot check failed' >&2; exit 2\n"
                "    fi\n"
                "    echo '0 0 48'\n"
                "  else\n"
                "    touch \"$GATE_TEST_SLOT_STATE\"; echo '24 0 0'\n"
                "  fi\n"
                "fi\n")
        }.items():
            path = binary / name
            path.write_text(body)
            path.chmod(0o755)
        self.batch_log = self.root / "batch.log"
        self.environment = dict(os.environ,
                                PATH=f"{binary}:{os.environ['PATH']}",
                                ZESU_GATE_LOCK=str(self.root / "gate.lock"),
                                ZESU_GATE_CAP_POLL_SECONDS="1",
                                GATE_TEST_BATCH_LOG=str(self.batch_log),
                                GATE_TEST_SLOT_STATE=str(self.root / "slots"))

    def gate(self, **changes):
        return subprocess.run(["bash", str(self.root / "tools/det/gate.sh"),
                               "check-iris", "gate.log"], cwd=self.root,
                              env=dict(self.environment, **changes),
                              capture_output=True, text=True, timeout=8)

    def test_drain_timeout_does_not_start_gate(self):
        result = self.gate(GATE_TEST_COQC="1", GATE_TEST_DRAIN_FAIL="1",
                           ZESU_GATE_DRAIN_SECONDS="0")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertFalse(self.batch_log.exists())

    def test_live_cap_drop_stops_gate(self):
        result = self.gate()
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn("gate stopped: width 24 exceeds 0 slots", result.stderr)
        self.assertEqual(self.batch_log.read_text().strip(), "batch")

    def test_short_green_gate_exits_before_next_cap_check(self):
        result = self.gate(GATE_TEST_BATCH_SLEEP="0.1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.batch_log.read_text().strip(), "batch")

    def test_live_slot_check_failure_stops_gate(self):
        result = self.gate(GATE_TEST_LIVE_FAIL="1")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn("gate stopped: coqc slot check failed", result.stderr)
        self.assertEqual(self.batch_log.read_text().strip(), "batch")


if __name__ == "__main__":
    unittest.main()
