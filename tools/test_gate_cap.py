"""Gate launch checks with a fake guard and no project build."""

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from test_guard import fixture_environment


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
            "  coqc-count) [ -z \"${GATE_TEST_COUNTER_FAIL:-}\" ] || exit \"$GATE_TEST_COUNTER_FAIL\"; "
            "echo \"${GATE_TEST_NONWRITER:-${GATE_TEST_COQC:-0}}\" ;;\n"
            "  reset-peak|window) : ;;\n"
            "  watch) sleep 100 ;;\n"
            "  report) [ -z \"${GATE_TEST_REPORT_FAIL:-}\" ] || exit \"$GATE_TEST_REPORT_FAIL\"; echo fake ;;\n"
            "  peak) echo 0 ;;\n"
            "  batch) echo batch >> \"$GATE_TEST_BATCH_LOG\"; "
            "sleep \"${GATE_TEST_BATCH_SLEEP:-10}\" ;;\n"
            "esac\n")
        guard.chmod(0o755)
        binary = self.root / "bin"
        binary.mkdir()
        for name, body in {
            "free": "#!/bin/sh\necho 'Mem: 2147483648 0 0 0 0 2147483648'\n",
            "systemctl": "#!/bin/sh\nexit 0\n",
            "pgrep": "#!/bin/sh\necho \"${GATE_TEST_COQC:-0}\"\n",
            "python3": (
                "#!/bin/sh\n"
                "if [ \"$1\" = tools/det/coqc_slots.py ]; then\n"
                "  echo \"$*\" >> \"$GATE_TEST_SLOT_ARGS\"\n"
                "  if [ \"${GATE_TEST_DRAIN_FAIL:-0}\" = 1 ]; then\n"
                "    echo 'drain incomplete' >&2; exit 3\n"
                "  fi\n"
                "  if [ -e \"$GATE_TEST_SLOT_STATE\" ]; then\n"
                "    if [ \"${GATE_TEST_LIVE_FAIL:-0}\" = 1 ]; then\n"
                "      echo 'slot check failed' >&2; exit 2\n"
                "    fi\n"
                "    if [ \"${GATE_TEST_WRITERS:-0}\" != 0 ]; then echo \"24 0 $GATE_TEST_WRITERS\"; else echo '0 0 48'; fi\n"
                "  else\n"
                "    touch \"$GATE_TEST_SLOT_STATE\"; echo '24 0 0'\n"
                "  fi\n"
                "fi\n")
        }.items():
            path = binary / name
            path.write_text(body)
            path.chmod(0o755)
        self.batch_log = self.root / "batch.log"
        self.environment = fixture_environment(
                                PATH=f"{binary}:{os.environ['PATH']}",
                                ZESU_GATE_LOCK=str(self.root / "gate.lock"),
                                ZESU_GATE_CAP_POLL_SECONDS="1",
                                GATE_TEST_BATCH_LOG=str(self.batch_log),
                                GATE_TEST_SLOT_ARGS=str(self.root / "slot-args.log"),
                                GATE_TEST_SLOT_STATE=str(self.root / "slots"))

    def gate(self, **changes):
        return subprocess.run(["bash", str(self.root / "tools/det/gate.sh"),
                               "check-iris", "gate.log"], cwd=self.root,
                              env=dict(self.environment, **changes),
                              capture_output=True, text=True, timeout=8)

    def test_explicit_updated_guard_admits_live_writers_in_gate_preflight(self):
        local = self.root / "tools/resource_guard.sh"
        updated = self.root / "updated-guard.sh"
        shutil.copy2(local, updated)
        local.write_text('#!/bin/sh\necho "OLD GUARD USED" >&2; exit 91\n')
        result = self.gate(ZESU_RESOURCE_GUARD=str(updated), GATE_TEST_COQC="16",
                           GATE_TEST_NONWRITER="0", GATE_TEST_WRITERS="16",
                           GATE_TEST_BATCH_SLEEP="1.2")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("gate check-iris with 24 jobs", result.stdout)
        self.assertIn("coqc nonwriter 0", result.stdout)
        self.assertEqual(self.batch_log.read_text().strip(), "batch")

    def test_preflight_and_monitor_pass_exact_own_build_store(self):
        result = self.gate(GATE_TEST_WRITERS="16", GATE_TEST_BATCH_SLEEP="1.2")
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = (self.root / "slot-args.log").read_text().splitlines()
        self.assertGreaterEqual(len(calls), 2)
        for call in calls:
            self.assertIn(f"--own-build-dir {self.root}/_build/agents/infra", call)
        self.assertIn("--drain-floor 0", calls[0])
        self.assertNotIn("--drain-floor", calls[1])

    def test_decoder_compile_runs_only_inside_guarded_gate_phase(self):
        checker = self.root / "ZesuSsz/Evidence/check_write_success_decoder.sh"
        record = self.root / "decoder-phase.log"
        checker.write_text(
            '#!/bin/sh\n'
            '[ "${ZESU_IN_BATCH:-}" = 1 ] && [ "${ZESU_AGGREGATE_LIMIT:-}" = 120G ] &&\n'
            '[ "${ZESU_AGGREGATE_SLICE:-}" = zesuaggregate1000p123r1.slice ] || exit 94\n'
            'printf "%s|%s|%s\\n" "$ZESU_AGGREGATE_SLICE" "$AGENT_BUILD_DIR" "$AGENT_JOBS" >> "$DECODER_PHASE_RECORD"\n')
        outside = subprocess.run(["bash", str(checker)],
                                 env={**self.environment, "DECODER_PHASE_RECORD": str(record)},
                                 capture_output=True, text=True)
        self.assertEqual(outside.returncode, 94)
        self.assertFalse(record.exists())
        guard = self.root / "tools/resource_guard.sh"
        guard.write_text(guard.read_text().replace(
            'sleep "${GATE_TEST_BATCH_SLEEP:-10}"',
            'shift 3; export ZESU_IN_BATCH=1 ZESU_AGGREGATE_SLICE=zesuaggregate1000p123r1.slice ZESU_AGGREGATE_LIMIT=120G; exec "$@"'))
        make = self.root / "bin/make"
        make.write_text(
            '#!/bin/sh\n'
            'for argument do case "$argument" in *=*) export "$argument" ;; esac; done\n'
            'exec bash ZesuSsz/Evidence/check_write_success_decoder.sh\n')
        make.chmod(0o755)
        result = self.gate(DECODER_PHASE_RECORD=str(record))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(record.read_text().splitlines(),
                         [f"zesuaggregate1000p123r1.slice|{self.root}/_build/agents/infra|24"])
        # The real Makefile retains the uncached executable check.
        makefile = (GATE.parents[2] / "Makefile").read_text()
        target = makefile.split("check-evidence-tools: startup-traces", 1)[1].split(".PHONY: check-fast", 1)[0]
        self.assertIn("bash ZesuSsz/Evidence/check_write_success_decoder.sh", target)

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

    def test_failed_compiler_counter_stops_gate_before_batch_launch(self):
        for status in (2, 3):
            with self.subTest(status=status):
                result = self.gate(GATE_TEST_COUNTER_FAIL=str(status))
                self.assertEqual(result.returncode, 3, result.stderr)
                self.assertIn("compiler snapshot failed during gate drain", result.stderr)
                self.assertFalse(self.batch_log.exists())

    def test_invalid_compiler_count_stops_gate_before_batch_launch(self):
        result = self.gate(GATE_TEST_NONWRITER="invalid")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertIn("invalid compiler count during gate drain", result.stderr)
        self.assertFalse(self.batch_log.exists())

    def test_failed_counter_report_stops_gate_before_batch_launch(self):
        result = self.gate(GATE_TEST_REPORT_FAIL="3")
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertFalse(self.batch_log.exists())


if __name__ == "__main__":
    unittest.main()
