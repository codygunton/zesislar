"""Tests for the resource guard's gate lock and ramp, and for prom.py."""

import os
import fcntl
import json
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


def fixture_environment(**changes):
    """Remove inherited build routes before a fixture sets its own routes."""
    environment = {name: value for name, value in os.environ.items()
                   if not name.startswith("ZESU_")}
    environment.pop("ROCQ_COQC_BINARY", None)
    environment.update(changes)
    return environment


class GuardLockTest(unittest.TestCase):
    def test_batch_scrubs_trace_before_returning_failure(self):
        from test_coqc_recipe import csexp

        (self.bin / "systemd-run").write_text(
            '#!/bin/sh\nwhile [ "$1" != -- ]; do shift; done; shift; exec "$@"\n')
        header = csexp(["config", "init", "1", ["env", ["TEST_KEY=private-value"]]])
        event = csexp(["process", "finish", "2", ["exit", "1"]])
        trace = Path(self.directory.name) / "trace.csexp"
        writer = Path(self.directory.name) / "write_trace.py"
        writer.write_text("import pathlib,sys\n"
                          f"pathlib.Path(sys.argv[2]).write_bytes({header + event!r})\n"
                          "raise SystemExit(7)\n")
        result = self.guard("batch", "trace", "--", sys.executable,
                            str(writer), "--trace-file", str(trace))
        self.assertEqual(result.returncode, 7, result.stderr)
        self.assertEqual(trace.read_bytes(), event)
        self.assertNotIn("private-value", result.stdout + result.stderr)

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        base = Path(self.directory.name)
        self.lock = base / "lock"
        self.environment = {**fixture_environment(),
                            "ZESU_GATE_LOCK": str(self.lock),
                            "ZESU_GUARD_STATE": str(base / "state"),
                            "ZESU_RAMP_FILE": str(base / "ramp"),
                            "ZESU_SCOPE_PREFIX": f"zesutest{os.getpid()}",
                            "ZESU_GUARD_POLL": "0.1",
                            "ZESU_MAX_COQC": "100000",
                            "ZESU_MAX_LOAD": "100000",
                            "ZESU_MAX_BLOCKED": "100000"}
        self.bin = base / "bin"
        self.bin.mkdir()
        self.cgroup = base / "controller-cgroup"
        self.cgroup.write_text("0::/user.slice/user-1000.slice/user@1000.service/app.slice/fixture.scope\n")
        self.environment["GUARD_TEST_CONTROLLER_CGROUP"] = str(self.cgroup)
        fake_cat = self.bin / "cat"
        fake_cat.write_text(
            '#!/bin/sh\n'
            'if [ "$#" = 1 ]; then\n'
            ' case "$1" in\n'
            '  /proc/*/cgroup)\n'
            '   pid=${1#/proc/}; pid=${pid%/cgroup}\n'
            '   case "$pid" in\n'
            '    ""|*[!0-9]*) ;;\n'
            '    *) exec /usr/bin/cat "$GUARD_TEST_CONTROLLER_CGROUP" ;;\n'
            '   esac ;;\n'
            ' esac\n'
            'fi\n'
            'exec /usr/bin/cat "$@"\n')
        fake_cat.chmod(0o755)
        fake_free = self.bin / "free"
        fake_free.write_text(
            "#!/bin/sh\n"
            "printf 'Mem: %s %s 0 0 0 %s\\n' "
            "\"$((251 * 1073741824))\" "
            "\"$((GUARD_TEST_USED_GIB * 1073741824))\" "
            "\"$(((251 - GUARD_TEST_USED_GIB) * 1073741824))\"\n"
        )
        fake_free.chmod(0o755)
        # Guard fixtures must not inspect or trim the shared host cache.
        fake_df = self.bin / "df"
        fake_df.write_text("#!/bin/sh\nprintf 'Avail\\n60000000000\\n'\n")
        fake_df.chmod(0o755)
        fake_systemd = self.bin / "systemd-run"
        fake_systemd.write_text("#!/bin/sh\nprintf '%s\\n' \"$@\"\n")
        fake_systemd.chmod(0o755)
        fake_systemctl = self.bin / "systemctl"
        fake_systemctl.write_text(
            "#!/usr/bin/env python3\n"
            "import json,os,pathlib,sys\n"
            "args=sys.argv[1:];state=pathlib.Path(os.environ['GUARD_TEST_SLICE_STATE'])\n"
            "data=json.loads(state.read_text()) if state.exists() else {}\n"
            "if 'set-property' in args:\n"
            " if os.environ.get('GUARD_TEST_SLICE_FAIL'):sys.exit(1)\n"
            " unit=args[args.index('--runtime')+1];data[unit]=dict(x.split('=',1) for x in args if '=' in x)\n"
            " state.write_text(json.dumps(data))\n"
            "elif 'show' in args:\n"
            " unit=args[args.index('show')+1]\n"
            " for key,value in data.get(unit,{}).items():\n"
            "  if value.endswith('G'):value=str(int(value[:-1])*1073741824)\n"
            "  print(key+'='+value)\n"
            "elif 'list-units' in args:\n"
            " live=os.environ.get('GUARD_TEST_LIVE_SCOPES')\n"
            " if live:print(pathlib.Path(live).read_text(),end='')\n"
            "elif 'kill' in args or 'stop' in args:\n"
            " with open(os.environ['GUARD_TEST_SYSTEMCTL_LOG'],'a') as f:f.write(' '.join(args)+'\\n')\n"
        )
        fake_systemctl.chmod(0o755)
        self.environment["PATH"] = f"{self.bin}:{os.environ['PATH']}"
        self.environment["GUARD_TEST_USED_GIB"] = "40"
        state = base / "state"
        state.mkdir(exist_ok=True)
        (state / "disk-busy").write_text(f"{int(time.time()) + 60} 0\n")
        self.environment["GUARD_TEST_SYSTEMCTL_LOG"] = str(base / "systemctl.log")
        self.environment["GUARD_TEST_SLICE_STATE"] = str(base / "slice-state.json")
        for name in ("ZESU_GUARD", "ZESU_IN_GATE", "ZESU_IN_BATCH", "ZESU_ARM",
                     "ZESU_BATCH_LIMIT", "ZESU_IO", "ZESU_WRITER_ID",
                     "ZESU_RESOURCE_GUARD", "ZESU_COQC_RESERVATION", "ZESU_COQC_SCOPE",
                     "ZESU_AGGREGATE_SLICE", "ZESU_AGGREGATE_LIMIT"):
            self.environment.pop(name, None)

    def tearDown(self):
        self.directory.cleanup()

    def guard(self, *arguments):
        return subprocess.run([str(GUARD), *arguments], capture_output=True,
                              text=True, env=self.environment, timeout=10)

    def batch_environment(self, limit="150G"):
        slice_name = f"zesuaggregate1000p{os.getpid()}r1.slice"
        subprocess.run(["systemctl", "--user", "set-property", "--runtime", slice_name,
                        f"MemoryMax={limit}", "MemorySwapMax=0"],
                       env=self.environment, check=True)
        return {"ZESU_IN_BATCH": "1", "ZESU_AGGREGATE_SLICE": slice_name,
                "ZESU_AGGREGATE_LIMIT": limit}

    def prepare_blocked_fixture(self, blocked):
        base = Path(self.directory.name)
        count = base / "blocked-count"
        count.write_text(f"{blocked}\n")
        self.environment["GUARD_TEST_BLOCKED_COUNT"] = str(count)
        self.environment["ZESU_MAX_BLOCKED"] = "16"
        self.environment["ZESU_POPULATING_PREFIX"] = str(base / "populating")
        self.environment["ZESU_DISK_BUSY_PERCENT"] = "100000"
        fake_awk = self.bin / "awk"
        fake_awk.write_text(
            '#!/bin/sh\n'
            'case "$1" in\n'
            '  *procs_blocked*) cat "$GUARD_TEST_BLOCKED_COUNT" ;;\n'
            '  *) exec /usr/bin/awk "$@" ;;\n'
            'esac\n')
        fake_awk.chmod(0o755)
        fake_pgrep = self.bin / "pgrep"
        fake_pgrep.write_text('#!/bin/sh\nprintf "0\\n"\n')
        fake_pgrep.chmod(0o755)
        return count

    def writer_fixture(self, state="wanted", count=0):
        self.prepare_blocked_fixture(0)
        counter = Path(self.directory.name) / "coqc-count"
        counter.write_text(f"{count}\n")
        (self.bin / "pgrep").write_text('#!/bin/sh\ncount=$(cat "$GUARD_TEST_COQC_COUNT"); seq 1 "$count"\n')
        self.environment.update(GUARD_TEST_COQC_COUNT=str(counter), ZESU_MAX_COQC="48",
                                ZESU_PROC_ROOT=str(Path(self.directory.name) / "proc"))
        self.lock.write_text(f"state={state} holder=fixture pid={os.getpid()} start=x\n")
        return counter

    def reserve_writer(self, writer):
        result = subprocess.run([str(GUARD), "reserve-coqc", str(os.getpid())],
                                env={**self.environment, "ZESU_WRITER_ID": writer},
                                capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.strip())
        token = result.stdout.strip()
        confirmed = subprocess.run([str(GUARD), "confirm-coqc", token],
                                   env={**self.environment, "ZESU_WRITER_ID": writer},
                                   capture_output=True, text=True, timeout=3)
        self.assertEqual(confirmed.returncode, 0, confirmed.stderr)
        return token

    def assert_launch_waits(self, arguments, environment, reason):
        process = subprocess.Popen([str(GUARD), *arguments], env=environment,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            log = Path(self.environment["ZESU_GUARD_STATE"]) / "guard.log"
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline and process.poll() is None:
                if log.exists() and reason in log.read_text():
                    break
                time.sleep(0.02)
            self.assertIsNone(process.poll())
            self.assertIn(reason, log.read_text())
        finally:
            process.terminate()
            process.communicate(timeout=3)

    def test_empty_compiler_snapshots_allow_counts_and_admission(self):
        self.prepare_blocked_fixture(0)
        for status in (0, 1):
            with self.subTest(status=status):
                (self.bin / "pgrep").write_text(f"#!/bin/sh\nexit {status}\n")
                for arguments in (("coqc-count",), ("coqc-count", "nonwriter")):
                    result = self.guard(*arguments)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stdout.strip(), "0")
                self.assertEqual(self.guard("wait").returncode, 0)
                self.assertEqual(self.guard("hold").stdout.strip(), "none")
                result = self.guard("reserve-coqc", str(os.getpid()))
                self.assertEqual(result.returncode, 0, result.stderr)
                token = result.stdout.strip()
                self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
                self.guard("release-coqc", token)

    def test_failed_compiler_snapshots_refuse_all_counter_callers(self):
        self.prepare_blocked_fixture(0)
        (self.bin / "pgrep").write_text("#!/bin/sh\nexit 1\n")
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        try:
            for status in (2, 3, 127):
                for output in ("", "9000000\\n"):
                    with self.subTest(status=status, output=output):
                        (self.bin / "pgrep").write_text(
                            f"#!/bin/sh\nprintf '{output}'\nexit {status}\n")
                        commands = (("coqc-count",), ("coqc-count", "nonwriter"),
                                    ("hold",), ("wait",), ("report",),
                                    ("confirm-coqc", token))
                        for arguments in commands:
                            result = self.guard(*arguments)
                            self.assertEqual(result.returncode, status,
                                             (arguments, result.stderr))
                            self.assertEqual(result.stdout, "")
                            self.assertIn("compiler snapshot failed", result.stderr)
                        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
                        self.assertEqual(list(reservations.iterdir()), [])
        finally:
            self.guard("release-coqc", token)

    def test_failed_admission_snapshot_after_successful_hold_refuses_reservation(self):
        self.prepare_blocked_fixture(0)
        counter = Path(self.directory.name) / "snapshot-call-count"
        self.environment["GUARD_TEST_SNAPSHOT_CALLS"] = str(counter)
        (self.bin / "pgrep").write_text(
            '#!/bin/sh\nfile="$GUARD_TEST_SNAPSHOT_CALLS"\n'
            'count=0; [ ! -f "$file" ] || count=$(cat "$file")\n'
            'count=$((count + 1)); echo "$count" > "$file"\n'
            'if [ "$count" = 1 ]; then exit 1; else exit 3; fi\n')
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        result = self.guard("confirm-coqc", token)
        self.assertEqual(result.returncode, 3, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertEqual(counter.read_text().strip(), "2")
        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        self.assertEqual(list(reservations.iterdir()), [])

    def test_failed_confirmation_snapshot_after_successful_hold_refuses_launch(self):
        self.prepare_blocked_fixture(0)
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        counter = Path(self.directory.name) / "snapshot-call-count"
        self.environment["GUARD_TEST_SNAPSHOT_CALLS"] = str(counter)
        (self.bin / "pgrep").write_text(
            '#!/bin/sh\nfile="$GUARD_TEST_SNAPSHOT_CALLS"\n'
            'count=0; [ ! -f "$file" ] || count=$(cat "$file")\n'
            'count=$((count + 1)); echo "$count" > "$file"\n'
            'if [ "$count" = 1 ]; then exit 1; else exit 2; fi\n')
        try:
            result = self.guard("confirm-coqc", token)
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertEqual(result.stdout, "")
            self.assertEqual(counter.read_text().strip(), "2")
            self.assertFalse(Path(token).exists())
        finally:
            self.guard("release-coqc", token)

    def test_failed_snapshot_prevents_scope_and_batch_commands(self):
        self.prepare_blocked_fixture(0)
        executed = Path(self.directory.name) / "command-executed"
        for status in (2, 3):
            (self.bin / "pgrep").write_text(f"#!/bin/sh\nexit {status}\n")
            for arguments, extra in (
                (("scope", "failure", "--", "touch", str(executed)), {}),
                (("batch", "failure", "--", "touch", str(executed)), {}),
                (("batch", "nested", "--", "touch", str(executed)), {"ZESU_IN_BATCH": "1"}),
            ):
                with self.subTest(status=status, arguments=arguments):
                    result = subprocess.run([str(GUARD), *arguments],
                                            env={**self.environment, **extra},
                                            capture_output=True, text=True, timeout=3)
                    self.assertEqual(result.returncode, status, result.stderr)
                    self.assertFalse(executed.exists())

    def test_failed_snapshot_prevents_scope_exec_command(self):
        self.prepare_blocked_fixture(0)
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        executed = Path(self.directory.name) / "command-executed"
        try:
            for status in (2, 3):
                (self.bin / "pgrep").write_text(f"#!/bin/sh\nexit {status}\n")
                result = self.guard("scope-exec", token, "--", "touch", str(executed))
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertFalse(executed.exists())
                self.assertFalse(Path(token).exists())
        finally:
            self.guard("release-coqc", token)

    def test_writer_admission_under_wanted_and_held_gates(self):
        for state in ("wanted", "held"):
            with self.subTest(state=state):
                self.writer_fixture(state)
                self.environment["ZESU_WRITER_ID"] = "tail-fields-2"
                token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
                self.assertTrue(token)
                try:
                    self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
                    self.assertEqual(self.guard("hold").stdout.strip(), "none")
                    self.environment.pop("ZESU_WRITER_ID")
                    self.assertEqual(self.guard("confirm-coqc", token).returncode, 2)
                    self.assertIn("gate lock", self.guard("hold").stdout)
                finally:
                    self.guard("release-coqc", token)

    def test_gate_leaves_16_slots_and_admits_all_16_writers(self):
        counter = self.writer_fixture(count=32)
        self.environment["ZESU_IN_GATE"] = "1"
        request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                 "16 slots reserved for writers")
        tokens = [self.reserve_writer(f"writer-{i // 2}") for i in range(16)]
        try:
            self.assertEqual(len(tokens), 16)
            request = subprocess.run([str(GUARD), "reserve-coqc", str(os.getpid())],
                                     env={**self.environment, "ZESU_WRITER_ID": "ninth"},
                                     check=True, capture_output=True, text=True).stdout.strip()
            self.assert_launch_waits(["confirm-coqc", request],
                                     {**self.environment, "ZESU_WRITER_ID": "ninth"},
                                     "reservations machine-wide")
            counter.write_text("0\n")
            request = subprocess.run([str(GUARD), "reserve-coqc", str(os.getpid())],
                                     env={**self.environment, "ZESU_WRITER_ID": "ninth"},
                                     check=True, capture_output=True, text=True).stdout.strip()
            self.assert_launch_waits(["confirm-coqc", request],
                                     {**self.environment, "ZESU_WRITER_ID": "ninth"},
                                     "16 reserved slots")
        finally:
            for token in tokens:
                self.guard("release-coqc", token)

    def test_each_writer_has_two_slots_even_with_gate_flag(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_IN_GATE="1")
        tokens = [self.reserve_writer("tf2") for _ in range(2)]
        try:
            request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
            self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                     "writer tf2 at its 2 compiler limit")
        finally:
            for token in tokens:
                self.guard("release-coqc", token)

    def test_gate_does_not_wait_for_writer_reservations_or_scopes(self):
        self.writer_fixture()
        token = self.reserve_writer("tf2")
        (self.bin / "systemctl").write_text(
            '#!/bin/sh\nprintf "zesutest-writer-tf2-coqc.scope loaded active running\n"\n')
        try:
            self.assertEqual(self.guard("lock-hold", str(os.getpid())).returncode, 0)
            self.assertIn("state=held", self.lock.read_text())
        finally:
            self.guard("release-coqc", token)

    def test_writer_does_not_bypass_memory_blocked_or_machine_limits(self):
        counter = self.writer_fixture()
        self.environment["ZESU_WRITER_ID"] = "tf2"
        self.environment["GUARD_TEST_USED_GIB"] = "226"
        request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                 "memory available 25 GiB")
        self.environment["GUARD_TEST_USED_GIB"] = "40"
        Path(self.environment["GUARD_TEST_BLOCKED_COUNT"]).write_text("17\n")
        request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                 "blocked 17")
        Path(self.environment["GUARD_TEST_BLOCKED_COUNT"]).write_text("16\n")
        counter.write_text("48\n")
        request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                 "coqc 48 machine-wide")

    def test_writer_reservation_rechecks_nonwriter_cap_before_launch(self):
        counter = self.writer_fixture(count=31)
        self.environment["ZESU_IN_GATE"] = "1"
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assertTrue(token)
        try:
            counter.write_text("32\n")
            self.assert_launch_waits(["confirm-coqc", token], self.environment,
                                     "16 slots reserved for writers")
            counter.write_text("31\n")
            self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
        finally:
            self.guard("release-coqc", token)

    def test_reserved_compiler_absent_from_pid_snapshot_keeps_its_slot(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_MAX_COQC="1")
        token = self.reserve_writer("tf2")
        fake_pid = "9000000"
        proc = Path(self.environment["ZESU_PROC_ROOT"]) / fake_pid
        proc.mkdir(parents=True)
        (proc / "comm").write_text("coqc\n")
        self.assertEqual(self.guard("mark-coqc", token, fake_pid).returncode, 0)
        # A marked compiler occupies a slot before the next PID snapshot.
        try:
            request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
            self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                     "coqc 0 with 1 reservations machine-wide")
        finally:
            self.guard("release-coqc", token)

    def test_gate_counter_excludes_live_writer_and_shell_wrapper(self):
        self.writer_fixture()
        token = self.reserve_writer("tf2")
        proc = Path(self.environment["ZESU_PROC_ROOT"])
        for pid in (9000000, 9000001, 9000002):
            entry = proc / str(pid)
            entry.mkdir(parents=True)
            (entry / "comm").write_text("coqc\n")
        (proc / "9000002/exe").symlink_to("/bin/bash")
        self.assertEqual(self.guard("mark-coqc", token, "9000000").returncode, 0)
        snapshot = Path(self.directory.name) / "pids"
        snapshot.write_text("9000000\n9000001\n9000002\n")
        (self.bin / "pgrep").write_text('#!/bin/sh\ncat "$GUARD_TEST_PIDS"\n')
        self.environment["GUARD_TEST_PIDS"] = str(snapshot)
        try:
            for state in ("wanted", "held"):
                self.lock.write_text(f"state={state} holder=fixture pid={os.getpid()} start=x\n")
                self.assertEqual(self.guard("coqc-count").stdout.strip(), "2")
                self.assertEqual(self.guard("coqc-count", "nonwriter").stdout.strip(), "1")
            snapshot.write_text("9000000\n9000002\n")
            self.assertEqual(self.guard("coqc-count", "nonwriter").stdout.strip(), "0")
        finally:
            self.guard("release-coqc", token)

    def test_writer_confirmation_rechecks_blocked_and_memory(self):
        self.writer_fixture()
        self.environment["ZESU_WRITER_ID"] = "tf2"
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        try:
            Path(self.environment["GUARD_TEST_BLOCKED_COUNT"]).write_text("17\n")
            self.assert_launch_waits(["confirm-coqc", token], self.environment, "blocked 17")
            Path(self.environment["GUARD_TEST_BLOCKED_COUNT"]).write_text("16\n")
            self.environment["GUARD_TEST_USED_GIB"] = "226"
            self.assert_launch_waits(["confirm-coqc", token], self.environment, "memory available 25 GiB")
            self.environment["GUARD_TEST_USED_GIB"] = "40"
            self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
        finally:
            self.guard("release-coqc", token)

    def test_admitted_scope_drains_before_a_new_gate(self):
        self.prepare_blocked_fixture(0)
        (self.bin / "systemd-run").write_text(
            '#!/bin/sh\n'
            'printf "state=wanted holder=fixture pid=%s start=x\n" "$FAKE_GATE_PID" > "$ZESU_GATE_LOCK"\n'
            'while [ "$1" != -- ]; do shift; done; shift; exec "$@"\n')
        self.environment["FAKE_GATE_PID"] = str(os.getpid())
        result = subprocess.run([str(GUARD), "scope", "fixture", "--", "/bin/echo", "WRONG"],
                                env=self.environment, capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("WRONG", result.stdout)
        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        self.assertEqual(list(reservations.iterdir()), [])
        self.assertEqual(self.guard("lock-hold", str(os.getpid())).returncode, 0)

    def test_writer_identity_validation_and_batch_refusal(self):
        self.prepare_blocked_fixture(0)
        self.environment["ZESU_WRITER_ID"] = "../../bad"
        self.assertEqual(self.guard("reserve-coqc", str(os.getpid())).returncode, 2)
        self.environment["ZESU_WRITER_ID"] = "tf2"
        self.assertEqual(self.guard("batch", "bad", "--", "true").returncode, 2)

    def test_direct_launches_hold_at_17_and_resume_at_16(self):
        count = self.prepare_blocked_fixture(17)
        modes = ({}, {"ZESU_IN_GATE": "1"}, self.batch_environment())
        for command in ("scope", "batch"):
            for mode in modes:
                with self.subTest(command=command, mode=mode):
                    count.write_text("17\n")
                    log = Path(self.environment["ZESU_GUARD_STATE"]) / "guard.log"
                    previous = log.stat().st_size if log.exists() else 0
                    process = subprocess.Popen(
                        [str(GUARD), command, "blocked-test", "--",
                         "/bin/echo", "LAUNCHED"],
                        env={**self.environment, **mode}, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                    try:
                        deadline = time.monotonic() + 3
                        while time.monotonic() < deadline:
                            if process.poll() is not None:
                                break
                            if log.exists() and "HOLD blocked 17" in log.read_text()[previous:]:
                                break
                            time.sleep(0.02)
                        self.assertIsNone(process.poll(), "launch bypassed the blocked limit")
                        self.assertIn("HOLD blocked 17", log.read_text()[previous:])
                        count.write_text("16\n")
                        stdout, stderr = process.communicate(timeout=5)
                        self.assertEqual(process.returncode, 0, stderr)
                        self.assertIn("LAUNCHED", stdout)
                        self.assertIn("RESUME", log.read_text()[previous:])
                    finally:
                        if process.poll() is None:
                            process.terminate()
                        process.communicate(timeout=3)

    def test_reservation_rechecks_blocked_under_gate_owner_exemption(self):
        count = self.prepare_blocked_fixture(16)
        self.environment["ZESU_IN_GATE"] = "1"
        self.lock.write_text(f"state=wanted holder=t pid={os.getpid()} start=x\n")
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assertTrue(token)
        count.write_text("17\n")
        process = subprocess.Popen([str(GUARD), "confirm-coqc", token],
                                   env=self.environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            time.sleep(0.2)
            self.assertIsNone(process.poll())
            count.write_text("16\n")
            _, stderr = process.communicate(timeout=3)
            self.assertEqual(process.returncode, 0, stderr)
            self.assertTrue(self.lock.exists())
        finally:
            if process.poll() is None:
                process.terminate()
            process.communicate(timeout=3)
            self.guard("release-coqc", token)
        self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
        self.assertTrue(Path(token).exists())
        self.guard("release-coqc", token)

    def test_confirmation_refuses_a_foreign_gate_without_waiting_on_it(self):
        self.prepare_blocked_fixture(0)
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assertTrue(token)
        self.lock.write_text(f"state=wanted holder=t pid={os.getpid()} start=x\n")
        try:
            result = self.guard("confirm-coqc", token)
            self.assertEqual(result.returncode, 3)
            self.assertIn("confirmation refused by gate lock", result.stderr)
        finally:
            self.guard("release-coqc", token)
        self.assertEqual(self.guard("lock-hold", str(os.getpid())).returncode, 0)

    def test_reservation_rechecks_the_48_machine_cap(self):
        self.prepare_blocked_fixture(0)
        count = Path(self.directory.name) / "coqc-count"
        count.write_text("47\n")
        (self.bin / "pgrep").write_text('#!/bin/sh\ncount=$(cat "$GUARD_TEST_COQC_COUNT"); seq 1 "$count"\n')
        self.environment["GUARD_TEST_COQC_COUNT"] = str(count)
        self.environment["ZESU_MAX_COQC"] = "48"
        self.environment["ZESU_PROC_ROOT"] = str(Path(self.directory.name) / "proc")
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assertTrue(token)
        count.write_text("48\n")
        process = subprocess.Popen([str(GUARD), "confirm-coqc", token],
                                   env=self.environment, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            time.sleep(0.2)
            self.assertIsNone(process.poll())
            count.write_text("47\n")
            _, stderr = process.communicate(timeout=3)
            self.assertEqual(process.returncode, 0, stderr)
        finally:
            if process.poll() is None:
                process.terminate()
            process.communicate(timeout=3)
            self.guard("release-coqc", token)

    def test_confirmed_coqc_reservations_keep_the_48_cap(self):
        base = Path(self.directory.name)
        count = base / "coqc-count"
        count.write_text("47\n")
        fake_pgrep = self.bin / "pgrep"
        fake_pgrep.write_text('#!/bin/sh\ncount=$(cat "$GUARD_TEST_COQC_COUNT"); '
                              'seq 1 "$((count - 1))"; echo 12345\n')
        fake_pgrep.chmod(0o755)
        self.environment["GUARD_TEST_COQC_COUNT"] = str(count)
        self.environment["ZESU_MAX_COQC"] = "48"
        self.environment["ZESU_PROC_ROOT"] = str(Path(self.directory.name) / "proc")
        self.environment["ZESU_IN_BATCH"] = "1"
        proc = base / "proc" / "12345"
        proc.mkdir(parents=True)
        (proc / "comm").write_text("coqc\n")
        self.environment["ZESU_PROC_ROOT"] = str(proc.parent)
        first = self.guard("reserve-coqc", str(os.getpid()))
        self.assertEqual(first.returncode, 0, first.stderr)
        first_token = first.stdout.strip()
        confirmed = self.guard("confirm-coqc", first_token)
        self.assertEqual(confirmed.returncode, 0, confirmed.stderr)
        second_token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        second = subprocess.Popen(
            [str(GUARD), "confirm-coqc", second_token],
            env=self.environment, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            time.sleep(0.2)
            self.assertIsNone(second.poll())
            marked = self.guard("mark-coqc", first_token, "12345")
            self.assertEqual(marked.returncode, 0, marked.stderr)
            count.write_text("48\n")
            time.sleep(0.2)
            self.assertIsNone(second.poll())
            count.write_text("47\n")
            stdout, stderr = second.communicate(timeout=3)
            self.assertEqual(second.returncode, 0, stderr)
            self.assertEqual(stdout, "")
            self.assertTrue(Path(second_token).exists())
        finally:
            if second.poll() is None:
                second.terminate()
                second.wait(timeout=3)
            self.guard("release-coqc", first_token)
            if second_token:
                self.guard("release-coqc", second_token)

    def test_pending_reservations_do_not_block_confirmation(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_MAX_COQC="1")
        tokens = [self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
                  for _ in range(3)]
        self.assertTrue(all(tokens))
        try:
            result = subprocess.run([str(GUARD), "confirm-coqc", tokens[0]],
                                    env=self.environment, capture_output=True,
                                    text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(tokens[0]).read_text().splitlines()[0], "confirmed")
            self.assert_launch_waits(["confirm-coqc", tokens[1]], self.environment,
                                     "coqc 0 with 1 reservations machine-wide")
            self.guard("release-coqc", tokens[0])
            result = subprocess.run([str(GUARD), "confirm-coqc", tokens[1]],
                                    env=self.environment, capture_output=True,
                                    text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
        finally:
            for token in tokens:
                self.guard("release-coqc", token)

    def test_confirmation_does_not_count_its_own_slot_twice(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_MAX_COQC="1")
        token = self.reserve_writer("tf2")
        try:
            result = subprocess.run([str(GUARD), "confirm-coqc", token],
                                    env=self.environment, capture_output=True,
                                    text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
        finally:
            self.guard("release-coqc", token)

    def test_96_dead_owner_confirmations_do_not_block_a_compiler(self):
        self.writer_fixture()
        self.lock.unlink()
        directory = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        directory.mkdir(exist_ok=True)
        expired = []
        for index in range(96):
            marker = directory / f"9000000.gate-{index // 32}.{index}"
            marker.write_text("confirmed\nwriter=\naggregate=\n")
            os.utime(marker, (time.time() - 120, time.time() - 120))
            expired.append(marker)
        token = directory / f"{os.getpid()}.launch"
        token.write_text("pending\nwriter=\naggregate=\n")
        result = subprocess.run([str(GUARD), "confirm-coqc", str(token)],
                                env=self.environment, capture_output=True,
                                text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(token.read_text().splitlines()[0], "confirmed")
        self.assertTrue(all(not marker.exists() for marker in expired))
        executed = Path(self.directory.name) / "executed"
        result = subprocess.run([str(GUARD), "scope-exec", str(token),
                                 "--", "touch", str(executed)],
                                env=self.environment, capture_output=True,
                                text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(executed.exists())

    def test_live_compilers_and_fresh_confirmations_share_the_48_cap(self):
        self.writer_fixture(count=40)
        self.lock.unlink()
        directory = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        directory.mkdir(exist_ok=True)
        launching = []
        for index in range(8):
            marker = directory / f"{os.getpid()}.launching-{index}"
            marker.write_text("confirmed\nwriter=\naggregate=\n")
            launching.append(marker)
        token = directory / f"{os.getpid()}.pending"
        token.write_text("pending\nwriter=\naggregate=\n")
        self.assert_launch_waits(["confirm-coqc", str(token)], self.environment,
                                 "coqc 40 with 8 reservations machine-wide")
        for marker in launching:
            self.guard("release-coqc", str(marker))
        result = subprocess.run([str(GUARD), "confirm-coqc", str(token)],
                                env=self.environment, capture_output=True,
                                text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(all(not marker.exists() for marker in launching))

    def test_confirmed_slot_drains_while_admission_mutex_is_held(self):
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        self.assertEqual(self.guard("confirm-coqc", token).returncode, 0)
        try:
            with open(str(self.lock) + ".mutex", "a") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                result = subprocess.run(
                    [str(GUARD), "confirm-coqc", token], env=self.environment,
                    text=True, capture_output=True, timeout=2)
                self.assertEqual(result.returncode, 0, result.stderr)
        finally:
            self.guard("release-coqc", token)

    def test_old_own_confirmation_remains_valid_before_launch(self):
        self.writer_fixture()
        token = Path(self.reserve_writer("tf2"))
        os.utime(token, (time.time() - 120, time.time() - 120))
        executed = Path(self.directory.name) / "executed"
        result = subprocess.run([str(GUARD), "scope-exec", str(token),
                                 "--", "touch", str(executed)],
                                env={**self.environment, "ZESU_WRITER_ID": "tf2"},
                                capture_output=True, text=True, timeout=3)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(executed.exists())
        log = Path(self.environment["ZESU_GUARD_STATE"]) / "guard.log"
        self.assertNotIn("RETRY reservation", log.read_text() if log.exists() else "")

    def test_old_marked_wrapper_with_live_nested_compiler_keeps_its_slot(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_MAX_COQC="1")
        token = Path(self.reserve_writer("tf2"))
        proc = Path(self.environment["ZESU_PROC_ROOT"])
        for pid, name, children in ((9000000, "bash", "9000001"),
                                    (9000001, "python", "9000002"),
                                    (9000002, "coqc", "")):
            entry = proc / str(pid)
            (entry / "task" / str(pid)).mkdir(parents=True)
            (entry / "comm").write_text(name + "\n")
            (entry / "task" / str(pid) / "children").write_text(children)
        self.assertEqual(self.guard("mark-coqc", str(token), "9000000").returncode, 0)
        os.utime(token, (time.time() - 120, time.time() - 120))
        try:
            request = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
            self.assert_launch_waits(["confirm-coqc", request], self.environment,
                                     "coqc 0 with 1 reservations machine-wide")
            self.assertTrue(token.exists())
        finally:
            self.guard("release-coqc", str(token))

    def test_marking_does_not_extend_the_confirmation_timeout(self):
        self.writer_fixture()
        token = Path(self.reserve_writer("tf2"))
        confirmed = time.time() - 30
        os.utime(token, (confirmed, confirmed))
        self.assertEqual(self.guard("mark-coqc", str(token), str(os.getpid())).returncode, 0)
        self.assertAlmostEqual(token.stat().st_mtime, confirmed, places=4)

    def test_dead_reservation_owner_and_child_are_removed(self):
        self.writer_fixture()
        self.environment.update(ZESU_WRITER_ID="tf2", ZESU_MAX_COQC="1")
        directory = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        directory.mkdir(exist_ok=True)
        dead_owner = directory / "9000000.owner"
        dead_owner.write_text("confirmed\nwriter=tf2\naggregate=\n")
        dead_child = directory / f"{os.getpid()}.child"
        dead_child.write_text("9000001\nwriter=tf2\naggregate=\n")
        token = self.reserve_writer("tf2")
        try:
            self.assertFalse(dead_owner.exists())
            self.assertFalse(dead_child.exists())
        finally:
            self.guard("release-coqc", token)

    def test_gate_waits_for_an_admitted_coqc_launch(self):
        token = self.guard("reserve-coqc", str(os.getpid()))
        self.assertEqual(token.returncode, 0, token.stderr)
        self.assertEqual(self.guard("confirm-coqc", token.stdout.strip()).returncode, 0)
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            self.environment["ZESU_GATE_SCOPE_WAIT"] = "0"
            result = self.guard("lock-hold", str(holder.pid))
            self.assertEqual(result.returncode, 3)
            self.assertIn("job scopes or launches still alive", result.stderr)
            self.assertFalse(self.lock.exists())
        finally:
            self.guard("release-coqc", token.stdout.strip())
            holder.terminate()
            holder.wait(timeout=3)

    def test_fixture_environment_removes_routes_and_retains_explicit_fixture_routes(self):
        from unittest.mock import patch
        inherited = {"ZESU_RESOURCE_GUARD": "/real/guard", "ZESU_ROCQ_COQC_WRAPPER": "/real/compiler",
                     "ZESU_SCRATCH_COQC_BINARY": "/real/scratch", "ZESU_WRITER_ID": "writer",
                     "ZESU_GATE_LOCK": "/real/wanted", "ZESU_COQC_RESERVATION": "/real/token",
                     "ROCQ_COQC_BINARY": "/real/compiler"}
        with patch.dict(os.environ, inherited):
            cleaned = fixture_environment()
            for name in inherited:self.assertNotIn(name, cleaned)
            explicit = fixture_environment(ZESU_RESOURCE_GUARD="/fixture/guard")
            self.assertEqual(explicit["ZESU_RESOURCE_GUARD"], "/fixture/guard")

    def test_subprocesses_do_not_inherit_guard_bypass_flags(self):
        for name in ("ZESU_GUARD", "ZESU_IN_GATE", "ZESU_IN_BATCH", "ZESU_ARM",
                     "ZESU_BATCH_LIMIT"):
            with self.subTest(name=name):
                self.assertNotIn(name, self.environment)

    def test_batch_fence_under_gate_environment(self):
        environment = {**fixture_environment(), "ZESU_GUARD": "0", "ZESU_IN_GATE": "1",
                       "ZESU_IN_BATCH": "1", "ZESU_ARM": "1",
                       "ZESU_BATCH_LIMIT": "120G", "ZESU_IO": "batch"}
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

    def test_wanted_lock_holds_new_launches(self):
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            self.assertTrue(self.lock.read_text().startswith("state=wanted "))
            waited = subprocess.run(
                ["timeout", "0.5", str(GUARD), "batch", "t", "--", "true"],
                capture_output=True, text=True, env=self.environment)
            self.assertEqual(waited.returncode, 124)
            self.environment["ZESU_IN_BATCH"] = "1"
            self.assertNotIn("gate lock", self.guard("hold").stdout)
            del self.environment["ZESU_IN_BATCH"]
            self.assertEqual(self.guard("lock-hold", str(holder.pid)).returncode,
                             0)
            self.assertTrue(self.lock.read_text().startswith("state=held "))
        finally:
            holder.kill()
            holder.wait()

    def test_lock_hold_waits_for_running_scopes(self):
        fake_systemctl = self.bin / "systemctl"
        fake_systemctl.write_text("#!/bin/sh\necho arm.scope\n")
        self.environment["ZESU_GATE_SCOPE_WAIT"] = "0"
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            done = self.guard("lock-hold", str(holder.pid))
            self.assertEqual(done.returncode, 3)
            self.assertIn("job scopes or launches still alive", done.stderr)
            self.assertFalse(self.lock.exists())
        finally:
            holder.kill()
            holder.wait()

    def test_registered_launch_blocks_gate_transition(self):
        started = Path(self.directory.name) / "launch-started"
        fake_systemd = self.bin / "systemd-run"
        fake_systemd.write_text(
            "#!/bin/sh\n"
            f"touch '{started}'\n"
            "sleep 1\n"
        )
        self.environment["ZESU_GATE_SCOPE_WAIT"] = "0"
        launch = subprocess.Popen(
            [str(GUARD), "batch", "arm", "--", "true"],
            env=self.environment, stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL, text=True,
        )
        holder = subprocess.Popen(["sleep", "30"])
        try:
            for _ in range(100):
                if started.exists():
                    break
                time.sleep(0.01)
            self.assertTrue(started.exists())
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            done = self.guard("lock-hold", str(holder.pid))
            self.assertEqual(done.returncode, 3)
            self.assertIn("job scopes or launches still alive", done.stderr)
            self.assertFalse(self.lock.exists())
        finally:
            launch.wait(timeout=3)
            holder.kill()
            holder.wait()

    def test_running_arm_starts_scope_while_gate_wants(self):
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            self.environment.update(self.batch_environment())
            for startup_delay in (0, 1.1):
                with self.subTest(startup_delay=startup_delay):
                    (self.bin / "systemd-run").write_text(
                        f"#!/bin/sh\nsleep {startup_delay}\nprintf '%s\\n' \"$@\"\n")
                    process = subprocess.Popen(
                        [str(GUARD), "scope", "arm-job", "--", "true"],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, env=self.environment,
                    )
                    try:
                        deadline = time.monotonic() + 10
                        while process.poll() is None and time.monotonic() < deadline:
                            time.sleep(0.02)
                        self.assertIsNotNone(process.poll(), "scope startup did not complete")
                        stdout, stderr = process.communicate(timeout=1)
                        self.assertEqual(process.returncode, 0, stderr)
                        self.assertIn("MemoryMax=16G", stdout)
                        self.assertTrue(self.lock.read_text().startswith("state=wanted "))
                    finally:
                        if process.poll() is None:
                            process.terminate()
                        process.communicate(timeout=3)
        finally:
            holder.kill()
            holder.wait()

    def test_lock_release_uses_configured_path_and_owner(self):
        holder = subprocess.Popen(["sleep", "30"])
        try:
            self.assertEqual(self.guard("lock-want", str(holder.pid), "t").returncode,
                             0)
            self.assertEqual(self.guard("lock-release", "1").returncode, 0)
            self.assertTrue(self.lock.exists())
            self.assertEqual(self.guard("lock-release", str(holder.pid)).returncode,
                             0)
            self.assertFalse(self.lock.exists())
        finally:
            holder.kill()
            holder.wait()

    def test_peak_uses_total_minus_available(self):
        self.environment["GUARD_TEST_USED_GIB"] = "75"
        self.environment["ZESU_GUARD_POLL"] = "0.05"
        subprocess.run(["timeout", "0.2", str(GUARD), "watch"],
                       capture_output=True, env=self.environment)
        peak = self.guard("peak")
        self.assertEqual(peak.stdout.strip(), "75")

    def test_gate_refuses_to_build_after_drain_timeout(self):
        gate = (TOOLS / "det" / "gate.sh").read_text()
        self.assertIn("if (( coqc > floor || memory >= launch )); then", gate)
        self.assertIn("refusing: gate drain timed out", gate)
        self.assertIn("$guard lock-release $$", gate)

    def test_gate_jobs_caps(self):
        self.environment["GUARD_TEST_USED_GIB"] = "30"
        for name in ("ZESU_MAX_JOBS", "ZESU_GATE_MAX_JOBS", "ZESU_FAST_MAX_JOBS"):
            self.environment.pop(name, None)
        self.assertEqual(int(self.guard("jobs").stdout), 48)
        self.assertEqual(int(self.guard("gate-jobs").stdout), 24)
        self.assertEqual(int(self.guard("gate-jobs", "check-fast").stdout), 24)

    def test_available_memory_thresholds(self):
        for used, expected in ((215, None), (216, "requires 36 GiB"),
                               (231, "requires 36 GiB"),
                               (232, "below the 20 GiB hold"),
                               (241, "below the 20 GiB hold")):
            with self.subTest(used=used):
                self.environment["GUARD_TEST_USED_GIB"] = str(used)
                result = self.guard("hold")
                self.assertEqual(result.returncode, 0)
                if expected:
                    self.assertIn(expected, result.stdout)
                else:
                    self.assertNotIn("memory", result.stdout)

    def test_scope_and_batch_memory_fences(self):
        for arguments, fence in (("scope", "MemoryMax=16G"),
                                 ("batch", "MemoryMax=150G")):
            with self.subTest(arguments=arguments):
                result = self.guard(arguments, "test", "--", "true")
                self.assertEqual(result.returncode, 0)
                self.assertIn(fence, result.stdout)
                self.assertIn("MemorySwapMax=0", result.stdout)

    def test_aggregate_contains_parent_and_compiler_but_excludes_writer(self):
        base = Path(self.directory.name)
        events = base / "aggregate-scopes.jsonl"
        self.prepare_blocked_fixture(0)
        self.environment["AGGREGATE_TEST_EVENTS"] = str(events)
        (self.bin / "systemd-run").write_text(
            '#!/usr/bin/env python3\nimport json,os,sys\n'
            'with open(os.environ["AGGREGATE_TEST_EVENTS"],"a") as f:f.write(json.dumps(sys.argv[1:])+"\\n")\n'
            'args=sys.argv[sys.argv.index("--")+1:];os.execvp(args[0],args)\n')
        command = base / "parent.py"
        command.write_text(
            "import os,subprocess,sys\n"
            "guard=sys.argv[1]\n"
            "subprocess.run([guard,'batch','nested','--',guard,'scope','ordinary','--','true'],check=True)\n"
)
        for gate, limit in ((False, "150G"), (True, "120G")):
            with self.subTest(gate=gate):
                events.unlink(missing_ok=True)
                if gate:self.lock.write_text(f"state=held holder=fixture pid={os.getpid()} start=x\n")
                env = {**self.environment, **({"ZESU_IN_GATE": "1"} if gate else {})}
                result = subprocess.run([str(GUARD), "batch", "parent", "--",
                                         sys.executable, str(command), str(GUARD)],
                                        env=env, capture_output=True, text=True, timeout=5)
                self.assertEqual(result.returncode, 0, result.stderr)
                writer = subprocess.run([str(GUARD), "scope", "writer", "--", "true"],
                                        env={**self.environment, "ZESU_WRITER_ID": "tf2"},
                                        capture_output=True, text=True, timeout=5)
                self.assertEqual(writer.returncode, 0, writer.stderr)
                scopes = [json.loads(line) for line in events.read_text().splitlines()]
                self.assertEqual(len(scopes), 3)
                slices = [next(arg for arg in row if arg.startswith("--slice=")) for row in scopes]
                self.assertEqual(slices[0], slices[1])
                self.assertTrue(slices[0].startswith("--slice=zesuaggregate"))
                self.assertEqual(slices[2], "--slice=app.slice")
                self.assertIn(f"MemoryMax={limit}", scopes[0])
                for row in scopes[1:]:self.assertIn("MemoryMax=16G", row)
                for row in scopes:self.assertIn("MemorySwapMax=0", row)
                properties = json.loads(Path(self.environment["GUARD_TEST_SLICE_STATE"]).read_text())
                self.assertEqual(properties[slices[0].split("=",1)[1]]["MemoryMax"], limit)
                self.assertEqual(list((Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations").iterdir()), [])

    def test_missing_or_changed_aggregate_fence_rejects_compiler(self):
        self.prepare_blocked_fixture(0)
        for context in ({"ZESU_IN_BATCH": "1"},
                        {**self.batch_environment("150G"), "ZESU_AGGREGATE_LIMIT": "120G"},
                        {**self.batch_environment(), "ZESU_AGGREGATE_SLICE": "app.slice"}):
            with self.subTest(context=context):
                result = subprocess.run([str(GUARD), "scope", "bad", "--", "echo", "WRONG"],
                                        env={**self.environment, **context}, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertNotIn("WRONG", result.stdout)
                self.assertEqual(list((Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations").iterdir()), [])

    def test_writer_controller_rejects_batch_context(self):
        self.prepare_blocked_fixture(0)
        result = subprocess.run([str(GUARD), "scope", "writer", "--", "echo", "WRONG"],
                                env={**self.environment, **self.batch_environment(), "ZESU_WRITER_ID": "tf2"},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertNotIn("WRONG", result.stdout)

    def test_fixture_controller_cgroup_is_private(self):
        result = subprocess.run(["cat", f"/proc/{os.getpid()}/cgroup"],
                                env=self.environment, check=True, capture_output=True, text=True)
        self.assertEqual(result.stdout, self.cgroup.read_text())
        ordinary = Path(self.directory.name) / "ordinary-file"
        ordinary.write_text("ordinary content\n")
        result = subprocess.run(["cat", str(ordinary)], env=self.environment,
                                check=True, capture_output=True, text=True)
        self.assertEqual(result.stdout, ordinary.read_text())
        result = subprocess.run(["cat", "/proc/123invalid/cgroup"], env=self.environment,
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        result = subprocess.run(["cat", "/proc/self/cgroup"], env=self.environment,
                                check=True, capture_output=True, text=True)
        self.assertEqual(result.stdout, Path("/proc/self/cgroup").read_text())

    def test_writer_controller_rejects_fixture_aggregate_cgroup(self):
        self.prepare_blocked_fixture(0)
        self.cgroup.write_text(
            "0::/user.slice/user-1000.slice/user@1000.service/"
            f"zesuaggregate1000p{os.getpid()}r1.slice/fixture.scope\n")
        result = subprocess.run([str(GUARD), "scope", "writer", "--", "echo", "WRONG"],
                                env={**self.environment, "ZESU_WRITER_ID": "tf2"},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("writer controller must start outside the batch aggregate", result.stderr)
        self.assertNotIn("WRONG", result.stdout)
        reservations = Path(self.environment["ZESU_GUARD_STATE"]) / "coqc-reservations"
        self.assertEqual(list(reservations.iterdir()), [])
        self.assertEqual((Path(self.environment["ZESU_GUARD_STATE"]) / "scopes").read_text(), "")

    def test_batch_cleanup_removes_only_its_compiler_reservations(self):
        self.prepare_blocked_fixture(0)
        context = self.batch_environment()
        ordinary = subprocess.run([str(GUARD), "reserve-coqc", str(os.getpid())],
                                  env={**self.environment, **context}, check=True, capture_output=True, text=True).stdout.strip()
        writer = subprocess.run([str(GUARD), "reserve-coqc", str(os.getpid())],
                                env={**self.environment, "ZESU_WRITER_ID": "tf2"},
                                check=True, capture_output=True, text=True).stdout.strip()
        subprocess.run([str(GUARD), "confirm-coqc", ordinary],
                       env={**self.environment, **context}, check=True, capture_output=True, text=True)
        subprocess.run([str(GUARD), "confirm-coqc", writer],
                       env={**self.environment, "ZESU_WRITER_ID": "tf2"},
                       check=True, capture_output=True, text=True)
        # Retain the owner to test explicit cleanup instead of stale-owner cleanup.
        (self.bin / "systemd-run").write_text(
            '#!/bin/sh\nwhile [ "$1" != -- ]; do shift; done; shift; exec "$@"\n')
        command = (f'token=$("{GUARD}" reserve-coqc {os.getpid()}); '
                   f'"{GUARD}" confirm-coqc "$token" && printf "%s\\n" "$token" > "$AGGREGATE_TOKEN_OUTPUT"')
        token_file = Path(self.directory.name) / "aggregate-token"
        result = subprocess.run([str(GUARD), "batch", "cleanup", "--", "bash", "-c", command],
                                env={**self.environment, "AGGREGATE_TOKEN_OUTPUT": str(token_file)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(token_file.exists())
        self.assertFalse(Path(token_file.read_text().strip()).exists())
        self.assertTrue(Path(ordinary).exists())
        self.assertTrue(Path(writer).exists())
        for token in (ordinary, writer):self.guard("release-coqc", token)

    def test_failed_slice_cap_prevents_parent_launch(self):
        self.prepare_blocked_fixture(0)
        self.environment["GUARD_TEST_SLICE_FAIL"] = "1"
        result = self.guard("batch", "bad", "--", "echo", "WRONG")
        self.assertEqual(result.returncode, 2)
        self.assertNotIn("WRONG", result.stdout)
        self.assertEqual(list((Path(self.environment["ZESU_GUARD_STATE"]) / "launches").iterdir()), [])

    def test_direct_batch_waits_at_launch_limit(self):
        self.environment["GUARD_TEST_USED_GIB"] = "226"
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

    def test_watch_kills_youngest_scope_at_10_gib_available(self):
        state = Path(self.environment["ZESU_GUARD_STATE"])
        state.mkdir(exist_ok=True)
        (state / "scopes").write_text("old.scope\nyoung.scope\n")
        live = Path(self.directory.name) / "live-scopes"
        live.write_text("old.scope loaded active running\nyoung.scope loaded active running\n")
        self.environment["GUARD_TEST_LIVE_SCOPES"] = str(live)
        log = Path(self.environment["GUARD_TEST_SYSTEMCTL_LOG"])
        self.environment["ZESU_GUARD_POLL"] = "0.05"
        self.environment["GUARD_TEST_USED_GIB"] = "240"
        subprocess.run(["timeout", "0.2", str(GUARD), "watch"],
                       capture_output=True, env=self.environment)
        self.assertFalse(log.exists())
        self.environment["GUARD_TEST_USED_GIB"] = "241"
        # Delay the mock action beyond the former fixed timeout.
        systemctl = self.bin / "systemctl"
        systemctl.write_text(systemctl.read_text().replace(
            "elif 'kill' in args or 'stop' in args:\n",
            "elif 'kill' in args or 'stop' in args:\n import time;time.sleep(0.25)\n"))
        process = subprocess.Popen([str(GUARD), "watch"],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   text=True, env=self.environment)
        actions = ""
        try:
            deadline = time.monotonic() + 3
            while time.monotonic() < deadline and process.poll() is None:
                actions = log.read_text() if log.exists() else ""
                if "young.scope" in actions:
                    break
                time.sleep(0.02)
        finally:
            if process.poll() is None:
                process.terminate()
            stdout, stderr = process.communicate(timeout=3)
        self.assertIn("young.scope", actions, f"stdout: {stdout}\nstderr: {stderr}")
        self.assertNotIn("old.scope", actions)

    def test_startup_prunes_scope_registry_to_live_units(self):
        state = Path(self.environment["ZESU_GUARD_STATE"])
        registry = state / "scopes"
        registry.write_text("abandoned.scope\n" * 27761 + "young.scope\nyoung.scope\n")
        live = Path(self.directory.name) / "live-scopes"
        live.write_text("young.scope loaded active running\n")
        self.environment["GUARD_TEST_LIVE_SCOPES"] = str(live)
        self.assertEqual(self.guard("coqc-count").returncode, 0)
        self.assertEqual(registry.read_text(), "young.scope\n")

    def test_scope_exec_registers_the_active_scope(self):
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        environment = {**self.environment, "ZESU_SCOPE_UNIT": "young.scope"}
        try:
            result = subprocess.run([str(GUARD), "scope-exec", token, "--", "true"],
                                    env=environment, capture_output=True, text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
            registry = Path(self.environment["ZESU_GUARD_STATE"]) / "scopes"
            self.assertEqual(registry.read_text(), "young.scope\n")
        finally:
            self.guard("release-coqc", token)

    def test_scope_exec_accepts_explicit_cpu_limit(self):
        token = self.guard("reserve-coqc", str(os.getpid())).stdout.strip()
        environment = {**self.environment, "ZESU_SCOPE_CPU": "600"}
        try:
            result = subprocess.run([str(GUARD), "scope-exec", token, "--", "bash", "-c", "ulimit -t"],
                                    env=environment, capture_output=True, text=True, timeout=3)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), "600")
        finally:
            self.guard("release-coqc", token)

    def test_scope_rejects_invalid_cpu_limit(self):
        result = self.guard("scope", "probe", "--cpu", "invalid", "--", "true")
        self.assertEqual(result.returncode, 2)
        self.assertIn("invalid CPU limit", result.stderr)

    def probe_environment(self):
        return {'ZESU_DIAGNOSTIC_PROBE': '1', 'ZESU_PROBE_ISSUE': '10',
                'ZESU_MODULE_LIMIT_GIB': '64', 'ZESU_PROOF_CPU_LIMIT': 'unlimited'}

    def test_probe_scope_uses_64_gib_fence_and_unlimited_cpu(self):
        self.environment.update(self.probe_environment())
        result = self.guard('scope', 'probe', '--', 'true')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('MemoryMax=64G', result.stdout)
        self.assertIn('MemorySwapMax=0', result.stdout)

    def test_probe_scope_exec_has_unlimited_soft_and_hard_cpu(self):
        self.environment.update(self.probe_environment())
        token = self.guard('reserve-coqc', str(os.getpid())).stdout.strip()
        try:
            result = self.guard('scope-exec', token, '--', 'bash', '-c',
                                'ulimit -St; ulimit -Ht')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.splitlines(), ['unlimited', 'unlimited'])
        finally:
            self.guard('release-coqc', token)

    def test_probe_scope_rejects_finite_cpu_and_gate_inheritance(self):
        for change in ({'ZESU_IN_GATE': '1'}, {'ZESU_MODULE_LIMIT_GIB': '6'},
                       {'ZESU_PROOF_CPU_LIMIT': '1200'}, {'ZESU_PROBE_ISSUE': ''},
                       {'ZESU_DIAGNOSTIC_PROBE': 'invalid'}):
            with self.subTest(change=change):
                self.environment.update(self.probe_environment())
                self.environment.pop('ZESU_IN_GATE', None)
                self.environment.update(change)
                result = self.guard('scope', 'probe', '--', 'true')
                self.assertEqual(result.returncode, 2, result.stderr)
        self.environment.pop('ZESU_IN_GATE', None)
        self.environment.update(self.probe_environment())
        result = self.guard('scope', 'probe', '--cpu', '14400', '--', 'true')
        self.assertEqual(result.returncode, 2, result.stderr)


    def test_probe_scope_exec_rejects_finite_cpu_before_child(self):
        self.environment.update(self.probe_environment())
        self.environment['ZESU_SCOPE_CPU'] = '1200'
        result = self.guard('scope-exec', 'unused', '--', 'true')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('probe CPU must be unlimited', result.stderr)



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
