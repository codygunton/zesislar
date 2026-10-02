"""Check writer admission limits and reservation classes in isolation."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


GUARD = Path(__file__).with_name("resource_guard.sh")
LIBRARY = GUARD.read_text().split("\nprune_scope_registry\n\ncase ", 1)[0]


class ResourceGuard(unittest.TestCase):
    def run_guard(self, script, **variables):
        with tempfile.TemporaryDirectory() as directory:
            environment = {key: value for key, value in os.environ.items()
                           if not key.startswith("ZESU_")}
            environment.update(ZESU_GUARD_STATE=directory, **variables)
            return subprocess.run(["bash"], input=LIBRARY + "\n" + script,
                                  text=True, capture_output=True, env=environment, timeout=20)

    def test_configured_limit_changes_writer_admission(self):
        script = '''
compiler_pids() { echo "123 124"; }
live_reservations() { printf '%s\\n' "$STATE_DIR/one" "$STATE_DIR/two"; }
reservation_compiler() { [ "${1##*/}" = one ] && echo 123 || echo 124; }
printf 'confirmed\\nwriter=test\\n' > "$STATE_DIR/one"
cp "$STATE_DIR/one" "$STATE_DIR/two"
compiler_admission_reason
'''
        default = self.run_guard(script, ZESU_WRITER_ID="test")
        self.assertEqual(default.returncode, 0, default.stderr)
        self.assertIn("at its 2 compiler limit", default.stdout)
        configured = self.run_guard(script, ZESU_WRITER_ID="test",
                                    ZESU_WRITER_MAX_COQC="4")
        self.assertEqual(configured.returncode, 0, configured.stderr)
        self.assertEqual(configured.stdout, "")

    def test_invalid_limit_fails(self):
        for value in ("0", "-1", "text"):
            result = self.run_guard("reservation_class", ZESU_WRITER_MAX_COQC=value)
            self.assertEqual(result.returncode, 2)
            self.assertIn("invalid writer compiler limit", result.stderr)

    def test_reservation_classes(self):
        cases = [("standalone", {}), ("writer:test", {"ZESU_WRITER_ID": "test"}),
                 ("batch", {"ZESU_IN_BATCH": "1"}),
                 ("gate", {"ZESU_IN_GATE": "1", "ZESU_IN_BATCH": "1"})]
        for expected, variables in cases:
            result = self.run_guard("reservation_class", **variables)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), expected)

    def test_missing_request_is_admitted(self):
        result = self.run_guard("""
hold_reason() { :; }
compiler_admission_reason() { :; }
marker="$COQC_RESERVATIONS/$$.missing"
confirm_coqc "$marker"
head -n 1 "$marker"
cat "$LOG"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("confirmed", result.stdout)
        self.assertNotIn("RETRY reservation", result.stdout)

    def test_legacy_pending_request_is_replaced(self):
        result = self.run_guard("""
hold_reason() { :; }
marker="$COQC_RESERVATIONS/$$.expired"
printf 'pending\\nwriter=\\naggregate=\\n' > "$marker"
compiler_admission_reason() {
  if [ ! -f "$STATE_DIR/expired-once" ]; then
    touch "$STATE_DIR/expired-once"
    rm -f "$marker"
  fi
}
confirm_coqc "$marker"
head -n 1 "$marker"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("confirmed", result.stdout)

    def test_two_batches_exceed_cap_without_deadlock(self):
        result = self.run_guard("""
hold_reason() { :; }
compiler_pids() { :; }
POLL_SECONDS=0.01
worker() {
  local owner=$BASHPID marker
  marker=$(reserve_coqc "$owner") || return
  [ ! -e "$marker" ] || return 10
  confirm_coqc "$marker" || return
  # A repeated confirmation must not wait on the slot it already owns.
  confirm_coqc "$marker" || return
  printf 'start %s\n' "$owner" >> "$STATE_DIR/events"
  sleep 0.05
  printf 'end %s\n' "$owner" >> "$STATE_DIR/events"
  release_coqc "$marker"
}
batch() {
  local pids="" pid status=0
  for _ in 1 2 3; do worker & pids="$pids $!"; done
  for pid in $pids; do wait "$pid" || status=1; done
  return "$status"
}
batch & one=$!
batch & two=$!
wait "$one" || exit 11
wait "$two" || exit 12
cat "$STATE_DIR/events"
[ -z "$(live_reservations)" ]
""", ZESU_MAX_COQC="2", ZESU_IN_BATCH="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        active = set()
        starts = 0
        peak = 0
        for line in result.stdout.splitlines():
            event, pid = line.split()
            if event == "start":
                active.add(pid)
                starts += 1
                peak = max(peak, len(active))
            else:
                active.remove(pid)
        self.assertEqual(starts, 6)
        self.assertFalse(active)
        self.assertLessEqual(peak, 2)

    def test_confirmed_launch_does_not_expire_before_compiler_start(self):
        result = self.run_guard("""
hold_reason() { :; }
compiler_pids() { :; }
marker=$(reserve_coqc $$)
confirm_coqc "$marker"
touch -d '2 minutes ago' "$marker"
live_reservations
[ -f "$marker" ] || exit 4
mark_coqc "$marker" $$
confirm_coqc "$marker"
[ -f "$marker" ]
release_coqc "$marker"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("coqc-reservations", result.stdout)

    def test_confirmation_errors_are_visible(self):
        result = self.run_guard('confirm_coqc "$COQC_RESERVATIONS/not-a-pid.token"')
        self.assertEqual(result.returncode, 2)
        self.assertIn("invalid reservation path or dead owner", result.stderr)
