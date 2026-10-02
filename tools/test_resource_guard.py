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
                                  text=True, capture_output=True, env=environment)

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

    def test_missing_token_is_reserved_again(self):
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
        self.assertIn("RETRY reservation", result.stdout)

    def test_expiry_during_admission_retries(self):
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
