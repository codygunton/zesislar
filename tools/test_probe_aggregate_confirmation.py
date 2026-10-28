"""Check quota decisions through the actual confirmation handler."""
import unittest
import tools.test_resource_guard as guard_fixtures
from tools.test_probe_aggregates import FIXTURE

class AggregateConfirmation(unittest.TestCase):
    run_guard = guard_fixtures.ResourceGuard.run_guard

    def test_nested_confirmation_publishes_without_an_extra_slot(self):
        result = self.run_guard(FIXTURE + r'''
for n in 1 2 3 4 5 6; do fixture_probe "$n" "zesuworkloads-aggregate1000p${n}r1.slice" 24; done
hold_reason() { :; }; compiler_pids() { :; }
ZESU_AGGREGATE_SLICE=zesuworkloads-aggregate1000p1r1.slice
mkdir -p "$PROC_ROOT/$$"
printf '0::/user.slice/zesuworkloads.slice/%s/mcp.scope\n' "$ZESU_AGGREGATE_SLICE" > "$PROC_ROOT/$$/cgroup"
request=$(reserve_coqc $$)
confirm_coqc "$request" || exit 91
[ "$(probe_count)" = 6 ] || exit 92
probe_record "$request" || exit 93
release_coqc "$request"
''', ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
            ZESU_MODULE_LIMIT_GIB="64", ZESU_PROOF_CPU_LIMIT="unlimited")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_seventh_confirmation_waits_without_holding_a_marker(self):
        result = self.run_guard(FIXTURE + r'''
for n in 1 2 3 4 5 6; do fixture_probe "$n" "zesuworkloads-aggregate1000p${n}r1.slice" 24; done
hold_reason() { :; }; compiler_pids() { :; }
ZESU_AGGREGATE_SLICE=zesuworkloads-aggregate1000p7r1.slice
mkdir -p "$PROC_ROOT/$$"
printf '0::/user.slice/zesuworkloads.slice/%s/client.scope\n' "$ZESU_AGGREGATE_SLICE" > "$PROC_ROOT/$$/cgroup"
request=$(reserve_coqc $$)
sleep() { [ ! -e "$request" ] || exit 92; exit 91; }
confirm_coqc "$request"
''', ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
            ZESU_MODULE_LIMIT_GIB="64", ZESU_PROOF_CPU_LIMIT="unlimited")
        self.assertEqual(result.returncode, 91, result.stderr)

if __name__ == '__main__':
    unittest.main()
