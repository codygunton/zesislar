"""Check shared probe quota accounting without starting workloads."""
from pathlib import Path
import unittest
import tools.test_resource_guard as guard_fixtures

FIXTURE = r'''
PROC_ROOT="$STATE_DIR/proc"; mkdir -p "$PROC_ROOT"
process_start() { echo 100; }
fixture_probe() {
  local owner=$1 aggregate=$2 memory=$3
  mkdir -p "$PROC_ROOT/$owner"
  printf '0::/user.slice/user-1000.slice/user@1000.service/zesuworkloads.slice/%s/client.scope\n' "$aggregate" > "$PROC_ROOT/$owner/cgroup"
  printf 'confirmed\naggregate=%s\nprobe=issue10\nmemory_gib=%s\ncpu=unlimited\nowner_start=100\n' "$aggregate" "$memory" > "$COQC_RESERVATIONS/$owner.probe"
}
live_reservations() { printf '%s\n' "$COQC_RESERVATIONS"/*; }
'''

class ProbeAggregates(unittest.TestCase):
    run_guard = guard_fixtures.ResourceGuard.run_guard

    def test_client_and_MCP_markers_count_three_aggregates(self):
        result = self.run_guard(FIXTURE + r'''
for n in 1 2 3; do
  aggregate="zesuworkloads-aggregate1000p${n}r1.slice"
  fixture_probe "$((n*10))" "$aggregate" 24
  fixture_probe "$((n*10+1))" "$aggregate" 64
done
[ "$(probe_count)" = 3 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_nested_compiler_can_join_an_aggregate_at_quota(self):
        result = self.run_guard(FIXTURE + r'''
for n in 1 2 3 4 5 6; do fixture_probe "$n" "zesuworkloads-aggregate1000p${n}r1.slice" 24; done
owner=100; ZESU_AGGREGATE_SLICE=zesuworkloads-aggregate1000p1r1.slice
mkdir -p "$PROC_ROOT/$owner"
printf '0::/user.slice/zesuworkloads.slice/%s/client.scope/mcp.scope\n' "$ZESU_AGGREGATE_SLICE" > "$PROC_ROOT/$owner/cgroup"
[ -z "$(probe_admission_reason "$owner")" ] || exit 91
[ "$(probe_count)" = 6 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_seventh_new_aggregate_stays_held(self):
        result = self.run_guard(FIXTURE + r'''
for n in 1 2 3 4 5 6; do fixture_probe "$n" "zesuworkloads-aggregate1000p${n}r1.slice" 64; done
owner=100; ZESU_AGGREGATE_SLICE=zesuworkloads-aggregate1000p7r1.slice
mkdir -p "$PROC_ROOT/$owner"
printf '0::/user.slice/zesuworkloads.slice/%s/client.scope\n' "$ZESU_AGGREGATE_SLICE" > "$PROC_ROOT/$owner/cgroup"
[ "$(probe_admission_reason "$owner")" = 'issue10 probes at their six-aggregate limit' ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_declared_aggregate_requires_actual_owner_membership(self):
        result = self.run_guard(FIXTURE + r'''
fixture_probe 100 zesuworkloads-aggregate1000p1r1.slice 24
ZESU_AGGREGATE_SLICE=zesuworkloads-aggregate1000p2r1.slice
probe_admission_reason 100
''')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn('outside its declared aggregate', result.stderr)

    def test_unverified_legacy_aggregate_does_not_merge_owners(self):
        result = self.run_guard(FIXTURE + r'''
for owner in 100 101; do
  fixture_probe "$owner" zesuworkloads-aggregate1000p1r1.slice 24
  printf '0::/app.slice/old.scope\n' > "$PROC_ROOT/$owner/cgroup"
done
[ "$(probe_count)" = 2 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_mixed_fences_and_CPU_only_share_one_quota(self):
        result = self.run_guard(FIXTURE + r'''
fixture_probe 100 zesuworkloads-aggregate1000p1r1.slice 24
fixture_probe 101 zesuworkloads-aggregate1000p2r1.slice 64
fixture_probe 102 zesuworkloads-aggregate1000p3r1.slice 6
sed -i 's/probe=issue10$/probe=issue10-cpu-only/' "$COQC_RESERVATIONS/102.probe"
[ "$(probe_count)" = 3 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_invalid_memory_and_pending_records_do_not_count(self):
        result = self.run_guard(FIXTURE + r'''
fixture_probe 100 zesuworkloads-aggregate1000p1r1.slice 128
fixture_probe 101 zesuworkloads-aggregate1000p2r1.slice 24
sed -i '1s/confirmed/pending/' "$COQC_RESERVATIONS/101.probe"
fixture_probe 102 zesuworkloads-aggregate1000p3r1.slice 24
printf 'memory_gib=64\n' >> "$COQC_RESERVATIONS/102.probe"
[ "$(probe_count)" = 0 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_owner_identity_validation_stays_strict(self):
        result = self.run_guard(FIXTURE + r'''
fixture_probe 100 zesuworkloads-aggregate1000p1r1.slice 24
sed -i 's/owner_start=100/owner_start=99/' "$COQC_RESERVATIONS/100.probe"
[ "$(probe_count)" = 0 ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)

if __name__ == '__main__':
    unittest.main()
