"""Check writer admission limits and reservation classes in isolation."""

import json
import shutil
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

if __package__:
    from . import run_registry
else:
    import run_registry


GUARD = Path(__file__).with_name("resource_guard.sh")
SOURCE = GUARD.read_text()
LIBRARY = SOURCE.split("\nprune_scope_registry\n", 1)[0]
DISPATCH_MARKER = '\ncase "${1:-report}" in\n'
DISPATCH = DISPATCH_MARKER.lstrip("\n") + SOURCE.rsplit(DISPATCH_MARKER, 1)[1]
# Our account's cgroup files, meminfo, and loadavg, captured on 2026-11-03.
# The load and pressure lines are from the hour when another account's
# fuzzers raised load5 to 432.
ACCOUNT_FIXTURE = Path(__file__).with_name("fixtures") / "account-cgroup"
ACCOUNT_SETUP = r'''
mkdir -p "$ACCOUNT_CGROUP"
for file in memory.max memory.current memory.stat cpu.pressure io.pressure; do
  cp "$TEST_ACCOUNT/$file" "$ACCOUNT_CGROUP/$file"
done
memory() {
  awk '/^MemTotal:/ {t = $2 * 1024} /^MemAvailable:/ {a = $2 * 1024}
       END {printf "%.0f %.0f %.0f\n", t, t - a, a}' "$TEST_ACCOUNT/meminfo"
}
load_five() { awk '{printf "%d", $2}' "$TEST_ACCOUNT/loadavg"; }
blocked_count() { echo 99; }
coqc_count() { echo 0; }
'''

# These shell controls exercise slot publication, not the unified kernel ledger.
# Keep the real arithmetic for the profile-capacity control.
MEMORY_HELPER = r'''
import argparse
import os
from pathlib import Path
import module_memory

parser = argparse.ArgumentParser()
parser.add_argument("operation", choices=("admission", "ledger-confirm", "ledger-mark", "ledger-release", "ledger-recover-stale", "test-ledger-policy", "aggregate-limit"))
parser.add_argument("--guard-pid", type=int)
parser.add_argument("--inner-fence-bytes", type=int)
parser.add_argument("--booking-bytes", type=int)
parser.add_argument("--explicit-limit-bytes", type=int)
parser.add_argument("--gate-limit-bytes", type=int)
parser.add_argument("--all", action="store_true")
parser.add_argument("--marker", type=Path)
parser.add_argument("--replacement", type=Path)
parser.add_argument("--request-bytes", type=int)
parser.add_argument("--available-bytes", type=int)
parser.add_argument("--fallback-bytes", type=int)
parser.add_argument("--headroom-bytes", type=int, default=20 * 1024**3)
parser.add_argument("--maximum-compilers", type=int, default=48)
parser.add_argument("--proc", type=Path)
parser.add_argument("markers", nargs="*")
args = parser.parse_args()
state = Path(os.environ["ZESU_GUARD_STATE"])
if args.marker is not None:
    assert args.marker.parent == state / "coqc-reservations"

def admitted(markers):
    claims = []
    for marker in markers:
        lines = Path(marker).read_text().splitlines()
        if not lines or lines[0] == "pending":
            continue
        fields = dict(line.split("=", 1) for line in lines[1:] if "=" in line)
        claims.append(int(fields["memory_claim_bytes"]))
    return module_memory.admission(
        args.request_bytes, claims, args.available_bytes,
        headroom_bytes=args.headroom_bytes, maximum_compilers=args.maximum_compilers,
        slice_max_bytes=175 * 1024**3)["admitted"]

if args.operation == "ledger-recover-stale":
    assert args.all
    print("[]")  # Shell slot fixtures do not create unified ledger owners.
elif args.operation == "test-ledger-policy":
    module_memory.check_test_ledger()
elif args.operation == "aggregate-limit":
    print(module_memory._module.new_aggregate_limit(
        args.inner_fence_bytes, args.booking_bytes,
        explicit_limit_bytes=args.explicit_limit_bytes, gate_limit_bytes=args.gate_limit_bytes))
elif args.operation == "admission":
    if not admitted(args.markers):
        print("fixture memory admission refused")
elif args.operation == "ledger-confirm":
    assert args.replacement.parent == state
    if os.environ.get("ZESU_MODULE_MEMORY_PROFILE") and not admitted(args.marker.parent.glob("*")):
        raise SystemExit(3)
    os.replace(args.replacement, args.marker)
elif args.operation == "ledger-release":
    args.marker.unlink()
# ledger-mark only acknowledges the shell's private marker update.
'''


class ResourceGuard(unittest.TestCase):
    def test_profile_mode_opens_dune_width_without_changing_default_width(self):
        script = "memory() { echo $((200*GIB)) 0 $((100*GIB)); }; gate_jobs check-fast"
        result = self.run_guard(script, ZESU_MODULE_MEMORY_PROFILE="fixture")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "48")
        result = self.run_guard(script)
        self.assertEqual(result.stdout.strip(), "23")

    def test_profile_mode_uses_the_module_claim_for_headroom(self):
        result = self.run_guard("memory() { echo $((100*GIB)) 0 $((25*GIB)); }; memory_hold_reason",
                                ZESU_MODULE_MEMORY_PROFILE="fixture", ZESU_MODULE_CLAIM_BYTES=str(1024 ** 3))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "")

    def test_profile_memory_admission_is_atomic_across_requests(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_guard(r'''
hold_reason() { :; }
compiler_pids() { :; }
# Two 12 GiB claims exceed 70 percent of 30 GiB.
memory() { echo $((100*GIB)) 0 $((30*GIB)); }
POLL_SECONDS=0.01
worker() {
  local owner=$BASHPID marker
  marker=$(reserve_coqc "$owner") || return
  confirm_coqc "$marker" || return
  printf 'start %s\n' "$owner" >> "$STATE_DIR/events"
  sleep 0.1
  printf 'end %s\n' "$owner" >> "$STATE_DIR/events"
  release_coqc "$marker"
}
worker & first=$!
worker & second=$!
wait "$first" || exit 11
wait "$second" || exit 12
cat "$STATE_DIR/events"
''', ZESU_IN_BATCH="1", ZESU_MODULE_MEMORY_PROFILE="fixture",
                ZESU_MODULE_CLAIM_BYTES=str(12 * 1024 ** 3), ZESU_PROC_ROOT=directory)
        self.assertEqual(result.returncode, 0, result.stderr)
        active = set()
        starts = peak = 0
        for line in result.stdout.splitlines():
            event, pid = line.split()
            if event == "start":
                active.add(pid)
                starts += 1
                peak = max(peak, len(active))
            else:
                active.remove(pid)
        self.assertEqual(starts, 2)
        self.assertEqual(peak, 1)
        self.assertFalse(active)

    def confirmed_marker(self, **environment):
        with tempfile.TemporaryDirectory() as directory:
            return self.run_guard(r'''
hold_reason() { :; }
compiler_pids() { :; }
memory() { echo $((100*GIB)) 0 $((60*GIB)); }
marker=$(reserve_coqc $$) || exit 11
confirm_coqc "$marker" || exit 12
cat "$marker"
release_coqc "$marker"
''', ZESU_IN_BATCH="1", ZESU_MODULE_MEMORY_PROFILE="fixture",
                ZESU_MODULE_CLAIM_BYTES=str(5 * 1024 ** 3), ZESU_PROC_ROOT=directory, **environment)

    def test_a_measured_module_records_its_peak_in_its_reservation(self):
        result = self.confirmed_marker(ZESU_MODULE_MEASURED_PEAK_BYTES=str(4 * 1024 ** 3))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(f"memory_claim_bytes={5 * 1024 ** 3}\n", result.stdout)
        self.assertIn(f"memory_measured_peak_bytes={4 * 1024 ** 3}\n", result.stdout)
        unmeasured = self.confirmed_marker()
        self.assertEqual(unmeasured.returncode, 0, unmeasured.stderr)
        self.assertNotIn("memory_measured_peak_bytes", unmeasured.stdout)
        self.assertNotEqual(self.confirmed_marker(ZESU_MODULE_MEASURED_PEAK_BYTES="many").returncode, 0)

    def test_a_fence_kill_is_named_recorded_and_lowers_a_later_probe_claim(self):
        result = self.run_guard(r'''
MEMORY_TOOL="$(dirname "$0")/module_memory.py"
cd "$STATE_DIR" || exit 9
printf 'Lemma probe : True. Proof. exact I. Qed.\n' > Probe.v
scope_result() { echo exit-code; }
report_fence_kill zesudet-other.scope coqc Probe.v
[ ! -e "$FENCE_KILLS" ] || exit 10
scope_result() { echo oom-kill; }
report_fence_kill zesudet-af28.scope python3 measure.py measure.json coqc Probe.v
MEMORY_CLAIM_BYTES=$((48 * GIB))
probe_fence_claim python3 measure.py measure.json coqc Probe.v || exit 11
echo "claim=$MEMORY_CLAIM_BYTES"
MEMORY_CLAIM_BYTES=$((48 * GIB)) MEMORY_TOOL=/nonexistent/module_memory.py
probe_fence_claim python3 measure.py measure.json coqc Probe.v || exit 12
echo "failed lookup claim=$MEMORY_CLAIM_BYTES"
MEMORY_TOOL="$(dirname "$0")/module_memory.py"
cat "$FENCE_KILLS"
''', ZESU_MODULE_LIMIT_GIB="16", ZESU_GATE_MODULE_LIMIT_GIB="16")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("memory fence kill: zesudet-af28.scope reached its 16 GiB fence", result.stderr)
        self.assertIn(f"claim={20 * 1024 ** 3}\n", result.stdout)
        # A failed lookup keeps the full request.
        self.assertIn(f"failed lookup claim={48 * 1024 ** 3}\n", result.stdout)
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
        self.assertEqual([(row["unit"], row["fence_bytes"]) for row in rows],
                         [("zesudet-af28.scope", 16 * 1024 ** 3)])
        self.assertEqual(len(rows[0]["source_sha256"]), 64)

    def test_disk_trim_threshold_uses_decimal_bytes(self):
        for free, trimmed in ((60000000000, False), (59999999999, True)):
            with self.subTest(free=free):
                result = self.run_guard(r"""
home_free_bytes() { echo "$TEST_FREE"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
cat > "$DUNE_CACHE_TRIM_BIN" <<'SH_TRIM'
#!/usr/bin/env bash
[ "$DUNE_CACHE_ROOT" = /home/cody/.cache/dune ] || exit 91
[ "$*" = 'cache trim --trimmed-size=20GiB' ] || exit 92
echo fixture-trim-output
SH_TRIM
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission || exit $?
cat "$LOG"
""", TEST_FREE=str(free))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual("CACHE_TRIM start" in result.stdout, trimmed)
                self.assertEqual("CACHE_TRIM end" in result.stdout, trimmed)

    def test_disk_probe_refusal_rechecks_after_trim(self):
        for flag, memory in (("1", "64"), ("cpu-only", "6")):
            for after, allowed in ((20000000000, True), (19999999999, False)):
                with self.subTest(flag=flag, after=after):
                    result = self.run_guard(r"""
echo 10000000000 > "$STATE_DIR/free"
home_free_bytes() { cat "$STATE_DIR/free"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
cat > "$DUNE_CACHE_TRIM_BIN" <<'SH_TRIM'
#!/usr/bin/env bash
echo "$TEST_AFTER" > "$ZESU_GUARD_STATE/free"
SH_TRIM
chmod +x "$DUNE_CACHE_TRIM_BIN"
hold_reason() { :; }
compiler_pids() { :; }
marker=$(reserve_coqc $$)
confirm_coqc "$marker"; status=$?
cat "$LOG"
exit "$status"
""", TEST_AFTER=str(after), ZESU_DIAGNOSTIC_PROBE=flag,
                                            ZESU_MODULE_LIMIT_GIB=memory,
                                            ZESU_PROOF_CPU_LIMIT="unlimited", ZESU_PROBE_ISSUE="10")
                    self.assertEqual(result.returncode, 0 if allowed else 3, result.stderr)
                    self.assertIn(f"free_bytes={after}", result.stdout)
                    self.assertEqual("REFUSE probe launch" in result.stdout, not allowed)

    def test_disk_trim_failure_retains_output_and_rechecks_free_space(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 30000000000; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho fixture-trim-error >&2\nexit 7\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission || exit $?
cat "$LOG" "$STATE_DIR/cache-trim.log"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("status=7 free_bytes=30000000000", result.stdout)
        self.assertIn("fixture-trim-error", result.stdout)

    def test_cache_maintenance_is_serialized(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 59000000000; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
cat > "$DUNE_CACHE_TRIM_BIN" <<'SH_TRIM'
#!/usr/bin/env bash
echo start >> "$ZESU_GUARD_STATE/events"
sleep 0.05
echo end >> "$ZESU_GUARD_STATE/events"
SH_TRIM
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission & one=$!
cache_disk_admission & two=$!
wait "$one" || exit 91
wait "$two" || exit 92
cat "$STATE_DIR/events"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["start", "end"])

    def test_waiter_rechecks_space_after_serialized_maintenance(self):
        result = self.run_guard(r"""
echo 59000000000 > "$STATE_DIR/free"
home_free_bytes() { cat "$STATE_DIR/free"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
cat > "$DUNE_CACHE_TRIM_BIN" <<'SH_TRIM'
#!/usr/bin/env bash
echo trim >> "$ZESU_GUARD_STATE/events"
sleep 0.05
echo 60000000000 > "$ZESU_GUARD_STATE/free"
SH_TRIM
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission & one=$!
cache_disk_admission & two=$!
wait "$one" || exit 91
wait "$two" || exit 92
cat "$STATE_DIR/events"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "trim")

    def test_confirmed_scope_keeps_its_admission_on_low_disk(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 0; }
marker="$COQC_RESERVATIONS/$$.confirmed"
printf 'confirmed\nwriter=\naggregate=\n' > "$marker"
confirm_coqc "$marker" || exit $?
[ ! -e "$STATE_DIR/cache-trim.log" ] || exit 91
[ "$(head -n 1 "$marker")" = confirmed ] || exit 92
""", ZESU_DIAGNOSTIC_PROBE="cpu-only", ZESU_MODULE_LIMIT_GIB="6",
                                ZESU_PROOF_CPU_LIMIT="unlimited", ZESU_PROBE_ISSUE="10")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_invalid_disk_measurement_refuses_launch(self):
        result = self.run_guard('home_free_bytes() { echo unavailable; }; cache_disk_admission')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("cannot read /home free bytes", result.stderr)

    def test_concurrent_low_interval_trims_once(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 54000000000; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho trim >> "$ZESU_GUARD_STATE/events"\nsleep 0.05\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
pids=()
for i in {1..10}; do cache_disk_admission & pids+=("$!"); done
for pid in "${pids[@]}"; do wait "$pid" || exit 91; done
cache_disk_admission || exit 92
[ -e "$STATE_DIR/cache-low-space" ] || exit 93
cat "$STATE_DIR/events"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["trim"])

    def test_new_low_crossing_trims_again(self):
        result = self.run_guard(r"""
echo 54000000000 > "$STATE_DIR/free"
home_free_bytes() { cat "$STATE_DIR/free"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho trim >> "$ZESU_GUARD_STATE/events"\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission || exit 91
cache_disk_admission || exit 92
[ -e "$STATE_DIR/cache-low-space" ] || exit 93
echo 60000000000 > "$STATE_DIR/free"
cache_disk_admission || exit 94
[ ! -e "$STATE_DIR/cache-low-space" ] || exit 95
echo 59999999999 > "$STATE_DIR/free"
cache_disk_admission || exit 96
cat "$STATE_DIR/events"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["trim", "trim"])

    def test_probe_below_twenty_retrims_despite_low_marker(self):
        for flag in ("1", "cpu-only"):
            for after in (19999999999, 20000000000):
                with self.subTest(flag=flag, after=after):
                    result = self.run_guard(r"""
echo 19999999999 > "$STATE_DIR/free"
: > "$STATE_DIR/cache-low-space"
home_free_bytes() { cat "$STATE_DIR/free"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
cat > "$DUNE_CACHE_TRIM_BIN" <<'SH_TRIM'
#!/usr/bin/env bash
echo trim >> "$ZESU_GUARD_STATE/events"
echo "$TEST_AFTER" > "$ZESU_GUARD_STATE/free"
SH_TRIM
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission; status=$?
cat "$STATE_DIR/events"
exit "$status"
""", ZESU_DIAGNOSTIC_PROBE=flag, TEST_AFTER=str(after))
                    self.assertEqual(result.returncode, 3 if after < 20000000000 else 0,
                                     result.stderr)
                    self.assertEqual(result.stdout.splitlines(), ["trim"])

    def test_each_probe_below_twenty_retries_and_refuses(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 19000000000; }
: > "$STATE_DIR/cache-low-space"
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho trim >> "$ZESU_GUARD_STATE/events"\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission; [ "$?" = 3 ] || exit 91
cache_disk_admission; [ "$?" = 3 ] || exit 92
cat "$STATE_DIR/events"
""", ZESU_DIAGNOSTIC_PROBE="cpu-only")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["trim", "trim"])

    def test_probe_at_twenty_keeps_low_interval_marker(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 20000000000; }
: > "$STATE_DIR/cache-low-space"
DUNE_CACHE_TRIM_BIN="$STATE_DIR/not-a-real-dune"
cache_disk_admission || exit 91
[ -e "$STATE_DIR/cache-low-space" ] || exit 92
[ ! -e "$STATE_DIR/cache-trim.log" ] || exit 93
""", ZESU_DIAGNOSTIC_PROBE="cpu-only")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_failed_trim_does_not_mark_interval_complete(self):
        result = self.run_guard(r"""
home_free_bytes() { echo 30000000000; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho failure >> "$ZESU_GUARD_STATE/events"\nexit 7\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission || exit 91
[ ! -e "$STATE_DIR/cache-low-space" ] || exit 92
cache_disk_admission || exit 93
[ ! -e "$STATE_DIR/cache-low-space" ] || exit 94
cat "$STATE_DIR/events"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), ["failure", "failure"])

    def test_invalid_measurement_after_trim_does_not_mark_interval(self):
        result = self.run_guard(r"""
echo 59000000000 > "$STATE_DIR/free"
home_free_bytes() { cat "$STATE_DIR/free"; }
DUNE_CACHE_TRIM_BIN="$STATE_DIR/dune"
printf '#!/usr/bin/env bash\necho invalid > "$ZESU_GUARD_STATE/free"\n' > "$DUNE_CACHE_TRIM_BIN"
chmod +x "$DUNE_CACHE_TRIM_BIN"
cache_disk_admission; [ "$?" = 2 ] || exit 91
[ ! -e "$STATE_DIR/cache-low-space" ] || exit 92
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_admitted_scope_sets_unlimited_stack_and_preserves_cpu_limit(self):
        for cpu, expected_cpu in (("1200", 1200), ("unlimited", -1)):
            with self.subTest(cpu=cpu):
                result = self.run_guard(r"""
ulimit -S -s 8192
apply_scope_limits || exit 91
python3 - <<'PY_LIMITS'
import json, resource
print(json.dumps({"stack": resource.getrlimit(resource.RLIMIT_STACK),
                  "cpu": resource.getrlimit(resource.RLIMIT_CPU)}))
PY_LIMITS
""", ZESU_SCOPE_CPU=cpu)
                self.assertEqual(result.returncode, 0, result.stderr)
                limits = json.loads(result.stdout)
                self.assertEqual(limits["stack"], [-1, -1])
                self.assertEqual(limits["cpu"], [expected_cpu, expected_cpu])

    def test_scope_exec_applies_limits_for_arms_and_both_probe_types(self):
        cases = (({}, 2400),
                 ({"ZESU_DIAGNOSTIC_PROBE": "1", "ZESU_MODULE_LIMIT_GIB": "64",
                   "ZESU_PROOF_CPU_LIMIT": "unlimited", "ZESU_SCOPE_CPU": "unlimited",
                   "ZESU_PROBE_ISSUE": "10"}, -1),
                 ({"ZESU_DIAGNOSTIC_PROBE": "cpu-only", "ZESU_MODULE_LIMIT_GIB": "6",
                   "ZESU_PROOF_CPU_LIMIT": "unlimited", "ZESU_SCOPE_CPU": "unlimited",
                   "ZESU_PROBE_ISSUE": "10"}, -1))
        for variables, cpu in cases:
            with self.subTest(variables=variables):
                # Replace admission in this private fixture. Keep the real dispatch.
                result = self.run_guard(r"""
confirm_coqc() { :; }
mark_coqc() { :; }
cat() {
  if [[ "$1" == /proc/*/cgroup ]]; then
    printf '0::/user.slice/zesuworkloads.slice/fixture.scope\n'
  else command cat "$@"; fi
}
systemctl() {
  [ "$*" = '--user show zesuworkloads.slice -p MemoryMax -p MemorySwapMax' ] || return 2
  printf 'MemoryMax=187904819200\nMemorySwapMax=0\n'
}
ulimit -S -s 8192
set -- scope-exec fixture -- python3 -c 'import json, resource; print(json.dumps({"stack":resource.getrlimit(resource.RLIMIT_STACK), "cpu":resource.getrlimit(resource.RLIMIT_CPU)}))'
""" + DISPATCH, **variables)
                self.assertEqual(result.returncode, 0, result.stderr)
                limits = json.loads(result.stdout)
                self.assertEqual(limits["stack"], [-1, -1])
                self.assertEqual(limits["cpu"], [cpu, cpu])

    def test_termination_record_retains_actual_stack_limits(self):
        for soft, hard, expected in (("8388608", "unlimited", [8388608, None]),
                                     ("unlimited", "unlimited", [None, None])):
            with self.subTest(soft=soft, hard=hard):
                result = self.run_guard(r"""
PROC_ROOT="$STATE_DIR/proc"
CGROUP_ROOT="$STATE_DIR/cgroup"
mkdir -p "$PROC_ROOT/123" "$CGROUP_ROOT/fixture.scope"
printf '123 (coqc) R 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 456 0\n' > "$PROC_ROOT/123/stat"
printf '0::/fixture.scope\n' > "$PROC_ROOT/123/cgroup"
printf 'Max stack size            %s              %s            bytes\n' "$TEST_SOFT" "$TEST_HARD" > "$PROC_ROOT/123/limits"
printf '123\n' > "$CGROUP_ROOT/fixture.scope/cgroup.procs"
systemctl() { printf 'ControlGroup=/fixture.scope\nKillSignal=15\n'; }
record_scope_termination fixture.scope SIGKILL memory-boundary
cat "$STATE_DIR/terminations.jsonl"
""", TEST_SOFT=soft, TEST_HARD=hard)
                self.assertEqual(result.returncode, 0, result.stderr)
                record = json.loads(result.stdout)
                self.assertEqual(record["pid"], 123)
                self.assertTrue(record["stack_limits_available"])
                self.assertEqual([record["stack_limits"]["soft_bytes"],
                                  record["stack_limits"]["hard_bytes"]], expected)

    def test_worker_count_uses_70_percent_and_preserves_headroom(self):
        result = self.run_guard(r"""
JOB_GIB=3
available_gib() { echo 180; }
[ "$(guard_jobs)" = 42 ] || exit 91
available_gib() { echo 26; }
[ "$(guard_jobs)" = 2 ] || exit 92
available_gib() { echo 250; }
[ "$(guard_jobs)" = 48 ]
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_interim_six_slot_gate_admits_an_ordinary_compiler(self):
        result = self.run_guard(r"""
hold_reason() { :; }
compiler_pids() { echo 123; }
printf 'state=held holder=fixture pid=%s start=x\n' "$$" > "$GATE_LOCK"
request=$(reserve_coqc $$)
sleep() { echo unexpected-cap-wait >&2; exit 91; }
confirm_coqc "$request" || exit 92
[ "$(head -n 1 "$request")" = confirmed ]
""", ZESU_MAX_COQC="6", ZESU_IN_GATE="1")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_available_memory_launch_boundaries(self):
        for limit, available, allowed in ((6, 26, True), (6, 25, False),
                                          (64, 84, True), (64, 83, False)):
            with self.subTest(limit=limit, available=available):
                result = self.run_guard(r"""
available_gib() { echo "$TEST_AVAILABLE"; }
memory_hold_reason
""", ZESU_MODULE_LIMIT_GIB=str(limit), TEST_AVAILABLE=str(available))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(not result.stdout.strip(), allowed)

    def test_small_memory_requests_still_obey_global_and_writer_limits(self):
        result = self.run_guard(r"""
MEMORY_CLAIM_BYTES=$GIB
MAX_COQC=48
compiler_pids() { seq 1 48; }
live_reservations() { :; }
[ -n "$(compiler_admission_reason)" ] || exit 90
compiler_pids() { :; }
WRITER_ID=fixture
WRITER_MAX_COQC=8
live_reservations() { printf '%s\n' "$STATE_DIR"/slot{1..8}; }
reservation_writer() { echo fixture; }
reservation_compiler() { :; }
for i in {1..8}; do echo confirmed > "$STATE_DIR/slot$i"; done
[ -n "$(compiler_admission_reason)" ] || exit 91
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_available_memory_hold_and_kill_boundaries(self):
        for available, held, killed in ((20, False, False), (19, True, False),
                                        (11, True, False), (10, True, True), (9, True, True)):
            with self.subTest(available=available):
                result = self.run_guard(r"""
available_gib() { echo "$TEST_AVAILABLE"; }
memory() { echo "0 0 $(( TEST_AVAILABLE * GIB ))"; }
case "$(memory_hold_reason)" in *'20 GiB hold') echo held ;; esac
if memory_kill_required; then echo killed; fi
""", TEST_AVAILABLE=str(available))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual("held" in result.stdout.splitlines(), held)
                self.assertEqual("killed" in result.stdout.splitlines(), killed)

    def test_kill_boundary_compares_exact_available_bytes(self):
        for difference, killed in ((-1, True), (0, True), (1, False)):
            with self.subTest(difference=difference):
                result = self.run_guard(r"""
memory() { echo "0 0 $((10 * GIB + TEST_DIFFERENCE))"; }
if memory_kill_required; then echo killed; fi
""", TEST_DIFFERENCE=str(difference))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual("killed" in result.stdout.splitlines(), killed)

    def test_available_policy_ignores_retired_used_thresholds(self):
        result = self.run_guard(r"""
MODULE_LIMIT_GIB=6
available_gib() { echo 26; }
used_gib() { echo 230; }
memory() { echo "0 0 $((26 * GIB))"; }
[ -z "$(memory_hold_reason)" ] || exit 91
if memory_kill_required; then exit 92; fi
JOB_GIB=6
[ "$(guard_jobs)" = 1 ]
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def account_guard(self, script, **variables):
        return self.run_guard(ACCOUNT_SETUP + script, TEST_ACCOUNT=str(ACCOUNT_FIXTURE), **variables)

    def test_captured_host_admits_under_another_accounts_load(self):
        result = self.account_guard(r"""
cpu_signal; io_signal; load_five; echo
account_memory; used_gib; available_gib; memory_scope
record_peak; cat "$PEAK"
echo "hold=$(hold_reason)"
rm "$ACCOUNT_CGROUP/cpu.pressure" "$ACCOUNT_CGROUP/io.pressure"
echo "fallback=$(hold_reason)"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [
            "cpu-pressure 5 50", "io-pressure 1 50", "432",
            "163208757248 33225204464", "30", "121",
            "account of 152 GiB (launch <80 %, hold 88 %, kill 95 %), "
            "machine available 140 GiB (backstop 12)",
            "33225204464", "hold=", "fallback=load5 432"])

    def test_account_memory_lines_are_fractions_of_the_cap(self):
        cap = 152 * 1024 ** 3
        edges = {pct: -(-cap * pct // 100) for pct in (80, 88, 95)}
        launch, hold = "launch line 80 %", "at the 88 % hold"
        for used, reason, killed in ((edges[80] - 1, "", False), (edges[80], launch, False),
                                     (edges[88] - 1, launch, False), (edges[88], hold, False),
                                     (edges[95] - 1, hold, False), (edges[95], hold, True)):
            with self.subTest(used=used):
                result = self.account_guard(r"""
echo $(( TEST_USED + 3 )) > "$ACCOUNT_CGROUP/memory.current"
printf 'anon %s\nactive_file 1\ninactive_file 1\nslab_reclaimable 1\n' "$TEST_USED" > "$ACCOUNT_CGROUP/memory.stat"
echo "reason=$(memory_hold_reason)"
if memory_kill_required; then echo killed; fi
""", ZESU_MODULE_LIMIT_GIB="6", TEST_USED=str(used))
                self.assertEqual(result.returncode, 0, result.stderr)
                lines = result.stdout.splitlines()
                self.assertTrue(lines[0].startswith("reason="), result.stdout)
                self.assertTrue(lines[0].endswith(reason) if reason else lines[0] == "reason=",
                                result.stdout)
                self.assertEqual("killed" in lines, killed)

    def test_account_use_excludes_file_cache_and_reclaimable_slab(self):
        result = self.account_guard(r"""
echo $(( 140 * GIB )) > "$ACCOUNT_CGROUP/memory.current"
printf 'anon 1\nactive_file %s\ninactive_file %s\nslab_reclaimable %s\n' $GIB $GIB $(( 51 * GIB )) > "$ACCOUNT_CGROUP/memory.stat"
echo "$(used_gib) reason=$(memory_hold_reason)"
printf 'anon 1\nkernel %s\n' $(( 52 * GIB )) > "$ACCOUNT_CGROUP/memory.stat"
echo "$(used_gib) reason=$(memory_hold_reason)"
if memory_kill_required; then echo killed; fi
echo max > "$ACCOUNT_CGROUP/memory.max"
echo $(( 134 * GIB )) > "$ACCOUNT_CGROUP/memory.current"
memory_hold_reason
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [
            "87 reason=", "140 reason=account memory 140 of 152 GiB, at the 88 % hold",
            "account memory 134 of 152 GiB, at the 88 % hold"])

    def test_machine_memory_holds_only_below_its_backstop_and_never_kills(self):
        for available, reason in ((25, ""), (12, ""),
                                  (11, "machine memory available 11 GiB, below the 12 GiB backstop")):
            with self.subTest(available=available):
                result = self.account_guard(r"""
memory() { echo $(( 251 * GIB )) $(( (251 - TEST_AVAILABLE) * GIB )) $(( TEST_AVAILABLE * GIB )); }
echo "reason=$(memory_hold_reason)"
if memory_kill_required; then echo killed; fi
""", TEST_AVAILABLE=str(available))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), ["reason=" + reason])
        result = self.account_guard(r"""
memory() { echo $(( 251 * GIB )) $(( 226 * GIB )) $(( 25 * GIB )); }
memory_hold_reason
""", ZESU_MACHINE_MIN_AVAILABLE_GIB="30")
        self.assertEqual(result.stdout.strip(),
                         "machine memory available 25 GiB, below the 30 GiB backstop")

    def test_account_job_room_and_percent_overrides(self):
        result = self.account_guard(r"""
printf 'anon 1\n' > "$ACCOUNT_CGROUP/memory.stat"
echo $(( 100 * GIB )) > "$ACCOUNT_CGROUP/memory.current"
memory_hold_reason
if memory_kill_required; then echo killed; fi
""", ZESU_MODULE_LIMIT_GIB="64", ZESU_LAUNCH_PCT="70", ZESU_KILL_PCT="65")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [
            "account memory available 52 GiB, requires 84 GiB for a 64 GiB job", "killed"])
        for name, value in (("ZESU_HOLD_PCT", "0"), ("ZESU_HOLD_PCT", "101"),
                            ("ZESU_LAUNCH_PCT", "8x")):
            with self.subTest(**{name: value}):
                self.assertEqual(self.run_guard("true", **{name: value}).returncode, 2)

    def test_account_pressure_limits_use_some_cpu_and_full_io(self):
        for cpu, io, limit, reason in (("50.00", "50.00", "50", ""),
                                       ("50.01", "0.00", "50", "cpu-pressure 51"),
                                       ("0.00", "60.00", "50", "io-pressure 60"),
                                       ("55.00", "55.00", "60", "")):
            with self.subTest(cpu=cpu, io=io, limit=limit):
                result = self.account_guard(r"""
printf 'some avg10=0.00 avg60=%s avg300=0.00 total=1\nfull avg10=0.00 avg60=99.00 avg300=0.00 total=1\n' "$TEST_CPU" > "$ACCOUNT_CGROUP/cpu.pressure"
printf 'some avg10=0.00 avg60=99.00 avg300=0.00 total=1\nfull avg10=0.00 avg60=%s avg300=0.00 total=1\n' "$TEST_IO" > "$ACCOUNT_CGROUP/io.pressure"
echo "reason=$(hold_reason)"
""", TEST_CPU=cpu, TEST_IO=io, ZESU_MAX_CPU_PRESSURE=limit, ZESU_MAX_IO_PRESSURE=limit)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "reason=" + reason)

    def test_probe_confirmation_requires_84_gib_available(self):
        result = self.run_guard(r"""
available_gib() { echo 83; }
coqc_count() { echo 0; }
compiler_pids() { :; }
load_five() { echo 0; }
blocked_count() { echo 0; }
request=$(reserve_coqc $$)
sleep() { [ ! -e "$request" ] || exit 92; exit 91; }
wait_for_admission_change() { [ ! -e "$request" ] || exit 92; exit 91; }
confirm_coqc "$request"
""", ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
                                ZESU_MODULE_LIMIT_GIB="64",
                                ZESU_PROOF_CPU_LIMIT="unlimited")
        self.assertEqual(result.returncode, 91, result.stderr)

    def test_running_probe_yields_to_gate_but_keeps_resource_accounting(self):
        result = self.run_guard(r"""
fixture_marker="$COQC_RESERVATIONS/$$.probe"
printf '123\nwriter=\naggregate=\nprobe=issue10\nmemory_gib=64\ncpu=unlimited\nowner_start=%s\nscope=fixture-probe.scope\n' "$(process_start $$)" > "$fixture_marker"
mark_probe_scope "$fixture_marker" fixture-probe.scope || exit 90
live_reservations() { echo "$fixture_marker"; }
live_scopes() { echo fixture-probe.scope; }
live_launches() { :; }
compiler_pids() { echo 123; }
reservation_compiler() { echo 123; }
printf 'state=wanted holder=fixture pid=%s start=x\n' "$$" > "$GATE_LOCK"
sleep() { echo unexpected-gate-wait >&2; exit 91; }
lock_hold $$ || exit 92
grep -q '^state=held ' "$GATE_LOCK" || exit 93
[ "$(probe_count)" = 1 ] || exit 94
[ "$(nonwriter_coqc_count)" = 1 ] || exit 95
MAX_COQC=1
[ -n "$(compiler_admission_reason)" ] || exit 96
available_gib() { echo 25; }
[ "$(hold_reason)" = 'memory available 25 GiB, requires 36 GiB for a 16 GiB job' ] || exit 97
mark_coqc "$fixture_marker" $$ || exit 98
probe_record "$fixture_marker" || exit 99
grep -Fxq 'scope=fixture-probe.scope' "$fixture_marker"
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_gate_still_drains_ordinary_scopes_and_launches(self):
        result = self.run_guard(r"""
live_reservations() { :; }
live_scopes() { [ -f "$STATE_DIR/drained" ] || echo ordinary.scope; }
live_launches() { [ -f "$STATE_DIR/drained" ] || echo "$LAUNCHES/ordinary"; }
printf 'confirmed\nwriter=\n' > "$LAUNCHES/ordinary"
printf 'state=wanted holder=fixture pid=%s start=x\n' "$$" > "$GATE_LOCK"
sleep() { echo drained-ordinary; touch "$STATE_DIR/drained"; }
lock_hold $$
grep -q '^state=held ' "$GATE_LOCK"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "drained-ordinary")

    def test_probe_tag_rejects_wrong_limits_and_reused_owner(self):
        for memory, cpu, start in (("6", "unlimited", "actual"),
                                   ("64", "1200", "actual"),
                                   ("64", "unlimited", "0")):
            with self.subTest(memory=memory, cpu=cpu, start=start):
                result = self.run_guard(r"""
marker="$COQC_RESERVATIONS/$$.probe"
start="$TEST_START"
[ "$start" != actual ] || start=$(process_start $$)
printf 'confirmed\nwriter=\naggregate=\nprobe=issue10\nmemory_gib=%s\ncpu=%s\nowner_start=%s\n' "$TEST_MEMORY" "$TEST_CPU" "$start" > "$marker"
if probe_record "$marker"; then exit 91; fi
[ "$(gate_reservations)" = "$marker" ]
""", TEST_MEMORY=memory, TEST_CPU=cpu, TEST_START=start)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_six_probe_slots_are_atomic_across_simultaneous_requests(self):
        result = self.run_guard(r"""
hold_reason() { :; }
compiler_pids() { :; }
POLL_SECONDS=0.01
worker() {
  local owner=$BASHPID marker
  if (( $1 % 2 )); then
    ZESU_DIAGNOSTIC_PROBE=cpu-only; MODULE_LIMIT_GIB=6
  fi
  marker=$(reserve_coqc "$owner") || return
  confirm_coqc "$marker" || return
  confirm_coqc "$marker" || return
  printf 'start %s\n' "$owner" >> "$STATE_DIR/events"
  while [ ! -e "$STATE_DIR/release" ]; do sleep 0.01; done
  sleep 0.08
  printf 'end %s\n' "$owner" >> "$STATE_DIR/events"
  release_coqc "$marker"
}
pids=""
for n in 1 2 3 4 5 6 7 8 9 10 11 12; do worker "$n" & pids="$pids $!"; done
for attempt in {1..200}; do
  [ "$(probe_count)" -eq 6 ] && break
  sleep 0.01
done
[ "$(probe_count)" -eq 6 ] || exit 92
touch "$STATE_DIR/release"
for pid in $pids; do wait "$pid" || exit 91; done
cat "$STATE_DIR/events"
[ "$(probe_count)" = 0 ]
""", ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
                                     ZESU_MODULE_LIMIT_GIB="64",
                                     ZESU_PROOF_CPU_LIMIT="unlimited", ZESU_PROBE_AGGREGATE_LIMIT="6")
        self.assertEqual(result.returncode, 0, result.stderr)
        active = set()
        peak = 0
        starts = 0
        for line in result.stdout.splitlines():
            event, pid = line.split()
            if event == "start":
                active.add(pid)
                starts += 1
                peak = max(peak, len(active))
            else:
                active.remove(pid)
        self.assertEqual(starts, 12)
        self.assertEqual(peak, 6)
        self.assertFalse(active)

    def test_cpu_only_probe_uses_six_gib_and_the_shared_probe_slot(self):
        result = self.run_guard(r"""
available_gib() { echo 26; }
load_five() { echo 0; }
blocked_count() { echo 0; }
compiler_pids() { :; }
[ -z "$(memory_hold_reason)" ] || exit 90
marker=$(reserve_coqc $$)
confirm_coqc "$marker" || exit 91
grep -Fxq 'probe=issue10-cpu-only' "$marker" || exit 92
grep -Fxq 'memory_gib=6' "$marker" || exit 93
[ "$(probe_count)" = 1 ] || exit 94
mark_probe_scope "$marker" fixture-cpu-only.scope || exit 95
live_scopes() { echo fixture-cpu-only.scope; }
[ -z "$(gate_scopes)" ] || exit 96
available_gib() { echo 25; }
[ -n "$(memory_hold_reason)" ] || exit 97
release_coqc "$marker"
""", ZESU_DIAGNOSTIC_PROBE="cpu-only", ZESU_PROBE_ISSUE="10",
                                     ZESU_MODULE_LIMIT_GIB="6",
                                     ZESU_PROOF_CPU_LIMIT="unlimited")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_cpu_only_probe_rejects_incoherent_fences(self):
        baseline = {"ZESU_DIAGNOSTIC_PROBE": "cpu-only", "ZESU_PROBE_ISSUE": "10",
                    "ZESU_MODULE_LIMIT_GIB": "6", "ZESU_PROOF_CPU_LIMIT": "unlimited"}
        for change in ({"ZESU_MODULE_LIMIT_GIB": "64"}, {"ZESU_PROBE_ISSUE": ""},
                       {"ZESU_PROOF_CPU_LIMIT": "1200"}, {"ZESU_IN_GATE": "1"}):
            with self.subTest(change=change):
                result = self.run_guard("validate_probe_scope", **{**baseline, **change})
                self.assertEqual(result.returncode, 2, result.stderr)

    def test_cpu_only_probe_tag_keeps_owner_and_memory_validation(self):
        for memory, start in (("64", "$(process_start $$)"), ("6", "0")):
            result = self.run_guard(f"""
marker="$COQC_RESERVATIONS/$$.probe"
printf 'confirmed\nprobe=issue10-cpu-only\nmemory_gib={memory}\ncpu=unlimited\nowner_start=%s\n' "{start}" > "$marker"
if probe_record "$marker"; then exit 91; fi
""")
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_memory_kill_records_owned_identity_before_signal(self):
        result = self.run_guard(r"""
PROC_ROOT="$STATE_DIR/proc"
CGROUP_ROOT="$STATE_DIR/cgroup"
mkdir -p "$PROC_ROOT/123" "$CGROUP_ROOT/fixture.scope"
printf '123 (coqc) R 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 456 0\n' > "$PROC_ROOT/123/stat"
printf '0::/fixture.scope\n' > "$PROC_ROOT/123/cgroup"
printf '123\n' > "$CGROUP_ROOT/fixture.scope/cgroup.procs"
youngest_scope() { echo fixture.scope; }
systemctl() {
  case "$2" in
    show) printf 'ControlGroup=/fixture.scope\nKillSignal=15\n' ;;
    kill) [ -s "$STATE_DIR/terminations.jsonl" ] || return 91
          rm "$PROC_ROOT/123/stat"; printf '' > "$CGROUP_ROOT/fixture.scope/cgroup.procs" ;;
    stop) : ;;
  esac
}
kill_youngest >/dev/null || exit 92
cat "$STATE_DIR/terminations.jsonl"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        first = records[0]
        self.assertEqual((first["pid"], first["start_ticks"], first["scope"]),
                         (123, 456, "fixture.scope"))
        self.assertEqual(first["pid"], 123)
        self.assertFalse(first["stack_limits_available"])
        self.assertIsNone(first["stack_limits"])
        self.assertEqual(first["stack_limit_error"], "FileNotFoundError")
        self.assertEqual((first["signal"], first["cause"], first["phase"]),
                         ("SIGKILL", "memory-boundary", "before-request"))
        self.assertEqual(records[1]["cause"], "memory-boundary-cleanup")

    def test_aggregate_stop_records_each_descendant_scope(self):
        result = self.run_guard(r"""
PROC_ROOT="$STATE_DIR/proc"
CGROUP_ROOT="$STATE_DIR/cgroup"
for pid in 123 124; do
  mkdir -p "$PROC_ROOT/$pid" "$CGROUP_ROOT/fixture.slice/job-$pid.scope"
  printf '%s (coqc) R 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 456 0\n' "$pid" > "$PROC_ROOT/$pid/stat"
  printf '0::/fixture.slice/job-%s.scope\n' "$pid" > "$PROC_ROOT/$pid/cgroup"
  printf '%s\n' "$pid" > "$CGROUP_ROOT/fixture.slice/job-$pid.scope/cgroup.procs"
done
mkdir -p "$CGROUP_ROOT/fixture.slice/empty.scope"
: > "$CGROUP_ROOT/fixture.slice/empty.scope/cgroup.procs"
systemctl() {
  case "$2" in
    show) printf 'ControlGroup=/fixture.slice\nKillSignal=15\n' ;;
    stop) [ -s "$STATE_DIR/terminations.jsonl" ] ;;
  esac
}
stop_scope fixture.slice aggregate-cleanup || exit 91
cat "$STATE_DIR/terminations.jsonl"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        records = [json.loads(line) for line in result.stdout.splitlines()]
        self.assertEqual([(r["pid"], r["scope"]) for r in records],
                         [(123, "job-123.scope"), (124, "job-124.scope"), (None, "empty.scope")])
        self.assertTrue(all(r["signal"] == "SIGTERM" and
                            r["cause"] == "aggregate-cleanup" and
                            r["requested_unit"] == "fixture.slice" for r in records))

    def test_changed_cgroup_does_not_attribute_a_foreign_scope(self):
        result = self.run_guard(r"""
PROC_ROOT="$STATE_DIR/proc"
CGROUP_ROOT="$STATE_DIR/cgroup"
mkdir -p "$PROC_ROOT/123" "$CGROUP_ROOT/fixture.scope"
printf '123 (coqc) R 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 456 0\n' > "$PROC_ROOT/123/stat"
printf '0::/foreign.scope\n' > "$PROC_ROOT/123/cgroup"
printf '123\n' > "$CGROUP_ROOT/fixture.scope/cgroup.procs"
systemctl() { printf 'ControlGroup=/fixture.scope\nKillSignal=15\n'; }
record_scope_termination fixture.scope SIGKILL memory-boundary
cat "$STATE_DIR/terminations.jsonl"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(result.stdout)
        self.assertEqual(record["scope"], "fixture.scope")
        self.assertEqual(record["identity_error"], "cgroup-changed")

    def test_empty_stop_records_unavailable_pid_and_signal(self):
        result = self.run_guard(r"""
systemctl() { :; }
stop_scope fixture.scope empty-scope
cat "$STATE_DIR/terminations.jsonl"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(result.stdout)
        self.assertIsNone(record["pid"])
        self.assertIsNone(record["signal"])
        self.assertEqual(record["scope"], "fixture.scope")
        self.assertEqual(record["cause"], "empty-scope")
        self.assertIsNone(record["stack_limits"])
        self.assertFalse(record["stack_limits_available"])

    def test_scope_fences_require_configured_limit_or_valid_issue10_probe(self):
        cases = (({}, 0), ({"ZESU_MODULE_LIMIT_GIB": "64"}, 2),
                 ({"ZESU_MODULE_LIMIT_GIB": "12"}, 2),
                 ({"ZESU_DIAGNOSTIC_PROBE": "1", "ZESU_PROBE_ISSUE": "10",
                   "ZESU_MODULE_LIMIT_GIB": "64",
                   "ZESU_PROOF_CPU_LIMIT": "unlimited"}, 0))
        for variables, expected in cases:
            with self.subTest(variables=variables):
                result = self.run_guard("validate_probe_scope", **variables)
                self.assertEqual(result.returncode, expected, result.stderr)

    def test_ordinary_scope_defaults_to_the_configured_gate_limit(self):
        for memory in (6, 16, 32):
            with self.subTest(memory=memory):
                result = self.run_guard("validate_probe_scope && echo $MODULE_LIMIT_GIB",
                                        ZESU_GATE_MODULE_LIMIT_GIB=str(memory))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(memory))

    def test_ordinary_scope_accepts_every_configured_gate_limit(self):
        for memory in range(6, 33):
            with self.subTest(memory=memory):
                result = self.run_guard("validate_probe_scope", ZESU_IN_GATE="1",
                                        ZESU_GATE_MODULE_LIMIT_GIB=str(memory),
                                        ZESU_MODULE_LIMIT_GIB=str(memory))
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_ordinary_scope_rejects_invalid_or_mismatched_gate_limits(self):
        cases = [(limit, limit) for limit in
                 ("", "0", "5", "33", "64", "-6", "6.5", "invalid")]
        cases.extend((("32", "6"), ("6", "32"), ("16", "invalid")))
        for configured, module in cases:
            with self.subTest(configured=configured, module=module):
                result = self.run_guard("validate_probe_scope",
                                        ZESU_GATE_MODULE_LIMIT_GIB=configured,
                                        ZESU_MODULE_LIMIT_GIB=module)
                self.assertEqual(result.returncode, 2, result.stderr)

    def test_configured_gate_limit_preserves_diagnostic_probe_fences(self):
        for flag, memory in (("1", "64"), ("cpu-only", "6")):
            with self.subTest(flag=flag):
                result = self.run_guard("validate_probe_scope",
                                        ZESU_GATE_MODULE_LIMIT_GIB="32",
                                        ZESU_DIAGNOSTIC_PROBE=flag,
                                        ZESU_MODULE_LIMIT_GIB=memory,
                                        ZESU_PROOF_CPU_LIMIT="unlimited",
                                        ZESU_PROBE_ISSUE="10")
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_gate_acquires_lock_after_empty_scope_cleanup(self):
        result = self.run_guard('''
fixture_unit="${SCOPE_PREFIX}-dune-coqc-2147483647-92.scope"
printf '%s\\n' "$fixture_unit" > "$REGISTRY"
printf 'state=wanted holder=fixture pid=%s start=x\\n' "$$" > "$GATE_LOCK"
systemctl() {
  case "$2" in
    list-units) [ -f "$STATE_DIR/stopped" ] || printf '%s active running fixture\\n' "$fixture_unit" ;;
    show) printf '0\\n' ;;
    stop) touch "$STATE_DIR/stopped" ;;
  esac
}
live_launches() { :; }
gate_reservations() { :; }
lock_hold $$
prune_scope_registry
cat "$GATE_LOCK"
[ ! -s "$REGISTRY" ]
''')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("state=held", result.stdout)

    def test_empty_scope_requires_dead_launcher_and_successful_stop(self):
        for registered, launcher, tasks, stop, released in (
                (True, "2147483647", "0", 0, True),
                (True, "2147483647", "1", 0, False),
                (True, "2147483647", "[not set]", 0, False),
                (True, "$$", "0", 0, False),
                (False, "2147483647", "0", 0, False),
                (True, "2147483647", "0", 1, False)):
            with self.subTest(registered=registered, launcher=launcher,
                              tasks=tasks, stop=stop):
                script = f'''
fixture_unit="${{SCOPE_PREFIX}}-dune-coqc-{launcher}-92.scope"
{'printf "%s\\n" "$fixture_unit" > "$REGISTRY"' if registered else ':'}
systemctl() {{
  case "$2" in
    list-units) printf '%s active running fixture\\n' "$fixture_unit" ;;
    show) printf '%s\\n' '{tasks}' ;;
    stop) echo stopped >> "$STATE_DIR/stops"; return {stop} ;;
  esac
}}
live_scopes
'''
                result = self.run_guard(script)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(not result.stdout.strip(), released)

    @staticmethod
    def guard_environment(directory, **variables):
        helper = Path(directory) / "module_memory.py"
        helper.write_text("import sys\nsys.path.insert(0, " + repr(str(GUARD.parent)) + ")\n" + MEMORY_HELPER)
        ledger = Path(directory) / "LEDGER.json"
        ledger.write_text(json.dumps({"fixed_claims": {}, "region_claims": {}}))
        cgroups = Path(directory) / "cgroup"
        cgroups.mkdir()
        environment = {key: value for key, value in os.environ.items()
                       if not key.startswith("ZESU_")}
        environment.update(ZESU_GUARD_STATE=directory,
                           ZESU_GATE_LOCK=str(Path(directory) / "gate.lock"),
                           ZESU_RUN_REGISTRY=str(Path(directory) / "run-registry"),
                           ZESU_RUN_REGISTRY_TOOL=str(GUARD.with_name("run_registry.py")),
                           ZESU_CANONICAL_LEDGER=str(ledger),
                           ZESU_CGROUP_ROOT=str(cgroups),
                           ZESU_MODULE_MEMORY_TOOL=str(helper),
                           PYTHONDONTWRITEBYTECODE="1",
                           **variables)
        return environment

    # Legacy fixtures never inspect or trim the shared host cache.
    FIXTURE_PREFIX = "\nhome_free_bytes() { echo 60000000000; }\n"

    def run_guard(self, script, **variables):
        # Other test modules borrow this method, so it names its own class.
        with tempfile.TemporaryDirectory() as directory:
            environment = ResourceGuard.guard_environment(directory, **variables)
            return subprocess.run(["bash", "-c", LIBRARY + ResourceGuard.FIXTURE_PREFIX + script,
                                   str(GUARD.resolve())],
                                  text=True, capture_output=True, env=environment, timeout=120)

    def test_stop_closes_a_held_batch_whose_launching_shell_resumes_its_scheduler(self):
        # An agent's background shell continues a stopped child at once. The
        # registry froze every job of a held dune batch but waited for its
        # scheduler and reported stop_failed (2026-11-10).
        held = LIBRARY + self.FIXTURE_PREFIX + r"""
hold_reason() { echo "fixture hold"; }
compiler_pids() { :; }
POLL_SECONDS=0.05; WAKE_TIMEOUT=1
marker=$(reserve_coqc $$) || exit 9
confirm_coqc "$marker"
"""
        resuming_shell = (
            "import os, signal, sys\n"
            "pid = os.fork()\n"
            "if pid == 0:\n    os.execv(sys.argv[1], sys.argv[1:])\n"
            "while True:\n"
            "    _, status = os.waitpid(pid, os.WUNTRACED)\n"
            "    if os.WIFSTOPPED(status):\n        os.kill(pid, signal.SIGCONT)\n"
            "    else:\n        sys.exit(0)\n")
        with tempfile.TemporaryDirectory() as directory:
            environment = self.guard_environment(directory)
            store = Path(directory) / "run-registry"
            launcher = subprocess.Popen(
                [sys.executable, "-c", resuming_shell, sys.executable, str(GUARD.with_name("run_registry.py")),
                 "--store", str(store), "run", "--id", "held", "--kind", "fixture", "--owner", "test",
                 "--", "bash", "-c", held, str(GUARD.resolve())],
                env=environment, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                log = Path(directory) / "guard.log"
                deadline = time.monotonic() + 60
                while not (log.exists() and "HOLD reservation launch" in log.read_text()):
                    self.assertLess(time.monotonic(), deadline, "the fixture launch never held")
                    time.sleep(0.05)
                registry = run_registry.Registry(store)
                released = Path(directory) / "claim-released"
                registry.add_claim("held", "fixture", [sys.executable, "-c",
                                                       "import pathlib, sys; pathlib.Path(sys.argv[1]).touch()",
                                                       str(released)])
                registry.stop("held", grace=2.0)
                row = registry.read()["runs"]["held"]
                self.assertEqual(row["status"], "stopped")
                self.assertFalse(any(run_registry.live(actor) for actor in [row["scheduler"]] + row["jobs"]))
                self.assertTrue(row["claims"]["fixture"]["released"])
                self.assertTrue(released.exists())
                reservations = Path(directory) / "coqc-reservations"
                self.assertEqual(list(reservations.glob("*")) if reservations.exists() else [], [])
                ledger = json.loads((Path(directory) / "LEDGER.json").read_text())
                self.assertEqual(ledger["fixed_claims"], {})
                self.assertEqual(launcher.wait(timeout=30), 0)
            finally:
                if launcher.poll() is None:
                    launcher.kill()
                    launcher.wait()
                if store.exists():
                    # A failed stop leaves fixture actors; close them before the directory goes.
                    for row in run_registry.Registry(store).read()["runs"].values():
                        for actor in [row["scheduler"]] + row["jobs"]:
                            run_registry.send_signal(actor, run_registry.signal.SIGKILL)

    def test_held_launch_checks_published_totals_before_a_full_check(self):
        result = self.run_guard(r"""
MEMORY_CLAIM_BYTES=$((2 * GIB))
printf '%s\n' "$((10 * GIB)) $((10 * GIB)) $((100 * GIB)) $((11 * GIB)) -1 $((175 * GIB))" > "$ADMISSION_SUMMARY"
admission_plausible && echo room || echo full
printf '%s\n' "$((8 * GIB)) $((8 * GIB)) $((100 * GIB)) $((11 * GIB)) -1 $((175 * GIB))" > "$ADMISSION_SUMMARY"
admission_plausible && echo room || echo full
printf '%s\n' "$((300 * GIB)) $((300 * GIB)) $((100 * GIB)) $((150 * GIB)) $((10 * GIB)) $((175 * GIB))" > "$ADMISSION_SUMMARY"
admission_plausible && echo live || echo full
rm -f "$ADMISSION_SUMMARY"; admission_plausible && echo unknown || echo full
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["full", "room", "live", "unknown"])

    def test_owner_release_retries_a_draining_leaf_outside_the_mutex(self):
        script = r"""
count=0
release_coqc() {
  count=$((count + 1))
  if [ -e /proc/$BASHPID/fd/7 ]; then echo "mutex held between attempts"; fi
  [ "$count" -ge 3 ] && return 0
  return 5
}
ZESU_LEAF_DRAIN_POLL=0.01 release_coqc_drained "$COQC_RESERVATIONS/1.fixture"
echo "status=$? count=$count"
count=-1000
ZESU_LEAF_DRAIN_SECONDS=0 ZESU_LEAF_DRAIN_POLL=0.01 release_coqc_drained "$COQC_RESERVATIONS/1.fixture"
echo "bounded=$?"
grep -c "WAIT release: 1.fixture: compiler leaf draining" "$LOG"
"""
        result = self.run_guard(script)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["status=0", "count=3", "bounded=5", "2"])

    def test_dead_owner_recovery_waits_for_a_draining_leaf(self):
        with tempfile.TemporaryDirectory() as directory:
            fake = Path(directory) / "draining.py"
            fake.write_text("import sys\nprint('The shell compiler leaf is still draining.', file=sys.stderr)\n"
                            "raise SystemExit(5)\n")
            script = f"""
MEMORY_TOOL={fake}
recover_dead_reservation "$COQC_RESERVATIONS/2.fixture"
echo "status=$?"
grep -c "WAIT dead-owner reservation: 2.fixture: compiler leaf draining" "$LOG"
grep -c "KEEP dead-owner" "$LOG" || true
"""
            result = self.run_guard(script)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["status=5", "1", "0"])

    def test_held_launch_wakes_on_a_release_not_on_a_poll(self):
        if shutil.which("inotifywait") is None:
            self.skipTest("inotifywait is not installed")
        result = self.run_guard(r"""
MEMORY_CLAIM_BYTES=$((2 * GIB)); WAKE_TIMEOUT=60; POLL_SECONDS=0
printf '%s\n' "$((10 * GIB)) $((10 * GIB)) $((100 * GIB)) $((11 * GIB)) -1 $((175 * GIB))" > "$ADMISSION_SUMMARY"
( sleep 1; printf '%s\n' "$((10 * GIB)) $((10 * GIB)) $((100 * GIB)) $((11 * GIB)) -1 $((175 * GIB))" > "$ADMISSION_SUMMARY.tmp"; mv "$ADMISSION_SUMMARY.tmp" "$ADMISSION_SUMMARY"
  sleep 1; printf '%s\n' "$((5 * GIB)) $((5 * GIB)) $((100 * GIB)) $((11 * GIB)) -1 $((175 * GIB))" > "$ADMISSION_SUMMARY.tmp"; mv "$ADMISSION_SUMMARY.tmp" "$ADMISSION_SUMMARY" ) &
started=$SECONDS
wait_for_admission_change
echo $(( SECONDS - started ))
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        # The first change still leaves no room; the second release does.
        self.assertIn(int(result.stdout.split()[-1]), (1, 2, 3))

    def test_queued_admission_attempt_leaves_the_gate_mutex_free(self):
        # On 2026-11-12 about 100 held launches queued on the gate mutex, which
        # was held 97 % of the time; releases and marks waited minutes behind them.
        result = self.run_guard(r"""
hold_reason() { :; }
compiler_admission_reason() { :; }
module_memory_admission_reason() { :; }
recover_stale_reservations() { :; }
memory() { echo $((256*GIB)) 0 $((200*GIB)); }
# Another attempt holds the queue; this shell must not inherit its lock.
flock "$ADMISSION_QUEUE" -c "touch '$STATE_DIR/queued'; sleep 1.5" & holder=$!
while [ ! -e "$STATE_DIR/queued" ]; do sleep 0.05; done
marker=$(reserve_coqc $$) || exit 11
( confirm_coqc "$marker" ) & attempt=$!
sleep 0.5
( exec 7>>"$GATE_MUTEX"; flock -n 7 ) && echo mutex-free || echo mutex-taken
[ -f "$marker" ] && echo admitted-past-queue || echo queued
wait "$holder"
wait "$attempt" || exit 12
[ -f "$marker" ] && echo admitted
""", ZESU_IN_BATCH="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["mutex-free", "queued", "admitted"])

    def test_slot_refusal_runs_no_stale_ledger_recovery(self):
        result = self.run_guard(r"""
hold_reason() { :; }
compiler_admission_reason() { echo "coqc 31 with 17 reservations machine-wide"; }
recover_stale_reservations() { echo recovery; }
module_memory_admission_reason() { echo ledger; }
wait_for_admission_change() { echo "held ${2:-slots}"; exit 0; }
marker=$(reserve_coqc $$) || exit 11
confirm_coqc "$marker"
""", ZESU_IN_BATCH="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["held", "slots"])

    def test_ledger_refused_launch_waits_for_room_not_for_a_release(self):
        if shutil.which("inotifywait") is None:
            self.skipTest("inotifywait is not installed")
        result = self.run_guard(r"""
MEMORY_CLAIM_BYTES=$((2 * GIB)); LEDGER_RECHECK=60
publish() { printf '%s\n' "$1" > "$ADMISSION_SUMMARY.tmp"; mv "$ADMISSION_SUMMARY.tmp" "$ADMISSION_SUMMARY"; }
# Bookings are full and live memory is above half the slice.
publish "$((300 * GIB)) $((200 * GIB)) $((50 * GIB)) $((155 * GIB)) $((120 * GIB)) $((175 * GIB))"
stamp=$(cat "$ADMISSION_WAKE" 2>/dev/null)
( sleep 1; wake_admissions
  sleep 1; publish "$((300 * GIB)) $((200 * GIB)) $((50 * GIB)) $((155 * GIB)) $((120 * GIB)) $((175 * GIB))"
  sleep 1; touch "$STATE_DIR/room"; publish "$((300 * GIB)) $((200 * GIB)) $((50 * GIB)) $((155 * GIB)) $((80 * GIB)) $((175 * GIB))" ) &
wait_for_admission_change "$stamp" "$SECONDS"
[ -e "$STATE_DIR/room" ] && echo room || echo early
wait
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["room"])

    def test_aged_ledger_waiter_may_fill_live_memory_to_the_slice_cap(self):
        result = self.run_guard(r"""
MEMORY_CLAIM_BYTES=$((2 * GIB))
printf '%s\n' "$((300 * GIB)) $((200 * GIB)) $((50 * GIB)) $((155 * GIB)) $((120 * GIB)) $((175 * GIB))" > "$ADMISSION_SUMMARY"
admission_plausible && echo room || echo full
admission_plausible senior && echo room || echo full
# A fresh slice sample replaces the summary's live figure.
mkdir -p "$WORKLOAD_SLICE_CGROUP"
printf 'anon %s\nfile 0\n' "$((160 * GIB))" > "$WORKLOAD_SLICE_CGROUP/memory.stat"
admission_plausible senior && echo room || echo full
printf 'anon %s\nfile 0\n' "$((10 * GIB))" > "$WORKLOAD_SLICE_CGROUP/memory.stat"
admission_plausible && echo room || echo full
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.split(), ["full", "room", "full", "room"])

    def test_gate_does_not_wait_for_unadmitted_probe_request(self):
        result = self.run_guard(r"""
marker="$COQC_RESERVATIONS/$$.probe"
printf 'pending\nwriter=\naggregate=\n' > "$marker"
printf 'state=wanted holder=fixture pid=%s start=x\n' "$$" > "$GATE_LOCK"
live_scopes() { :; }
live_launches() { :; }
# Any sleep means the gate queued behind the unstarted request.
sleep() { echo unexpected-gate-wait >&2; exit 91; }
lock_hold $$ || exit 92
grep -q '^state=held ' "$GATE_LOCK" || exit 93
[ -f "$marker" ] || exit 94
# The old request must still respect the gate when it tries to confirm.
confirm_coqc "$marker"; status=$?
[ "$status" = 3 ] || exit 95
[ ! -f "$marker" ] || exit 96
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("confirmation refused by gate lock", result.stderr)
        self.assertNotIn("unexpected-gate-wait", result.stderr)

    def test_gate_still_waits_for_confirmed_and_running_launches(self):
        for state in ("confirmed", "123"):
            with self.subTest(state=state):
                result = self.run_guard(r"""
marker="$COQC_RESERVATIONS/$$.probe"
printf '%s\nwriter=\naggregate=\n' "$TEST_RESERVATION_STATE" > "$marker"
printf 'state=wanted holder=fixture pid=%s start=x\n' "$$" > "$GATE_LOCK"
live_scopes() { :; }
live_launches() { :; }
# Keep the fake compiler present without reading any process environment.
live_reservations() {
  [ ! -f "$COQC_RESERVATIONS/$$.probe" ] || echo "$COQC_RESERVATIONS/$$.probe"
}
sleep() {
  grep -q '^state=wanted ' "$GATE_LOCK" || exit 91
  echo waited-for-admitted-launch
  rm "$marker"
}
lock_hold $$ || exit 92
grep -q '^state=held ' "$GATE_LOCK"
""", TEST_RESERVATION_STATE=state)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "waited-for-admitted-launch")

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

    def test_held_launch_starts_within_5_s_after_a_release(self):
        if shutil.which("inotifywait") is None:
            self.skipTest("inotifywait is not installed")
        result = self.run_guard(r"""
hold_reason() { :; }
compiler_pids() { :; }
first=$(reserve_coqc $$) || exit 10
confirm_coqc "$first" || exit 11
held() {
  local owner=$BASHPID second
  second=$(reserve_coqc "$owner") || exit 12
  confirm_coqc "$second" || exit 13
  date +%s%N > "$STATE_DIR/admitted"
  release_coqc "$second"
}
held & waiter=$!
sleep 2
[ ! -e "$STATE_DIR/admitted" ] || exit 14
date +%s%N > "$STATE_DIR/released"
release_coqc "$first"
wait "$waiter" || exit 15
echo $(( ($(cat "$STATE_DIR/admitted") - $(cat "$STATE_DIR/released")) / 1000000 ))
""", ZESU_MAX_COQC="1", ZESU_IN_BATCH="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        # The release wakes the held launch; a 30 s wait round would fail this.
        self.assertLess(int(result.stdout.split()[-1]), 5000)

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

    def test_unmarked_reservation_does_not_scan_its_owner(self):
        result = self.run_guard(r"""
mkdir -p "$STATE_DIR/proc/123/task/123"
printf 'coqc\n' > "$STATE_DIR/proc/123/comm"
printf '123\n' > "$STATE_DIR/proc/123/task/123/children"
PROC_ROOT="$STATE_DIR/proc"
compiler_process() { return 0; }
printf 'confirmed\nwriter=\n' > "$STATE_DIR/123.token"
if reservation_compiler "$STATE_DIR/123.token"; then exit 1; fi
printf '123\nwriter=\n' > "$STATE_DIR/123.token"
reservation_compiler "$STATE_DIR/123.token"
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "123")

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
