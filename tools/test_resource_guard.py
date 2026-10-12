"""Check writer admission limits and reservation classes in isolation."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


GUARD = Path(__file__).with_name("resource_guard.sh")
LIBRARY = GUARD.read_text().split("\nprune_scope_registry\n\ncase ", 1)[0]
DISPATCH = "case " + GUARD.read_text().split("\nprune_scope_registry\n\ncase ", 1)[1]


class ResourceGuard(unittest.TestCase):
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
        cases = (({}, 1200),
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
[ "$(guard_jobs)" = 48 ] || exit 93
MEMORY_POLICY=used
available_gib() { echo 180; }
used_gib() { echo 71; }
[ "$(guard_jobs)" = 42 ]
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
available_gib() { echo 26; }
used_gib() { echo 230; }
memory() { echo "0 0 $((26 * GIB))"; }
[ -z "$(memory_hold_reason)" ] || exit 91
if memory_kill_required; then exit 92; fi
JOB_GIB=6
[ "$(guard_jobs)" = 1 ]
""")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_interim_used_memory_policy_is_explicit(self):
        for used, admitted, killed in ((199, True, False), (200, False, False),
                                       (215, False, False), (229, False, False),
                                       (230, False, True)):
            with self.subTest(used=used):
                result = self.run_guard(r"""
used_gib() { echo "$TEST_USED"; }
available_gib() { echo 0; }
[ -n "$(memory_hold_reason)" ] || echo admitted
if memory_kill_required; then echo killed; fi
""", ZESU_MEMORY_POLICY="used", ZESU_LAUNCH_GIB="200",
                                         ZESU_HOLD_GIB="215", ZESU_KILL_GIB="230",
                                         TEST_USED=str(used))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual("admitted" in result.stdout.splitlines(), admitted)
                self.assertEqual("killed" in result.stdout.splitlines(), killed)

    def test_probe_confirmation_requires_84_gib_available(self):
        result = self.run_guard(r"""
available_gib() { echo 83; }
coqc_count() { echo 0; }
compiler_pids() { :; }
load_five() { echo 0; }
blocked_count() { echo 0; }
request=$(reserve_coqc $$)
sleep() { [ ! -e "$request" ] || exit 92; exit 91; }
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
[ "$(hold_reason)" = 'memory available 25 GiB, requires 26 GiB for a 6 GiB job' ] || exit 97
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

    def test_two_probe_slots_are_atomic_across_simultaneous_requests(self):
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
  sleep 0.08
  printf 'end %s\n' "$owner" >> "$STATE_DIR/events"
  release_coqc "$marker"
}
pids=""
for n in 1 2 3 4 5 6; do worker "$n" & pids="$pids $!"; done
for pid in $pids; do wait "$pid" || exit 91; done
cat "$STATE_DIR/events"
[ "$(probe_count)" = 0 ]
""", ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
                                     ZESU_MODULE_LIMIT_GIB="64",
                                     ZESU_PROOF_CPU_LIMIT="unlimited")
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
        self.assertEqual(starts, 6)
        self.assertEqual(peak, 2)
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

    def test_scope_fences_require_six_gib_or_valid_issue10_probe(self):
        cases = (({}, 0), ({"ZESU_MODULE_LIMIT_GIB": "64"}, 2),
                 ({"ZESU_MODULE_LIMIT_GIB": "12"}, 2),
                 ({"ZESU_DIAGNOSTIC_PROBE": "1", "ZESU_PROBE_ISSUE": "10",
                   "ZESU_MODULE_LIMIT_GIB": "64",
                   "ZESU_PROOF_CPU_LIMIT": "unlimited"}, 0))
        for variables, expected in cases:
            with self.subTest(variables=variables):
                result = self.run_guard("validate_probe_scope", **variables)
                self.assertEqual(result.returncode, expected, result.stderr)

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

    def run_guard(self, script, **variables):
        with tempfile.TemporaryDirectory() as directory:
            environment = {key: value for key, value in os.environ.items()
                           if not key.startswith("ZESU_")}
            environment.update(ZESU_GUARD_STATE=directory,
                               ZESU_GATE_LOCK=str(Path(directory) / "gate.lock"),
                               **variables)
            # Legacy fixtures never inspect or trim the shared host cache.
            prefix = "\nhome_free_bytes() { echo 60000000000; }\n"
            return subprocess.run(["bash"], input=LIBRARY + prefix + script,
                                  text=True, capture_output=True, env=environment, timeout=20)

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
