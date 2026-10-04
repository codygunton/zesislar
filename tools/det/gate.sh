#!/usr/bin/env bash
# Gates exclude new ordinary batches while named writers continue.
# The wanted lock waits for ordinary scopes and reservations to finish.
# The compiler drain excludes registered writers. Their 16 slots remain
# reserved. Each writer uses at most two compilers. Each gate uses 24 jobs
# inside its existing 120 GiB scope. The machine cap stays at 48.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
build_dir="$root/_build/agents/infra"
guard=${ZESU_RESOURCE_GUARD:-tools/resource_guard.sh}
reservations="${ZESU_GUARD_STATE:-${XDG_RUNTIME_DIR:-/tmp}/zesu-guard}/coqc-reservations"
target=${1:-check-iris}
log=${2:-_build/agents/infra/gate-$target.log}

# The lock is wanted from here to exit: no new batch starts behind it.
$guard lock-status >/dev/null
$guard lock-want $$ "${COORD_AGENT:-$USER}:gate-$target:$root" || exit $?
release() {
  $guard lock-release $$
  kill "${watcher:-}" 2>/dev/null || true
}
trap release EXIT
echo "gate lock: $($guard lock-status)"

# The checkers run unconditionally, before any step Dune can satisfy from
# its cache. A cached `check-fast` reported success while a hygiene
# violation stood for two commits: a gate the cache answers is not a gate.
# Every report names this run.
echo "uncached checks: hygiene, spec shapes, evidence tests"
python3 tools/machine_config.py --check
python3 -m unittest discover -s tools -p 'test_*.py' 2>&1 | tail -1
PYTHONPATH=ZesuSsz/Evidence python3 -m unittest discover \
  -s ZesuSsz/Evidence -p 'test_*.py' 2>&1 | tail -1
python3 ZesuSsz/Evidence/check_proof_hygiene.py
python3 ZesuSsz/Evidence/check_spec_shapes.py
echo "uncached checks passed"
# The executable decoder check runs uncached through check-evidence-tools
# inside the aggregate below. It can start compiler jobs.

# Running arms and batches complete; then the lock is held.
$guard lock-hold $$ || exit $?
echo "gate lock: $($guard lock-status)"

# Ordinary guards now hold; wait for nonwriter compilers to finish
# and for memory to fall below the guard's launch line (150 GiB used).
drain=${ZESU_GATE_DRAIN_SECONDS:-1800}
floor=0
launch=$(( ${ZESU_LAUNCH_GIB:-150} * 1073741824 ))
used() { free -b | awk '/^Mem:/ {printf "%.0f", $2 - $7}'; }
waited=0
compiler_count() {
  local count
  count=$($guard coqc-count nonwriter) || {
    echo "refusing: compiler snapshot failed during gate drain" >&2
    return 3
  }
  if ! [[ "$count" =~ ^[0-9]+$ ]]; then
    echo "refusing: invalid compiler count during gate drain" >&2
    return 3
  fi
  echo "$count"
}
while :; do
  coqc=$(compiler_count) || exit 3
  memory=$(used)
  if (( (coqc <= floor && memory < launch) || waited >= drain )); then break; fi
  sleep 10; waited=$(( waited + 10 ))
done
echo "drain: waited $waited s; coqc nonwriter $coqc; used $(( memory / 1073741824 )) GiB"
if (( coqc > floor || memory >= launch )); then
  echo "refusing: gate drain timed out with $coqc coqc and $(( memory / 1073741824 )) GiB used" >&2
  exit 3
fi

jobs=$($guard gate-jobs "$target")
slots=$(python3 tools/det/coqc_slots.py "$root" "$jobs" --own-build-dir "$build_dir" --proc "${ZESU_PROC_ROOT:-/proc}" --writer-reservations "$reservations" --drain-floor "$floor") || exit 3
read -r jobs own other <<< "$slots"
if (( jobs < 1 )); then
  echo "refusing: no coqc slot remains after drain" >&2
  exit 3
fi
$guard reset-peak
setsid nohup $guard watch >/dev/null 2>&1 &
watcher=$!
started=$(date -Is)

gate_report=$($guard report) || exit 3
echo "gate $target with $jobs jobs; $gate_report"
mkdir -p "$(dirname "$log")"
set +e
setsid env ZESU_GUARD=0 ZESU_IN_GATE=1 ZESU_IO=gate ZESU_BATCH_LIMIT=120G $guard batch "gate-${target}" -- \
  make "$target" AGENT_BUILD_DIR="$build_dir" FAST_JOBS="$jobs" \
  AGENT_JOBS="$jobs" GUARD="$guard" > "$log" 2>&1 &
gate_pid=$!
status=0
poll=${ZESU_GATE_CAP_POLL_SECONDS:-30}
gate_running() {
  local state
  state=$(ps -o stat= -p "$gate_pid" 2>/dev/null) || return 1
  [[ -n "$state" && "$state" != Z* ]]
}
stop_gate() {
  kill -- "-$gate_pid" 2>/dev/null || true
  systemctl --user list-units --type=scope --state=active --plain \
    --no-legend "${ZESU_SCOPE_PREFIX:-zesudet}-batch-gate-${target}-*" 2>/dev/null |
    awk '{print $1}' | while IFS= read -r unit; do
      systemctl --user stop "$unit" >/dev/null 2>&1 || true
    done
}
while gate_running; do
  sleep "$poll"
  gate_running || break
  if ! slots=$(python3 tools/det/coqc_slots.py "$root" "$jobs" --own-build-dir "$build_dir" --proc "${ZESU_PROC_ROOT:-/proc}" --writer-reservations "$reservations"); then
    echo "gate stopped: coqc slot check failed" >&2
    stop_gate
    status=3
    break
  fi
  read -r available own other <<< "$slots"
  if (( available < jobs )); then
    echo "gate stopped: width $jobs exceeds $available slots with $other other coqc" >&2
    stop_gate
    status=3
    break
  fi
done
wait "$gate_pid"
gate_status=$?
if (( status == 0 )); then status=$gate_status; fi
set -e
echo "gate $target exit $status; $(grep -c 'Timeout!' "$log" || true) Timeout!; batch peak $($guard peak) GiB"
$guard window --since "$started" || true
exit $status
