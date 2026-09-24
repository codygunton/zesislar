#!/usr/bin/env bash
# One project gate, alone, inside the batch scope.
#
# Plan section 4 rule 4: a gate never shares the machine with a probe,
# replay or benchmark batch, and never two gates at once, across every
# agent. The gate takes /tmp/zesu-gate.lock (holder, PID, start); every
# guard holds its launches while the lock is live, and the gate waits for
# the `coqc` already running to drain before it starts. Rule 1: it runs
# inside a systemd scope with a hard memory cap. Jobs come from the
# guard's `gate-jobs`: 48 for check-fast, 24 for check-iris.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
guard=tools/resource_guard.sh
gate_lock=${ZESU_GATE_LOCK:-/tmp/zesu-gate.lock}
target=${1:-check-iris}
log=${2:-_build/agents/infra/gate-$target.log}

live=$(systemctl --user list-units --type=scope --state=active --plain \
  --no-legend 'zesudet-*' 2>/dev/null | wc -l)
if [ "$live" -gt 0 ]; then
  echo "refusing: $live job scopes are alive; gates run alone" >&2
  systemctl --user list-units --type=scope --state=active --plain \
    --no-legend 'zesudet-*' >&2
  exit 3
fi

# The checkers run unconditionally, before any step Dune can satisfy from
# its cache. A cached `check-fast` reported success while a hygiene
# violation stood for two commits: a gate the cache answers is not a gate.
# Every report names this run.
echo "uncached checks: hygiene, parity, spec shapes, evidence tests"
python3 tools/machine_config.py --check
python3 -m unittest discover -s tools -p 'test_*.py' 2>&1 | tail -1
PYTHONPATH=ZesuSsz/Evidence python3 -m unittest discover \
  -s ZesuSsz/Evidence -p 'test_*.py' 2>&1 | tail -1
python3 ZesuSsz/Evidence/check_parity.py
python3 ZesuSsz/Evidence/check_proof_hygiene.py
python3 ZesuSsz/Evidence/check_spec_shapes.py
bash ZesuSsz/Evidence/check_write_success_decoder.sh
echo "uncached checks passed"

# The lock is held from here to exit. `run_locked` would hold it too, but
# the drain below must run inside it.
$guard lock-status >/dev/null
if ! ( set -C; printf 'holder=%s pid=%s start=%s\n' \
         "${COORD_AGENT:-$USER}:gate-$target:$root" $$ "$(date -Is)" \
         > "$gate_lock" ) 2>/dev/null; then
  echo "refusing: a gate holds $gate_lock: $(cat "$gate_lock")" >&2
  exit 3
fi
release() {
  grep -q "pid=$$ " "$gate_lock" 2>/dev/null && rm -f "$gate_lock"
  kill "${watcher:-}" 2>/dev/null || true
}
trap release EXIT
echo "gate lock: $(cat "$gate_lock")"

# Other agents' guards now hold; wait for their running `coqc` to finish.
drain=${ZESU_GATE_DRAIN_SECONDS:-1800}
floor=${ZESU_GATE_DRAIN_COQC:-0}
waited=0
while (( $(pgrep -c -x coqc || true) > floor )) && (( waited < drain )); do
  sleep 10; waited=$(( waited + 10 ))
done
echo "drain: waited $waited s; coqc machine-wide $(pgrep -c -x coqc || true)"

jobs=$($guard gate-jobs "$target")
slots=$(python3 tools/det/coqc_slots.py "$root" "$jobs" --drain-floor "$floor") || exit 3
read -r jobs own other <<< "$slots"
if (( jobs < 1 )); then
  echo "refusing: no coqc slot remains after drain" >&2
  exit 3
fi
$guard reset-peak
setsid nohup $guard watch >/dev/null 2>&1 &
watcher=$!
started=$(date -Is)

echo "gate $target with $jobs jobs; $($guard report)"
mkdir -p "$(dirname "$log")"
set +e
setsid env ZESU_GUARD=0 ZESU_IN_GATE=1 ZESU_IO=gate ZESU_BATCH_LIMIT=120G $guard batch "gate-${target}" -- \
  make "$target" AGENT_BUILD_DIR="$root/_build/agents/infra" FAST_JOBS="$jobs" \
  AGENT_JOBS="$jobs" > "$log" 2>&1 &
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
  if ! slots=$(python3 tools/det/coqc_slots.py "$root" "$jobs"); then
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
