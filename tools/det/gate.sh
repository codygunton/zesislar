#!/usr/bin/env bash
# One project gate, alone, inside the batch scope.
#
# Plan section 4 rule 4: a gate never shares the machine with a probe,
# replay or benchmark batch, and never two gates at once, across every
# agent. A gate has priority over new batches (amended 2026-09-24): it
# takes /tmp/zesu-gate.lock in the `wanted` state first, so every guard
# starts no new arm, batch, or probe; a running arm completes, the gate
# waits for its job scopes, marks the lock `held`, and waits for the
# `coqc` still running to drain before it starts. Rule 1: it runs
# inside a 120 GiB systemd scope (ZESU_IO=gate), so 48 GiB of the machine
# stay free for other users. Jobs come from the guard's `gate-jobs`: 48
# for check-fast, 24 for check-iris.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
guard=tools/resource_guard.sh
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

# Running arms and batches complete; then the lock is held.
$guard lock-hold $$ || exit $?
echo "gate lock: $($guard lock-status)"

# Other agents' guards now hold; wait for their running `coqc` to finish
# and for memory to fall below the guard's launch line (150 GiB used).
drain=${ZESU_GATE_DRAIN_SECONDS:-1800}
floor=0
launch=$(( ${ZESU_LAUNCH_GIB:-150} * 1073741824 ))
used() { free -b | awk '/^Mem:/ {printf "%.0f", $2 - $7}'; }
waited=0
while { (( $(pgrep -c -x coqc || true) > floor )) || (( $(used) >= launch )); } \
      && (( waited < drain )); do
  sleep 10; waited=$(( waited + 10 ))
done
coqc=$(pgrep -c -x coqc || true)
memory=$(used)
echo "drain: waited $waited s; coqc machine-wide $coqc; used $(( memory / 1073741824 )) GiB"
if (( coqc > floor || memory >= launch )); then
  echo "refusing: gate drain timed out with $coqc coqc and $(( memory / 1073741824 )) GiB used" >&2
  exit 3
fi

jobs=$($guard gate-jobs "$target")
$guard reset-peak
setsid nohup $guard watch >/dev/null 2>&1 &
watcher=$!
started=$(date -Is)

echo "gate $target with $jobs jobs; $($guard report)"
mkdir -p "$(dirname "$log")"
set +e
ZESU_GUARD=0 ZESU_IN_GATE=1 ZESU_IO=gate ZESU_BATCH_LIMIT=120G $guard batch "gate-${target}" -- \
  make "$target" AGENT_BUILD_DIR="$root/_build/agents/infra" FAST_JOBS="$jobs" \
  AGENT_JOBS="$jobs" > "$log" 2>&1
status=$?
set -e
echo "gate $target exit $status; $(grep -c 'Timeout!' "$log" || true) Timeout!; batch peak $($guard peak) GiB"
$guard window --since "$started" || true
exit $status
