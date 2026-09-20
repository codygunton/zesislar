#!/usr/bin/env bash
# One project gate, alone, inside the batch scope.
#
# Plan section 4 rule 4: a gate never shares the machine with a probe,
# replay or benchmark batch, and never two gates at once. Rule 1: it runs
# inside a systemd scope with a hard memory cap, so an over-large module
# is killed by the kernel instead of taking the server down. Concurrency
# comes from the guard's `gate-jobs`, which sizes the count to the cap with
# margin: 25 jobs at the 6 GiB module limit is 150 GiB inside a 200 GiB
# scope. 32 jobs was measured to reach the cap and the gate was killed.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
guard=tools/resource_guard.sh
target=${1:-check-iris}
log=${2:-_build/agents/det/gate-$target.log}

live=$(systemctl --user list-units --type=scope --state=active --plain \
  --no-legend 'zesudet-*' 2>/dev/null | wc -l)
if [ "$live" -gt 0 ]; then
  echo "refusing: $live job scopes are alive; gates run alone" >&2
  systemctl --user list-units --type=scope --state=active --plain \
    --no-legend 'zesudet-*' >&2
  exit 3
fi

jobs=$($guard gate-jobs)
$guard reset-peak
setsid nohup $guard watch >/dev/null 2>&1 &
watcher=$!
trap 'kill "$watcher" 2>/dev/null || true' EXIT

echo "gate $target with $jobs jobs; $($guard report)"
mkdir -p "$(dirname "$log")"
ZESU_GUARD=0 $guard batch "gate-${target}" -- nice -n 10 make "$target" \
  AGENT_BUILD_DIR="$root/_build/agents/det" AGENT_JOBS="$jobs" \
  > "$log" 2>&1
status=$?
echo "gate $target exit $status; peak $($guard peak) GiB; $($guard report)"
exit $status
