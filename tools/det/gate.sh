#!/usr/bin/env bash
# One project gate, alone, inside the batch scope.
#
# Plan section 4 rule 4: a gate never shares the machine with a probe,
# replay or benchmark batch, and never two gates at once. Rule 1: it runs
# inside a systemd scope with a hard memory cap, so an over-large module
# is killed by the kernel instead of taking the server down. Concurrency
# is fixed at 24 jobs for this buildout. The guard still caps memory.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
guard=tools/resource_guard.sh
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

jobs=24
$guard reset-peak
setsid nohup $guard watch >/dev/null 2>&1 &
watcher=$!
trap 'kill "$watcher" 2>/dev/null || true' EXIT

echo "gate $target with $jobs jobs; $($guard report)"
mkdir -p "$(dirname "$log")"
set +e
ZESU_GUARD=0 $guard batch "gate-${target}" -- nice -n 10 make "$target" \
  AGENT_BUILD_DIR="$root/_build/agents/infra" AGENT_JOBS="$jobs" \
  > "$log" 2>&1
status=$?
set -e
echo "gate $target exit $status; peak $($guard peak) GiB; $($guard report)"
exit $status
