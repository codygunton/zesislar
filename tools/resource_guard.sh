#!/usr/bin/env bash
# Resource guard for the determinism agent's batches.
#
# The machine has 251 GiB of RAM and 64 cores. The module limit is 6 GiB, so
# 48 concurrent jobs is 288 GiB: threads are a ceiling, memory is the binding
# limit. On 2026-09-20 a 48-job gate took the server out of memory and it
# rebooted. Nothing this agent runs in a batch starts outside this guard.
#
# Subcommands:
#   jobs                 the concurrency memory allows right now
#   wait                 block until it is safe to start one more job
#   watch                the polling loop; kills the youngest scope at 90 %
#   scope NAME -- CMD    run CMD in its own 6 GiB scope, registered
#   batch NAME -- CMD    run CMD in the batch scope, 200 GiB, swap off
#   report               one line of memory state, for a report
#
# Every threshold is a percentage of total memory, as the plan states them:
# launch below 70, hold at 80, kill the youngest job scope at 90.

set -uo pipefail

# The hard per-job cap: what one `coqc` scope may use before the kernel
# kills it. This is the module limit and does not change.
MODULE_LIMIT_GIB=${ZESU_MODULE_LIMIT_GIB:-6}
# What a job actually costs, which is what the job count should be sized
# against. Measured 2026-09-20: a clean `check-iris` at 25 jobs peaks at
# 75 GiB, so 3.0 GiB per job. 4 GiB carries margin over that.
JOB_GIB=${ZESU_JOB_GIB:-4}
BATCH_LIMIT=${ZESU_BATCH_LIMIT:-200G}
MAX_JOBS=${ZESU_MAX_JOBS:-48}
LAUNCH_PERCENT=${ZESU_LAUNCH_PERCENT:-70}
HOLD_PERCENT=${ZESU_HOLD_PERCENT:-80}
KILL_PERCENT=${ZESU_KILL_PERCENT:-90}
MAX_COQC=${ZESU_MAX_COQC:-48}
MAX_LOAD=${ZESU_MAX_LOAD:-80}
POLL_SECONDS=${ZESU_GUARD_POLL:-5}
SCOPE_PREFIX=${ZESU_SCOPE_PREFIX:-zesudet}
STATE_DIR=${ZESU_GUARD_STATE:-${XDG_RUNTIME_DIR:-/tmp}/zesu-guard}
REGISTRY="$STATE_DIR/scopes"
PEAK="$STATE_DIR/peak"
LOG="$STATE_DIR/guard.log"

mkdir -p "$STATE_DIR"
touch "$REGISTRY" "$LOG" "$PEAK"

GIB=$((1024 * 1024 * 1024))

note() { printf '%s %s\n' "$(date -Is)" "$*" >> "$LOG"; }

memory() { free -b | awk '/^Mem:/ {print $2, $3, $7}'; }

used_percent() {
  local total used
  read -r total used _ < <(memory)
  (( total > 0 )) || { echo 0; return; }
  echo $(( 100 * used / total ))
}

# `pgrep -c` prints 0 and exits non-zero when nothing matches, so a
# `|| echo 0` fallback would print the count twice.
coqc_count() { local n; n=$(pgrep -c coqc 2>/dev/null); echo "${n:-0}"; }

load_one() { awk '{printf "%d", $1}' /proc/loadavg; }

# jobs = min(MAX_JOBS, floor(0.8 * MemAvailable / module limit)), at least 1.
guard_jobs() {
  local total used available limit
  read -r total used available < <(memory)
  limit=$(( (available * 8 / 10) / (JOB_GIB * GIB) ))
  (( limit < 1 )) && limit=1
  (( limit > MAX_JOBS )) && limit=$MAX_JOBS
  echo "$limit"
}

# A gate is one cgroup running many `coqc` that Dune starts itself, so the
# kernel cannot kill one job inside it: it kills the gate. The job count
# must therefore fit the batch cap with margin, not just the machine.
# Measured 2026-09-20: with a rule that opened an unbounded search, 32
# jobs reached the 200 GiB cap and the gate was killed at a machine peak
# of 209 GiB; a clean gate at 25 jobs peaks at 75 GiB.
#
# A gate also has a ceiling that memory does not see. On 2026-09-22
# `check-iris` at 37 jobs failed with `Error: Timeout!` on
# `WriteSuccessExactByteListsPublicResources.v` and
# `WriteSuccessExactTailRawLoad.v`, and passed on the identical tree
# sixteen minutes later; both modules compile alone in 24.3 s and 10.5 s.
# A Coq `timeout` is wall clock, this automation wraps its own tactics in
# one, and 37 concurrent `coqc` processes spend those budgets on memory
# traffic. Thirty-six spinning processes at load 31 do not reproduce it,
# so the resource is bandwidth, which the memory formula cannot count.
# Lead's ruling 2026-09-22: gates run alone at 24 jobs, the timeouts stay
# as they are, and a red gate is re-run once before it is believed.
GATE_MAX_JOBS=${ZESU_GATE_MAX_JOBS:-24}

gate_jobs() {
  local cap fits allowed
  cap=${BATCH_LIMIT%G}
  fits=$(( (cap * 3 / 4) / JOB_GIB ))
  allowed=$(guard_jobs)
  (( fits < allowed )) && allowed=$fits
  (( GATE_MAX_JOBS < allowed )) && allowed=$GATE_MAX_JOBS
  (( allowed < 1 )) && allowed=1
  echo "$allowed"
}

live_scopes() {
  systemctl --user list-units --type=scope --state=active --plain --no-legend \
    "${SCOPE_PREFIX}-*" 2>/dev/null | awk '{print $1}'
}

# The youngest scope is the last one this agent registered that is still
# alive, so the kill lands on the job that has run least, not on a batch
# that is nearly done.
youngest_scope() {
  local unit
  while IFS= read -r unit; do
    [ -n "$unit" ] || continue
    systemctl --user is-active --quiet "$unit" && echo "$unit"
  done < <(tac "$REGISTRY") | head -1
}

kill_youngest() {
  local unit
  unit=$(youngest_scope)
  if [ -n "$unit" ]; then
    note "KILL $unit at $(used_percent)% used"
    systemctl --user kill --signal=SIGKILL "$unit" 2>/dev/null
    systemctl --user stop "$unit" 2>/dev/null
    echo "$unit"
  fi
}

guard_wait() {
  local percent coqc load
  while :; do
    percent=$(used_percent); coqc=$(coqc_count); load=$(load_one)
    if (( percent >= KILL_PERCENT )); then
      kill_youngest > /dev/null
    elif (( percent < LAUNCH_PERCENT )) && (( coqc <= MAX_COQC )) \
         && (( load < MAX_LOAD )); then
      return 0
    fi
    sleep "$POLL_SECONDS"
  done
}

# The watch also records the high-water mark of used memory, which is the
# batch peak every report has to carry.
record_peak() {
  local used before
  read -r _ used _ < <(memory)
  before=$(cat "$PEAK" 2>/dev/null); before=${before:-0}
  (( used > before )) && echo "$used" > "$PEAK"
}

guard_watch() {
  local percent
  note "watch start: total $(free -g | awk '/^Mem:/{print $2}') GiB"
  while :; do
    percent=$(used_percent)
    record_peak
    (( percent >= KILL_PERCENT )) && kill_youngest > /dev/null
    sleep "$POLL_SECONDS"
  done
}

run_scope() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  local unit="${SCOPE_PREFIX}-${name}-$$-${RANDOM}"
  echo "$unit.scope" >> "$REGISTRY"
  exec systemd-run --user --scope --quiet --unit="$unit" \
    -p "MemoryMax=${MODULE_LIMIT_GIB}G" -p MemorySwapMax=0 -- "$@"
}

run_batch() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  # One batch scope is enough. A gate calls `make`, and `make` wraps its
  # own build in a batch too; nesting a scope inside a scope either fails
  # or halves the cap for no gain.
  if [ -n "${ZESU_IN_BATCH:-}" ]; then
    exec "$@"
  fi
  local unit="${SCOPE_PREFIX}-batch-${name}-$$"
  echo "$unit.scope" >> "$REGISTRY"
  exec env ZESU_IN_BATCH=1 systemd-run --user --scope --quiet --unit="$unit" \
    -p "MemoryMax=${BATCH_LIMIT}" -p MemorySwapMax=0 -- "$@"
}

report() {
  local total used available
  read -r total used available < <(memory)
  local peak; peak=$(cat "$PEAK" 2>/dev/null); peak=${peak:-0}
  printf 'memory used %d of %d GiB (%d%%), available %d GiB, batch peak %d GiB; coqc %s; load %s; jobs %s; guard kills %s\n' \
    $(( used / GIB )) $(( total / GIB )) "$(used_percent)" \
    $(( available / GIB )) $(( peak / GIB )) "$(coqc_count)" \
    "$(awk '{print $1}' /proc/loadavg)" \
    "$(guard_jobs)" "$(grep -c ' KILL ' "$LOG" 2>/dev/null | head -1)"
}

case "${1:-report}" in
  jobs)   guard_jobs ;;
  gate-jobs) gate_jobs ;;
  reset-peak) echo 0 > "$PEAK" ;;
  peak)   awk '{printf "%d", $1 / 1073741824}' "$PEAK" 2>/dev/null; echo ;;
  wait)   guard_wait ;;
  watch)  guard_watch ;;
  scope)  shift; run_scope "$@" ;;
  batch)  shift; run_batch "$@" ;;
  report) report ;;
  *) echo "usage: $0 {jobs|gate-jobs|wait|watch|scope NAME -- CMD|batch NAME -- CMD|report|peak|reset-peak}" >&2; exit 2 ;;
esac
