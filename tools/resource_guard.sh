#!/usr/bin/env bash
# Resource guard for every batch, probe, arm, and gate on this machine.
#
# The machine has 251 GiB of RAM and 64 cores and is shared across agents.
# On 2026-09-20 a 48-job gate at the 6 GiB module limit asked for 288 GiB
# and the server rebooted, so the cgroup fence below stays. Two hours of
# Prometheus data on 2026-09-22 (plan section 4) showed that memory is no
# longer the binding limit: memory used peaked at 114.5 GiB, but load1
# spiked to 400-1,470 with every disk burst from a new arm's build
# directory. The guard therefore also paces launches, runs batch jobs in
# the idle IO class, and holds on load5 and blocked processes.
#
# Subcommands:
#   jobs                 the concurrency a batch may use right now
#   gate-jobs [TARGET]   the concurrency a gate may use: check-fast 48,
#                        check-iris (and any other gate) 24
#   wait                 block until one more job may start
#   watch                the polling loop; kills the youngest scope at 90 %
#   scope NAME -- CMD    run CMD in its own 6 GiB scope, registered
#   batch NAME -- CMD    run CMD in the batch scope, 200 GiB, swap off
#   locked NAME -- CMD   run CMD holding the gate lock
#   lock-status          print the gate lock, removing a stale one
#   report               one line of guard state and Prometheus figures
#   window ARGS          `tools/det/prom.py window ARGS`
#
# A job may start when all of these hold, checked machine-wide:
#   memory used below 70 % of total (the kill stays at 90 %);
#   at most 48 `coqc` processes, counted for every agent, not only ours;
#   load5 at most 80 and at most 16 blocked processes;
#   no gate holds /tmp/zesu-gate.lock;
#   the last launch by any guard is at least half a second old.

set -uo pipefail

# The hard per-job cap: what one `coqc` scope may use before the kernel
# kills it. This is the module limit and does not change.
MODULE_LIMIT_GIB=${ZESU_MODULE_LIMIT_GIB:-6}
# What a job actually costs, which is what the job count should be sized
# against. Measured 2026-09-20: a clean `check-iris` at 25 jobs peaks at
# 75 GiB, so 3.0 GiB per job; on 2026-09-22 batches 48 wide peaked at
# about 74 GiB, so 1.5. At 3 GiB the formula allows 48 whenever 180 GiB
# is available.
JOB_GIB=${ZESU_JOB_GIB:-3}
BATCH_LIMIT=${ZESU_BATCH_LIMIT:-200G}
MAX_JOBS=${ZESU_MAX_JOBS:-48}
LAUNCH_PERCENT=${ZESU_LAUNCH_PERCENT:-70}
HOLD_PERCENT=${ZESU_HOLD_PERCENT:-80}
KILL_PERCENT=${ZESU_KILL_PERCENT:-90}
MAX_COQC=${ZESU_MAX_COQC:-48}
MAX_LOAD=${ZESU_MAX_LOAD:-80}
MAX_BLOCKED=${ZESU_MAX_BLOCKED:-16}
# Two launches per second, shared by every guard of every agent.
RAMP_MS=${ZESU_RAMP_MS:-500}
RAMP_FILE=${ZESU_RAMP_FILE:-/tmp/zesu-guard-ramp}
GATE_LOCK=${ZESU_GATE_LOCK:-/tmp/zesu-gate.lock}
FAST_MAX_JOBS=${ZESU_FAST_MAX_JOBS:-48}
PROM=$(dirname "$0")/det/prom.py
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
# `|| echo 0` fallback would print the count twice. `pgrep` sees every
# user's processes, so this is the machine-wide count the plan asks for.
coqc_count() { local n; n=$(pgrep -c -x coqc 2>/dev/null); echo "${n:-0}"; }

# load5, not load1: the load1 spikes of 2026-09-22 lasted one to five
# minutes and followed disk bursts, and holding on them stalls a batch
# for a burst it did not cause.
load_five() { awk '{printf "%d", $2}' /proc/loadavg; }

blocked_count() { awk '/^procs_blocked/ {print $2}' /proc/stat; }

# --- the gate lock ---------------------------------------------------------
#
# "A gate runs alone" is mechanical across agents: a gate writes its holder,
# PID, and start time to the lock, and every guard holds launches while the
# lock is live. A lock whose PID is dead is removed and reported.

lock_pid() { sed -n 's/.*pid=\([0-9]*\).*/\1/p' "$GATE_LOCK" 2>/dev/null; }

# Prints the live holder, or nothing. Removes a stale lock and says so.
lock_live() {
  [ -e "$GATE_LOCK" ] || return 1
  local pid; pid=$(lock_pid)
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
    cat "$GATE_LOCK"; return 0
  fi
  local text; text=$(cat "$GATE_LOCK" 2>/dev/null)
  rm -f "$GATE_LOCK"
  note "STALE gate lock removed: $text"
  echo "resource guard: stale gate lock removed: $text" >&2
  return 1
}

lock_acquire() {
  local holder=$1 pid=$2 current
  while :; do
    if ( set -C; printf 'holder=%s pid=%s start=%s\n' "$holder" "$pid" \
           "$(date -Is)" > "$GATE_LOCK" ) 2>/dev/null; then
      note "LOCK taken by $holder pid $pid"
      return 0
    fi
    if current=$(lock_live); then
      echo "refusing: a gate holds $GATE_LOCK: $current" >&2
      return 3
    fi
  done
}

lock_release() {
  [ "$(lock_pid)" = "$1" ] && rm -f "$GATE_LOCK" && note "LOCK released by pid $1"
  return 0
}

run_locked() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  # A gate that already holds the lock runs `make`, which comes back here.
  # A benchmark arm's build is batch work, not a gate (ZESU_ARM).
  if [ -n "${ZESU_IN_GATE:-}${ZESU_ARM:-}" ]; then exec "$@"; fi
  lock_acquire "${COORD_AGENT:-$USER}:$name:$PWD" $$ || exit $?
  trap 'lock_release $$' EXIT
  ZESU_IN_GATE=1 "$@"
}

# Two launches per second across all guards: take the ramp file's lock,
# sleep out the rest of the half second since the last launch, stamp it.
ramp() {
  exec 9>>"$RAMP_FILE"
  flock 9
  local last now wait_ms
  last=$(cat "$RAMP_FILE" 2>/dev/null); last=${last:-0}
  now=$(date +%s%3N)
  wait_ms=$(( last + RAMP_MS - now ))
  if (( wait_ms > 0 )); then
    sleep "$(printf '%d.%03d' $(( wait_ms / 1000 )) $(( wait_ms % 1000 )))"
  fi
  date +%s%3N > "$RAMP_FILE"
  flock -u 9
  exec 9>&-
}

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
# traffic. Lead's ruling 2026-09-22: `check-iris` runs alone at 24 jobs,
# the timeouts stay, and a red gate is re-run once before it is believed.
# `check-fast` builds no proof module and runs at 48 (plan section 4).
# The memory formula stays as the ceiling for both.
GATE_MAX_JOBS=${ZESU_GATE_MAX_JOBS:-24}
gate_jobs() {
  local target=${1:-check-iris} cap allowed
  cap=$GATE_MAX_JOBS
  [ "$target" = check-fast ] && cap=$FAST_MAX_JOBS
  allowed=$(guard_jobs)
  (( cap < allowed )) && allowed=$cap
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

# Why the guard would hold a launch now, or nothing. A gate's own jobs
# are not held by its own lock.
hold_reason() {
  local percent coqc load blocked holder
  percent=$(used_percent); coqc=$(coqc_count)
  load=$(load_five); blocked=$(blocked_count)
  if (( percent >= LAUNCH_PERCENT )); then echo "memory ${percent}%"
  elif (( coqc >= MAX_COQC )); then echo "coqc $coqc machine-wide"
  elif (( load > MAX_LOAD )); then echo "load5 $load"
  elif (( blocked > MAX_BLOCKED )); then echo "blocked $blocked"
  elif [ -z "${ZESU_IN_GATE:-}" ] && holder=$(lock_live 2>/dev/null); then
    echo "gate lock: $holder"
  fi
}

# A hold is logged once when it starts and once when it ends, with its
# cause, so a report can name every hold.
guard_wait() {
  local reason held="" since
  while :; do
    (( $(used_percent) >= KILL_PERCENT )) && kill_youngest > /dev/null
    reason=$(hold_reason)
    if [ -z "$reason" ]; then
      [ -n "$held" ] && note "RESUME after $(( $(date +%s) - since )) s: $held"
      ramp
      return 0
    fi
    if [ "$reason" != "$held" ]; then
      note "HOLD $reason"; held=$reason; since=${since:-$(date +%s)}
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
    -p "MemoryMax=${MODULE_LIMIT_GIB}G" -p MemorySwapMax=0 -- \
    $(io_class) "$@"
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
    -p "MemoryMax=${BATCH_LIMIT}" -p MemorySwapMax=0 -- $(io_class) "$@"
}

# Batch work runs in the idle IO class so that populating a build
# directory from the Dune cache cannot saturate the disk. A gate sets
# ZESU_IO=gate: it runs alone and must finish inside its own timeouts.
io_class() {
  if [ "${ZESU_IO:-batch}" = gate ]; then echo "nice -n 10"
  else echo "ionice -c3 nice -n 10"; fi
}

# Guard state from /proc, then the machine figures from Prometheus. The
# Prometheus line is what a report quotes (plan section 4, rule 6).
report() {
  local peak holder
  peak=$(cat "$PEAK" 2>/dev/null); peak=${peak:-0}
  holder=$(lock_live 2>/dev/null) || holder=none
  printf 'guard: coqc %s machine-wide; load5 %s; blocked %s; jobs %s; batch peak %d GiB; gate lock %s; holds %s; guard kills %s\n' \
    "$(coqc_count)" "$(load_five)" "$(blocked_count)" "$(guard_jobs)" \
    $(( peak / GIB )) "$holder" \
    "$(grep -c ' HOLD ' "$LOG" 2>/dev/null | head -1)" \
    "$(grep -c ' KILL ' "$LOG" 2>/dev/null | head -1)"
  python3 "$PROM" now || echo "prometheus unavailable; no machine figures"
}

case "${1:-report}" in
  jobs)   guard_jobs ;;
  gate-jobs) gate_jobs "${2:-check-iris}" ;;
  reset-peak) echo 0 > "$PEAK" ;;
  peak)   awk '{printf "%d", $1 / 1073741824}' "$PEAK" 2>/dev/null; echo ;;
  wait)   guard_wait ;;
  watch)  guard_watch ;;
  scope)  shift; run_scope "$@" ;;
  batch)  shift; run_batch "$@" ;;
  locked) shift; run_locked "$@" ;;
  lock-status) lock_live || echo "no gate lock" ;;
  hold)   r=$(hold_reason); echo "${r:-none}" ;;
  window) shift; python3 "$PROM" window "$@" ;;
  report) report ;;
  *) echo "usage: $0 {jobs|gate-jobs [TARGET]|wait|watch|scope NAME -- CMD|batch NAME -- CMD|locked NAME -- CMD|lock-status|hold|report|window ARGS|peak|reset-peak}" >&2; exit 2 ;;
esac
