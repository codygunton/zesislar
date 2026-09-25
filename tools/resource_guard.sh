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
#   batch NAME -- CMD    run CMD in the batch scope, 150 GiB (a gate 120), swap off
#   locked NAME -- CMD   run CMD holding the gate lock
#   lock-status          print the gate lock, removing a stale one
#   lock-want PID HOLDER take the lock for a gate script, state wanted
#   lock-hold PID        wait for running job scopes to finish, then mark
#                        the lock held
#   report               one line of guard state and Prometheus figures
#   window ARGS          `tools/det/prom.py window ARGS`
#
# Memory budget (user rule 2026-09-22 21:00): 48 GiB of the 251 stay free
# for other users. In absolute terms, machine-wide used memory: launch
# below 150 GiB, hold at 180, kill the youngest job scope at 200. Fences:
# batch scope 150G, gate scope 120G, each `coqc` 6G, swap off.
#
# A job may start when all of these hold, checked machine-wide:
#   memory used below 150 GiB;
#   at most 48 `coqc` processes, counted for every agent, not only ours;
#   load5 at most 80 and at most 16 blocked processes;
#   no gate holds or wants /tmp/zesu-gate.lock.
# A gate has priority over new batches (plan section 4 item 4, amended
# 2026-09-24): it writes the lock in the `wanted` state before its build,
# and no new arm, batch, scope, or probe starts while the lock exists in
# either state. Jobs inside a running batch go on, so a running arm
# completes; the gate waits for it and then marks the lock `held`.
# While an arm populates its build directory, or while a disk is more than
# 80 % busy, launches also keep a ramp of two per second across guards;
# otherwise they fill the width as slots free up.

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
BATCH_LIMIT=${ZESU_BATCH_LIMIT:-150G}
GATE_LIMIT=${ZESU_GATE_LIMIT:-120G}
MAX_JOBS=${ZESU_MAX_JOBS:-48}
LAUNCH_GIB=${ZESU_LAUNCH_GIB:-150}
HOLD_GIB=${ZESU_HOLD_GIB:-180}
KILL_GIB=${ZESU_KILL_GIB:-200}
DISK_BUSY_PERCENT=${ZESU_DISK_BUSY_PERCENT:-80}
# An arm's build writes a marker `<prefix>.<pid>` while it populates its
# build directory from the Dune cache; the ramp applies while one is live.
POPULATING_PREFIX=${ZESU_POPULATING_PREFIX:-/tmp/zesu-populating}
MAX_COQC=${ZESU_MAX_COQC:-48}
MAX_LOAD=${ZESU_MAX_LOAD:-80}
MAX_BLOCKED=${ZESU_MAX_BLOCKED:-16}
# Two launches per second, shared by every guard of every agent.
RAMP_MS=${ZESU_RAMP_MS:-500}
RAMP_FILE=${ZESU_RAMP_FILE:-/tmp/zesu-guard-ramp}
GATE_LOCK=${ZESU_GATE_LOCK:-/tmp/zesu-gate.lock}
GATE_MUTEX="${GATE_LOCK}.mutex"
FAST_MAX_JOBS=${ZESU_FAST_MAX_JOBS:-48}
PROM=$(dirname "$0")/det/prom.py
POLL_SECONDS=${ZESU_GUARD_POLL:-5}
SCOPE_PREFIX=${ZESU_SCOPE_PREFIX:-zesudet}
STATE_DIR=${ZESU_GUARD_STATE:-${XDG_RUNTIME_DIR:-/tmp}/zesu-guard}
REGISTRY="$STATE_DIR/scopes"
LAUNCHES="$STATE_DIR/launches"
PEAK="$STATE_DIR/peak"
LOG="$STATE_DIR/guard.log"

mkdir -p "$STATE_DIR"
mkdir -p "$LAUNCHES"
touch "$REGISTRY" "$LOG" "$PEAK"

GIB=$((1024 * 1024 * 1024))

note() { printf '%s %s\n' "$(date -Is)" "$*" >> "$LOG"; }

memory() { free -b | awk '/^Mem:/ {print $2, $3, $7}'; }

# Used means total minus available, the figure Prometheus reports
# (`MemTotal - MemAvailable`), so the thresholds and the reports agree.
used_gib() {
  local total available
  read -r total _ available < <(memory)
  echo $(( (total - available) / GIB ))
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
# "A gate runs alone" is mechanical across agents: a gate writes its state,
# holder, PID, and start time to the lock, and every guard holds new
# launches while the lock is live, wanted or held. A lock whose PID is dead
# is removed and reported.

lock_pid() { sed -n 's/.*pid=\([0-9]*\).*/\1/p' "$GATE_LOCK" 2>/dev/null; }

# Prints the live holder, or nothing. Removes a stale lock and says so.
lock_live_unlocked() {
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

lock_live() {
  local status
  exec 7>>"$GATE_MUTEX"
  flock 7
  lock_live_unlocked; status=$?
  flock -u 7
  exec 7>&-
  return "$status"
}

lock_acquire() {
  local holder=$1 pid=$2 current
  while :; do
    exec 7>>"$GATE_MUTEX"
    flock 7
    if ( set -C; printf 'state=wanted holder=%s pid=%s start=%s\n' \
           "$holder" "$pid" "$(date -Is)" > "$GATE_LOCK" ) 2>/dev/null; then
      flock -u 7
      exec 7>&-
      note "LOCK wanted by $holder pid $pid"
      return 0
    fi
    current=$(lock_live_unlocked); local status=$?
    flock -u 7
    exec 7>&-
    if (( status == 0 )); then
      echo "refusing: a gate holds $GATE_LOCK: $current" >&2
      return 3
    fi
  done
}

# wanted -> held, once the running batches have finished. Gives up after
# ZESU_GATE_SCOPE_WAIT seconds (4 h) and releases the lock.
lock_hold() {
  local pid=$1 limit=${ZESU_GATE_SCOPE_WAIT:-14400} start=$SECONDS live
  local noted=""
  # A registered launch can precede its systemd scope. Wait for both.
  while live=$(( $(live_scopes | wc -l) + $(live_launches | wc -l) )); (( live > 0 )); do
    if (( SECONDS - start >= limit )); then
      echo "refusing: $live job scopes or launches still alive after $(( SECONDS - start )) s" >&2
      lock_release "$pid"; return 3
    fi
    [ -z "$noted" ] && note "LOCK wanted: waiting for $live job scopes" && noted=1
    sleep "$POLL_SECONDS"
  done
  local waited=$(( SECONDS - start ))
  [ "$(lock_pid)" = "$pid" ] || return 3
  sed -i 's/^state=wanted /state=held /' "$GATE_LOCK"
  note "LOCK held by pid $pid after $waited s"
}

lock_release() {
  exec 7>>"$GATE_MUTEX"
  flock 7
  if [ "$(lock_pid)" = "$1" ]; then
    rm -f "$GATE_LOCK"
    note "LOCK released by pid $1"
  fi
  flock -u 7
  exec 7>&-
  return 0
}

# A launch registers under the same mutex that creates the wanted lock.
# The gate waits for these registrations as well as active systemd scopes.
admit_launch() {
  local marker holder
  exec 7>>"$GATE_MUTEX"
  flock 7
  if holder=$(lock_live_unlocked 2>/dev/null); then
    flock -u 7
    exec 7>&-
    return 1
  fi
  marker="$LAUNCHES/$$.$RANDOM"
  : > "$marker"
  flock -u 7
  exec 7>&-
  echo "$marker"
}

live_launches() {
  local marker pid
  for marker in "$LAUNCHES"/*; do
    [ -e "$marker" ] || continue
    pid=${marker##*/}; pid=${pid%%.*}
    if kill -0 "$pid" 2>/dev/null; then echo "$marker"
    else rm -f "$marker"; fi
  done
}

run_locked() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  # A gate that already holds the lock runs `make`, which comes back here.
  # A benchmark arm's build is batch work, not a gate (ZESU_ARM).
  if [ -n "${ZESU_IN_GATE:-}${ZESU_ARM:-}" ]; then exec "$@"; fi
  lock_acquire "${COORD_AGENT:-$USER}:$name:$PWD" $$ || exit $?
  trap 'lock_release $$' EXIT
  lock_hold $$ || exit $?
  ZESU_IN_GATE=1 "$@"
}

# The busiest whole disk, in percent, over one second. A fifth of a
# second read 102 % on an idle disk, so the sample is one second, and
# guards share it for two seconds instead of each paying the second.
DISK_CACHE="$STATE_DIR/disk-busy"

disk_sample() {
  awk '$3 ~ /^(nvme[0-9]+n[0-9]+|sd[a-z]+)$/ {print $3, $13}' /proc/diskstats
}

disk_busy() {
  local stamp value first second
  # One guard samples; the others wait on the lock and read its result.
  exec 8>>"$DISK_CACHE.lock"
  flock 8
  read -r stamp value 2>/dev/null < "$DISK_CACHE"
  if [ -z "${stamp:-}" ] || (( $(date +%s) - stamp >= 2 )); then
    first=$(disk_sample); sleep 1; second=$(disk_sample)
    value=$(join <(echo "$first") <(echo "$second") \
      | awk 'BEGIN {m = 0} {u = ($3 - $2) / 10; if (u > m) m = u} END {printf "%d", m}')
    echo "$(date +%s) $value" > "$DISK_CACHE"
  fi
  flock -u 8
  exec 8>&-
  echo "$value"
}

populating() {
  local marker pid
  for marker in "$POPULATING_PREFIX".*; do
    [ -e "$marker" ] || continue
    pid=${marker##*.}
    if kill -0 "$pid" 2>/dev/null; then return 0; fi
    rm -f "$marker"
  done
  return 1
}

# The ramp is for disk bursts only (plan section 4, amended 2026-09-22):
# a permanent ramp held a 48-wide probe batch at 6 to 20 jobs.
ramp_needed() {
  populating && return 0
  (( $(disk_busy) > DISK_BUSY_PERCENT ))
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

# jobs = min(MAX_JOBS, floor((hold line - used) / job size)), at least 1:
# the jobs a batch starts now must fit under the 180 GiB hold, so the
# 48 GiB reserved for other users is never reached by a full batch.
guard_jobs() {
  local limit
  limit=$(( (HOLD_GIB - $(used_gib)) / JOB_GIB ))
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
    note "KILL $unit at $(used_gib) GiB used"
    systemctl --user kill --signal=SIGKILL "$unit" 2>/dev/null
    systemctl --user stop "$unit" 2>/dev/null
    echo "$unit"
  fi
}

# Why the guard would hold a launch now, or nothing. A gate's own jobs
# are not held by its own lock.
hold_reason() {
  local used coqc load blocked holder
  used=$(used_gib); coqc=$(coqc_count)
  load=$(load_five); blocked=$(blocked_count)
  if (( used >= HOLD_GIB )); then echo "memory ${used} GiB, at the ${HOLD_GIB} GiB hold"
  elif (( used >= LAUNCH_GIB )); then echo "memory ${used} GiB, launch line ${LAUNCH_GIB}"
  elif (( coqc >= MAX_COQC )); then echo "coqc $coqc machine-wide"
  elif (( load > MAX_LOAD )); then echo "load5 $load"
  elif (( blocked > MAX_BLOCKED )); then echo "blocked $blocked"
  elif [ -z "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}" ] \
       && holder=$(lock_live 2>/dev/null); then
    echo "gate lock: $holder"
  fi
}

# A hold is logged once when it starts and once when it ends, with its
# cause, so a report can name every hold.
guard_wait() {
  local reason held="" since
  while :; do
    (( $(used_gib) >= KILL_GIB )) && kill_youngest > /dev/null
    reason=$(hold_reason)
    if [ -z "$reason" ]; then
      [ -n "$held" ] && note "RESUME after $(( $(date +%s) - since )) s: $held"
      ramp_needed && ramp
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
  local total available used before
  read -r total _ available < <(memory)
  used=$(( total - available ))
  before=$(cat "$PEAK" 2>/dev/null); before=${before:-0}
  (( used > before )) && echo "$used" > "$PEAK"
}

guard_watch() {
  local used held=""
  note "watch start: total $(free -g | awk '/^Mem:/{print $2}') GiB"
  while :; do
    used=$(used_gib)
    record_peak
    if (( used >= HOLD_GIB )) && [ -z "$held" ]; then
      note "HOLD memory $used GiB at the $HOLD_GIB GiB hold"; held=1
    elif (( used < LAUNCH_GIB )); then held=""; fi
    (( used >= KILL_GIB )) && kill_youngest > /dev/null
    sleep "$POLL_SECONDS"
  done
}

# A new scope or batch waits while a gate wants or holds the lock. Work
# inside a running batch or gate is not new and goes on.
wait_for_gate() {
  [ -n "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}" ] && return 0
  local holder held=""
  while holder=$(lock_live 2>/dev/null); do
    [ -z "$held" ] && note "HOLD launch for gate: $holder" && held=1
    sleep "$POLL_SECONDS"
  done
  [ -n "$held" ] && note "RESUME launch after gate"
  return 0
}

# A direct `scope` or `batch` call obeys the launch line too; `wait`
# adds the other checks for runners that pace their own jobs.
wait_for_memory_budget() {
  local used held=""
  while :; do
    used=$(used_gib)
    (( used >= KILL_GIB )) && kill_youngest > /dev/null
    if (( used < LAUNCH_GIB )); then
      [ -n "$held" ] && note "RESUME memory launch at $used GiB"
      return 0
    fi
    [ -z "$held" ] && note "HOLD memory launch at $used GiB" && held=1
    sleep "$POLL_SECONDS"
  done
}

run_scope() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  wait_for_gate
  wait_for_memory_budget
  local marker="" status
  if [ -z "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}" ]; then
    until marker=$(admit_launch); do wait_for_gate; done
  fi
  local unit="${SCOPE_PREFIX}-${name}-$$-${RANDOM}"
  echo "$unit.scope" >> "$REGISTRY"
  systemd-run --user --scope --quiet --unit="$unit" \
    -p "MemoryMax=${MODULE_LIMIT_GIB}G" -p MemorySwapMax=0 -- \
    $(io_class) "$@"
  status=$?
  [ -z "$marker" ] || rm -f "$marker"
  return "$status"
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
  wait_for_gate
  wait_for_memory_budget
  local marker="" status
  if [ -z "${ZESU_IN_GATE:-}" ]; then
    until marker=$(admit_launch); do wait_for_gate; done
  fi
  local unit="${SCOPE_PREFIX}-batch-${name}-$$"
  echo "$unit.scope" >> "$REGISTRY"
  local limit=$BATCH_LIMIT
  [ "${ZESU_IO:-batch}" = gate ] && limit=$GATE_LIMIT
  env ZESU_IN_BATCH=1 systemd-run --user --scope --quiet --unit="$unit" \
    -p "MemoryMax=${limit}" -p MemorySwapMax=0 -- $(io_class) "$@"
  status=$?
  [ -z "$marker" ] || rm -f "$marker"
  return "$status"
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
  printf 'guard: used %s GiB (launch <%s, hold %s, kill %s); coqc %s machine-wide; load5 %s; blocked %s; jobs %s; batch peak %d GiB; gate lock %s; holds %s; guard kills %s\n' \
    "$(used_gib)" "$LAUNCH_GIB" "$HOLD_GIB" "$KILL_GIB" "$(coqc_count)" "$(load_five)" "$(blocked_count)" "$(guard_jobs)" \
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
  # A gate script passes its own PID, so the lock lives as long as the gate.
  lock-want) lock_acquire "$3" "$2" ;;
  lock-hold) lock_hold "$2" ;;
  lock-release) lock_release "$2" ;;
  hold)   r=$(hold_reason); echo "${r:-none}" ;;
  window) shift; python3 "$PROM" window "$@" ;;
  report) report ;;
  *) echo "usage: $0 {jobs|gate-jobs [TARGET]|wait|watch|scope NAME -- CMD|batch NAME -- CMD|locked NAME -- CMD|lock-status|lock-want PID HOLDER|lock-hold PID|lock-release PID|hold|report|window ARGS|peak|reset-peak}" >&2; exit 2 ;;
esac
