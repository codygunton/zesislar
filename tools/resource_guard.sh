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
#   gate-jobs [TARGET]   the concurrency a gate may use: 24
#   gate-module-limit    print the configured per-module gate limit in GiB
#   coqc-count [nonwriter] count actual compilers, excluding shell wrappers
#   native-limit         read the native admission limit without changing state
#   wait                 block until one more job may start
#   reserve-coqc PID     request a compiler launch without holding a slot
#   confirm-coqc TOKEN   admit a compiler launch atomically
#   watch                the polling loop; kills the youngest scope at its memory boundary
#   scope NAME [--cpu SECONDS] -- CMD    run CMD in its configured module scope, registered
#   batch NAME -- CMD    run CMD in the batch scope, 150 GiB (a gate 120), swap off
#   locked NAME -- CMD   run CMD holding the gate lock
#   lock-status          print the gate lock, removing a stale one
#   lock-want PID HOLDER take the lock for a gate script, state wanted
#                        ZESU_GATE_CLASS=root|child|preview queues by class
#                        and arrival order. Unclassified calls try once.
#   lock-hold PID        wait for running job scopes to finish, then mark
#                        the lock held
#   report               one line of guard state and Prometheus figures
#   window ARGS          `tools/det/prom.py window ARGS`
#
# Memory admission uses MemAvailable. Each launch needs its job limit
# plus 20 GiB. Hold below 20 GiB available; kill at or below 10 GiB available.
# Ordinary proofs use 6 GiB; issue-10 probes use 64 GiB and require 84 GiB
# available. CPU-only issue-10 probes use 6 GiB and require 26 GiB available.
# Both probe types share the same two admitted slots.
# The temporary used-memory policy is explicit: launch below 200 GiB,
# hold at 215 GiB, and kill at 230 GiB. It does not change scope fences.
# Memory limits remain 150G for batches and 120G for gates, with no swap.
# Other launch checks retain 48 compiler slots, load5 <= 80, blocked <= 16,
# and the gate lock. The interim controller may restrict compiler slots.
# Named writers may continue through a gate with two compilers each.
# A live gate leaves 16 of the 48 slots for writers.
# A gate has priority over new batches (plan section 4 item 4, amended
# 2026-09-24): it writes the lock in the `wanted` state before its build,
# and no new arm, batch, scope, or probe starts while the lock exists in
# either state. Jobs inside a running batch go on, so a running arm
# completes; the gate waits for it and then marks the lock `held`.
# Validated issue-10 probes continue beside gates. They retain compiler
# and memory accounting, with at most two admitted probes machine-wide.
# While an arm populates its build directory, or while a disk is more than
# 80 % busy, launches also keep a ramp of two per second across guards;
# otherwise they fill the width as slots free up.

set -uo pipefail

# Controllers query this policy before normal resource admission. Keep this
# branch before registry setup so the query does not create or prune state.
if [ "${1:-}" = native-limit ]; then
  [ "$#" -eq 1 ] || { echo "resource guard: native-limit takes no arguments" >&2; exit 2; }
  printf '%s\n' 8
  exit 0
fi

# The hard per-job cap: what one `coqc` scope may use before the kernel
# kills it. Ordinary wrappers use the configured gate module limit.
GATE_MODULE_LIMIT_GIB=${ZESU_GATE_MODULE_LIMIT_GIB-16}
MODULE_LIMIT_GIB=${ZESU_MODULE_LIMIT_GIB:-$GATE_MODULE_LIMIT_GIB}
# What a job actually costs, which is what the job count should be sized
# against. Measured 2026-09-20: a clean `check-iris` at 25 jobs peaks at
# 75 GiB, so 3.0 GiB per job; on 2026-09-22 batches 48 wide peaked at
# about 74 GiB, so 1.5. At 3 GiB the 70-percent formula allows 42
# workers when 180 GiB is available.
JOB_GIB=${ZESU_JOB_GIB:-3}
BATCH_LIMIT=${ZESU_BATCH_LIMIT:-150G}
GATE_LIMIT=${ZESU_GATE_LIMIT:-120G}
# All proof workloads share this kernel backstop across independent runs.
WORKLOAD_PARENT_SLICE=zesuworkloads.slice
WORKLOAD_PARENT_BYTES=187904819200
MAX_JOBS=${ZESU_MAX_JOBS:-48}
MEMORY_POLICY=${ZESU_MEMORY_POLICY:-available}
case "$MEMORY_POLICY" in available|used) ;; *) echo "resource guard: invalid memory policy" >&2; exit 2 ;; esac
LAUNCH_GIB=${ZESU_LAUNCH_GIB:-200}
HOLD_GIB=${ZESU_HOLD_GIB:-215}
KILL_GIB=${ZESU_KILL_GIB:-230}
MEMORY_HEADROOM_GIB=20
MEMORY_KILL_AVAILABLE_GIB=10
DISK_BUSY_PERCENT=${ZESU_DISK_BUSY_PERCENT:-80}
# Disk thresholds use decimal GB. Maintenance never removes worktree files.
DISK_TRIM_BELOW_BYTES=60000000000
DISK_PROBE_MIN_BYTES=20000000000
DUNE_CACHE_TRIM_BIN=/home/cody/islaris/_opam/bin/dune
# An arm's build writes a marker `<prefix>.<pid>` while it populates its
# build directory from the Dune cache; the ramp applies while one is live.
POPULATING_PREFIX=${ZESU_POPULATING_PREFIX:-/tmp/zesu-populating}
MAX_COQC=${ZESU_MAX_COQC:-48}
PROC_ROOT=${ZESU_PROC_ROOT:-/proc}
CGROUP_ROOT=${ZESU_CGROUP_ROOT:-/sys/fs/cgroup}
MAX_LOAD=${ZESU_MAX_LOAD:-80}
MAX_BLOCKED=${ZESU_MAX_BLOCKED:-16}
# Two launches per second, shared by every guard of every agent.
RAMP_MS=${ZESU_RAMP_MS:-500}
RAMP_FILE=${ZESU_RAMP_FILE:-/tmp/zesu-guard-ramp}
GATE_LOCK=${ZESU_GATE_LOCK:-/tmp/zesu-gate.lock}
GATE_MUTEX="${GATE_LOCK}.mutex"
GATE_WAITERS="${GATE_LOCK}.waiters"
FAST_MAX_JOBS=${ZESU_FAST_MAX_JOBS:-24}
# Gates leave 16 machine slots for writers. Each named writer gets two.
WRITER_RESERVED=16
WRITER_MAX_COQC=${ZESU_WRITER_MAX_COQC:-2}
if ! [[ "$WRITER_MAX_COQC" =~ ^[1-9][0-9]*$ ]]; then
  echo "resource guard: invalid writer compiler limit" >&2; exit 2
fi
WRITER_ID=${ZESU_WRITER_ID:-}
if [ -n "$WRITER_ID" ] && ! [[ "$WRITER_ID" =~ ^[a-zA-Z0-9._-]+$ ]]; then
  echo "resource guard: invalid writer identity" >&2; exit 2
fi
PROM=$(dirname "$0")/det/prom.py
POLL_SECONDS=${ZESU_GUARD_POLL:-5}
SCOPE_PREFIX=${ZESU_SCOPE_PREFIX:-zesudet}
STATE_DIR=${ZESU_GUARD_STATE:-${XDG_RUNTIME_DIR:-/tmp}/zesu-guard}
REGISTRY="$STATE_DIR/scopes"
LAUNCHES="$STATE_DIR/launches"
COQC_RESERVATIONS="$STATE_DIR/coqc-reservations"
PEAK="$STATE_DIR/peak"
LOG="$STATE_DIR/guard.log"

mkdir -p "$STATE_DIR"
mkdir -p "$LAUNCHES"
mkdir -p "$COQC_RESERVATIONS"
touch "$REGISTRY" "$LOG" "$PEAK"

GIB=$((1024 * 1024 * 1024))
MEMORY_TOOL=${ZESU_MODULE_MEMORY_TOOL:-$(dirname "$0")/module_memory.py}
if ! [[ "$MODULE_LIMIT_GIB" =~ ^[1-9][0-9]{0,2}$ ]]; then
  echo "resource guard: invalid module memory limit" >&2; exit 2
fi
MEMORY_CLAIM_BYTES=${ZESU_MODULE_CLAIM_BYTES:-$(( MODULE_LIMIT_GIB * GIB ))}
if ! [[ "$MEMORY_CLAIM_BYTES" =~ ^[1-9][0-9]{0,11}$ ]]; then
  echo "resource guard: invalid module memory reservation" >&2; exit 2
fi

note() { printf '%s %s\n' "$(date -Is)" "$*" >> "$LOG"; }

home_free_bytes() { df -B1 --output=avail /home | awk 'NR == 2 {print $1}'; }

# Dune trims only unused, single-link cache artifacts. Keep maintenance outside
# the admission mutex so existing scopes can release their compiler slots.
cache_disk_admission() {
  local free status=0 maintenance_lock low_marker="$STATE_DIR/cache-low-space"
  free=$(home_free_bytes) || return 2
  [[ "$free" =~ ^[0-9]+$ ]] || { echo "resource guard: cannot read /home free bytes" >&2; return 2; }
  exec {maintenance_lock}>>"$STATE_DIR/cache-maintenance.mutex" || return 2
  flock "$maintenance_lock" || { exec {maintenance_lock}>&-; return 2; }
  free=$(home_free_bytes)
  if ! [[ "$free" =~ ^[0-9]+$ ]]; then
    flock -u "$maintenance_lock"; exec {maintenance_lock}>&-
    echo "resource guard: cannot read /home free bytes" >&2; return 2
  fi
  if (( free >= DISK_TRIM_BELOW_BYTES )); then
    rm -f "$low_marker"
  elif [[ ! -e "$low_marker" ]] || { diagnostic_probe && (( free < DISK_PROBE_MIN_BYTES )); }; then
    note "CACHE_TRIM start pid=$BASHPID free_bytes=$free root=/home/cody/.cache/dune trimmed_size=20GiB"
    DUNE_CACHE_ROOT=/home/cody/.cache/dune "$DUNE_CACHE_TRIM_BIN" cache trim --trimmed-size=20GiB \
      >>"$STATE_DIR/cache-trim.log" 2>&1 || status=$?
    free=$(home_free_bytes)
    note "CACHE_TRIM end pid=$BASHPID status=$status free_bytes=$free"
    if [[ "$free" =~ ^[0-9]+$ ]]; then
      if (( free >= DISK_TRIM_BELOW_BYTES )); then
        rm -f "$low_marker"
      elif (( status == 0 )); then
        : > "$low_marker"
      fi
    fi
  fi
  flock -u "$maintenance_lock"; exec {maintenance_lock}>&-
  [[ "$free" =~ ^[0-9]+$ ]] || { echo "resource guard: cannot read /home free bytes" >&2; return 2; }
  if diagnostic_probe && (( free < DISK_PROBE_MIN_BYTES )); then
    note "REFUSE probe launch: /home free_bytes=$free requires=$DISK_PROBE_MIN_BYTES"
    echo "resource guard: probe refused: /home has $free free bytes, requires $DISK_PROBE_MIN_BYTES" >&2
    return 3
  fi
}

memory() { free -b | awk '/^Mem:/ {print $2, $3, $7}'; }

# Used means total minus available, the figure Prometheus reports
# (`MemTotal - MemAvailable`), so the thresholds and the reports agree.
used_gib() {
  local total available
  read -r total _ available < <(memory)
  echo $(( (total - available) / GIB ))
}

available_gib() {
  local total used available
  read -r total used available < <(memory)
  echo $(( available / GIB ))
}

memory_hold_reason() {
  local available used required job_gib=$MODULE_LIMIT_GIB
  if [ -n "${ZESU_MODULE_MEMORY_PROFILE:-}" ]; then
    job_gib=$(( (MEMORY_CLAIM_BYTES + GIB - 1) / GIB ))
  fi
  if [ "$MEMORY_POLICY" = available ]; then
    available=$(available_gib)
    required=$(( job_gib + MEMORY_HEADROOM_GIB ))
    if (( available < MEMORY_HEADROOM_GIB )); then
      echo "memory available $available GiB, below the 20 GiB hold"
    elif (( available < required )); then
      echo "memory available $available GiB, requires $required GiB for a $job_gib GiB job"
    fi
  else
    used=$(used_gib)
    if (( used >= HOLD_GIB )); then echo "memory ${used} GiB, at the ${HOLD_GIB} GiB hold"
    elif (( used >= LAUNCH_GIB )); then echo "memory ${used} GiB, launch line ${LAUNCH_GIB}"; fi
  fi
}

memory_kill_required() {
  if [ "$MEMORY_POLICY" = available ]; then
    local total used available
    read -r total used available < <(memory)
    (( available <= MEMORY_KILL_AVAILABLE_GIB * GIB ))
  else
    (( $(used_gib) >= KILL_GIB ))
  fi
}

# Dune's executable remains named coqc. Its Bash wrapper is not a compiler.
# Count one PID snapshot and remove shell wrappers before slot admission.
compiler_process() {
  local pid=$1 executable
  executable=$(readlink "$PROC_ROOT/$pid/exe" 2>/dev/null) || executable=""
  case "${executable##*/}" in bash|sh|dash|zsh|ksh) return 1 ;; esac
  return 0
}

compiler_pids() {
  local pid snapshot status
  if snapshot=$(pgrep -x coqc); then :
  else
    status=$?
    if (( status != 1 )); then
      echo "resource guard: compiler snapshot failed (pgrep exit $status)" >&2
      return "$status"
    fi
    snapshot=""
  fi
  for pid in $snapshot; do
    [[ "$pid" =~ ^[1-9][0-9]*$ ]] || continue
    compiler_process "$pid" && printf '%s ' "$pid"
  done
  return 0
}

coqc_count() {
  local snapshot
  snapshot=$(compiler_pids) || return $?
  set -- $snapshot
  echo "$#"
}

# load5, not load1: the load1 spikes of 2026-09-22 lasted one to five
# minutes and followed disk bursts, and holding on them stalls a batch
# for a burst it did not cause.
load_five() { awk '{printf "%d", $2}' /proc/loadavg; }

blocked_count() { awk '/^procs_blocked/ {print $2}' /proc/stat; }

# --- the gate lock ---------------------------------------------------------
#
# A gate excludes ordinary launches and admits named writers: it writes its state,
# holder, PID, and start time to the lock, and every guard holds new
# launches while the lock is live, wanted or held. A lock whose PID is dead
# is removed and reported.

lock_pid() { sed -n 's/.*pid=\([0-9]*\).*/\1/p' "$GATE_LOCK" 2>/dev/null; }

# A PID alone can refer to another process after its original owner exits.
# Read the start tick after the final ')' because comm can contain spaces.
gate_process_start() {
  local pid=$1 stat fields
  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 1
  { IFS= read -r stat < "/proc/$pid/stat"; } 2>/dev/null || return 1
  read -r -a fields <<< "${stat##*) }"
  [[ "${fields[0]:-Z}" != Z && "${fields[0]:-X}" != X ]] || return 1
  [[ "${fields[19]:-}" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "${fields[19]}"
}

# Called only under GATE_MUTEX. The owner, caller, and waiter must live.
gate_waiters_clean() {
  local marker class ticket owner owner_start waiter waiter_start caller caller_start extra current
  for marker in "$GATE_WAITERS"/*.waiter; do
    [ -e "$marker" ] || continue
    if read -r class ticket owner owner_start waiter waiter_start caller caller_start extra < "$marker" \
       && [[ "$class" =~ ^(root|child|preview)$ && "$ticket" =~ ^[1-9][0-9]*$ ]] \
       && (( ${#ticket} < 19 || (${#ticket} == 19 && ticket > 0) )) \
       && [ -z "$extra" ] \
       && current=$(gate_process_start "$owner") && [ "$current" = "$owner_start" ] \
       && current=$(gate_process_start "$waiter") && [ "$current" = "$waiter_start" ] \
       && current=$(gate_process_start "$caller") && [ "$current" = "$caller_start" ]; then
      continue
    fi
    rm -f -- "$marker"
    note "STALE gate waiter removed: ${marker##*/}"
  done
}

gate_class_rank() {
  case "$1" in root) echo 0 ;; child) echo 1 ;; preview) echo 2 ;; esac
}

gate_waiter_first() {
  local marker class ticket owner owner_start waiter waiter_start caller caller_start rank
  local best_rank=3 best_ticket=0 first=""
  for marker in "$GATE_WAITERS"/*.waiter; do
    [ -e "$marker" ] || continue
    read -r class ticket owner owner_start waiter waiter_start caller caller_start < "$marker" || return 2
    rank=$(gate_class_rank "$class")
    if (( rank < best_rank || (rank == best_rank && ticket < best_ticket) )); then
      best_rank=$rank; best_ticket=$ticket; first=$marker
    fi
  done
  printf '%s\n' "$first"
}

# Prints the live holder, or nothing. Removes a stale lock and says so.
lock_live_unlocked() {
  gate_waiters_clean
  [ -e "$GATE_LOCK" ] || return 1
  local pid start current; pid=$(lock_pid)
  start=$(sed -n 's/.*pid_start=\([0-9]*\).*/\1/p' "$GATE_LOCK" 2>/dev/null)
  if [ -n "$pid" ] && current=$(gate_process_start "$pid") \
     && { [ -z "$start" ] || [ "$current" = "$start" ]; }; then
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

# The subshell owns the waiter traps without replacing its caller's traps.
lock_acquire() (
  local holder=$1 pid=$2 current status marker="" ticket=0 first queued=0
  local class=${ZESU_GATE_CLASS:-child} owner_start waiter_start caller_start
  local waiter=$BASHPID caller=$$
  case "$class" in root|child|preview) ;; *)
    echo "resource guard: invalid gate class: $class" >&2; return 2 ;;
  esac
  [ -z "${ZESU_GATE_CLASS:-}" ] || queued=1
  owner_start=$(gate_process_start "$pid") || {
    echo "resource guard: invalid gate owner: $pid" >&2; return 2;
  }
  waiter_start=$(gate_process_start "$waiter") || return 2
  caller_start=$(gate_process_start "$caller") || return 2
  cleanup_waiter() {
    [ -n "$marker" ] || return 0
    exec 7>>"$GATE_MUTEX"
    flock 7 || return 2
    rm -f -- "$marker"
    flock -u 7
    exec 7>&-
  }
  trap cleanup_waiter EXIT
  trap 'exit 143' TERM
  trap 'exit 130' INT
  while :; do
    exec 7>>"$GATE_MUTEX"
    flock 7 || return 2
    gate_waiters_clean
    if [ -z "$marker" ]; then
      mkdir -p "$GATE_WAITERS" || return 2
      if [ -e "$GATE_WAITERS/next-ticket" ]; then
        read -r ticket < "$GATE_WAITERS/next-ticket" || return 2
        [[ "$ticket" =~ ^(0|[1-9][0-9]*)$ ]] \
          && (( ${#ticket} < 19 || (${#ticket} == 19 && ticket > 0) )) \
          && (( ticket < 9223372036854775807 )) || return 2
      fi
      ticket=$((ticket + 1))
      printf '%s\n' "$ticket" > "$GATE_WAITERS/next-ticket" || return 2
      marker="$GATE_WAITERS/$pid.$waiter.$RANDOM.waiter"
      printf '%s %s %s %s %s %s %s %s\n' "$class" "$ticket" "$pid" "$owner_start" \
        "$waiter" "$waiter_start" "$caller" "$caller_start" > "$marker" || return 2
      note "QUEUE gate class=$class ticket=$ticket owner=$pid waiter=$waiter caller=$caller"
    fi
    current=$(gate_process_start "$pid")
    if [ "$current" != "$owner_start" ] || [ ! -f "$marker" ]; then
      flock -u 7; exec 7>&-; return 2
    fi
    current=$(lock_live_unlocked); status=$?
    first=$(gate_waiter_first) || { flock -u 7; exec 7>&-; return 2; }
    if (( status != 0 )) && [ "$first" = "$marker" ] \
       && ( set -C; printf 'state=wanted holder=%s pid=%s start=%s class=%s pid_start=%s\n' \
           "$holder" "$pid" "$(date -Is)" "$class" "$owner_start" > "$GATE_LOCK" ) 2>/dev/null; then
      rm -f -- "$marker"
      marker=""
      flock -u 7
      exec 7>&-
      note "LOCK wanted by $holder pid $pid class=$class ticket=$ticket"
      return 0
    fi
    flock -u 7
    exec 7>&-
    if (( queued == 0 )); then
      echo "refusing: a gate holds or waits for $GATE_LOCK: ${current:-higher-priority waiter}" >&2
      return 3
    fi
    sleep "$POLL_SECONDS"
  done
)

# wanted -> held, once the running batches have finished. Gives up after
# ZESU_GATE_SCOPE_WAIT seconds (4 h) and releases the lock.
lock_hold() {
  local pid=$1 limit=${ZESU_GATE_SCOPE_WAIT:-14400} start=$SECONDS live
  local noted=""
  # A registered launch can precede its systemd scope. Wait for both.
  while live=$(( $(gate_scopes | wc -l) + $(gate_launches | wc -l) + $(gate_reservations | wc -l) )); (( live > 0 )); do
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
    if kill -0 "$pid" 2>/dev/null; then
      [ "$(sed -n 's/^writer=//p' "$marker")" ] || echo "$marker"
    else rm -f "$marker"; fi
  done
}

# An admitted launch keeps its slot until its owner or compiler exits.
live_reservations() {
  local marker owner child
  for marker in "$COQC_RESERVATIONS"/*; do
    [ -e "$marker" ] || continue
    owner=${marker##*/}; owner=${owner%%.*}
    if ! kill -0 "$owner" 2>/dev/null; then
      rm -f "$marker"; continue
    fi
    read -r child < "$marker" || continue
    if [[ "$child" =~ ^[0-9]+$ ]] && [ ! -d "$PROC_ROOT/$child" ]; then
      rm -f "$marker"; continue
    fi
    echo "$marker"
  done
}

reservation_writer() {
  local line
  while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in writer=*) printf '%s\n' "${line#writer=}" ;; esac
  done < "$1"
}

# A recorder can be the marked child. Count its actual compiler once.
reservation_compiler() {
  local child descendant queue comm
  read -r child < "$1" || return 1
  # An unmarked launch has no compiler yet. Its owner can include this scan.
  [[ "$child" =~ ^[0-9]+$ ]] || return 1
  queue=$child
  while [ -n "$queue" ]; do
    descendant=${queue%% *}
    if [ "$queue" = "$descendant" ]; then queue=""; else queue=${queue#* }; fi
    comm=""
    { IFS= read -r comm < "$PROC_ROOT/$descendant/comm"; } 2>/dev/null || true
    if [ "$comm" = coqc ] && compiler_process "$descendant"; then
      echo "$descendant"; return 0
    fi
    child=""
    { IFS= read -r child < "$PROC_ROOT/$descendant/task/$descendant/children"; } 2>/dev/null || true
    for child in $child; do queue="${queue:+$queue }$child"; done
  done
  return 1
}

nonwriter_coqc_count() {
  local snapshot pid marker compiler writer_pids="" count=0
  snapshot=$(compiler_pids) || return $?
  while IFS= read -r marker; do
    [ -n "$(reservation_writer "$marker")" ] || continue
    compiler=$(reservation_compiler "$marker") || continue
    writer_pids="$writer_pids $compiler"
  done < <(live_reservations)
  for pid in $snapshot; do
    [[ " $writer_pids " == *" $pid "* ]] || count=$(( count + 1 ))
  done
  echo "$count"
}

gate_reservations() {
  local marker state
  while IFS= read -r marker; do
    read -r state < "$marker" || continue
    # Old pending requests hold no slot and must yield to a gate.
    [ "$state" != pending ] || continue
    probe_record "$marker" && continue
    [ -n "$(reservation_writer "$marker")" ] || echo "$marker"
  done < <(live_reservations)
}

# A probe tag binds validated limits to the reservation owner's identity.
# These records remain in live_reservations and compiler admission counts.
process_start() {
  local stat
  IFS= read -r stat < "$PROC_ROOT/$1/stat" 2>/dev/null || return 1
  stat=${stat##*) }
  set -- $stat
  [ "$#" -ge 20 ] || return 1
  printf '%s\n' "${20}"
}

probe_record() {
  local marker=$1 owner start
  if grep -Fxq 'probe=issue10' "$marker"; then
    grep -Fxq 'memory_gib=64' "$marker" || return 1
  elif grep -Fxq 'probe=issue10-cpu-only' "$marker"; then
    grep -Fxq 'memory_gib=6' "$marker" || return 1
  else return 1; fi
  grep -Fxq 'cpu=unlimited' "$marker" || return 1
  owner=${marker##*/}; owner=${owner%%.*}
  start=$(sed -n 's/^owner_start=//p' "$marker")
  [ -n "$start" ] && [ "$start" = "$(process_start "$owner")" ]
}

probe_count() {
  local marker count=0
  while IFS= read -r marker; do
    probe_record "$marker" && count=$(( count + 1 ))
  done < <(live_reservations)
  echo "$count"
}

# Only gate draining ignores validated probes. Resource holds do not.
gate_scopes() {
  local unit marker probe
  while IFS= read -r unit; do
    probe=0
    while IFS= read -r marker; do
      if probe_record "$marker" && grep -Fxq "scope=$unit" "$marker"; then
        probe=1; break
      fi
    done < <(live_reservations)
    [ "$probe" = 1 ] || printf '%s\n' "$unit"
  done < <(live_scopes)
}

gate_launches() {
  local marker
  while IFS= read -r marker; do
    probe_record "$marker" || printf '%s\n' "$marker"
  done < <(live_launches)
}

# Associate an admitted probe's scope before systemd starts the compiler.
mark_probe_scope() {
  local marker=$1 unit=$2 replacement
  exec 7>>"$GATE_MUTEX"
  flock 7
  if ! reservation_path "$marker" || ! probe_record "$marker"; then
    flock -u 7; exec 7>&-; return 2
  fi
  replacement=$(mktemp "$STATE_DIR/probe-scope.XXXXXXXX") || {
    flock -u 7; exec 7>&-; return 2
  }
  if ! sed '/^scope=/d' "$marker" > "$replacement" \
     || ! printf 'scope=%s\n' "$unit" >> "$replacement" \
     || ! touch -r "$marker" "$replacement" \
     || ! mv -f -- "$replacement" "$marker"; then
    rm -f -- "$replacement"
    flock -u 7; exec 7>&-; return 2
  fi
  flock -u 7; exec 7>&-
}

# This runs under the gate mutex. Use one PID snapshot for both counts.
# Count confirmed launches and marked compilers, excluding pending requests.
compiler_admission_reason() {
  local confirming=${1:-0} count pending=0 marker writer compiler snapshot
  local writers=0 own=0 counted_writers=0 pending_writers=0 nonwriter_limit
  snapshot=$(compiler_pids) || return $?
  set -- $snapshot; count=$#
  while IFS= read -r marker; do
    local state
    read -r state < "$marker" || continue
    [ "$state" != pending ] || continue
    writer=$(reservation_writer "$marker")
    if [ -n "$writer" ]; then
      writers=$(( writers + 1 ))
      [ "$writer" != "$WRITER_ID" ] || own=$(( own + 1 ))
    fi
    compiler=$(reservation_compiler "$marker") || compiler=""
    if [ -n "$compiler" ] && [[ " $snapshot " == *" $compiler "* ]]; then
      [ -z "$writer" ] || counted_writers=$(( counted_writers + 1 ))
    else
      pending=$(( pending + 1 ))
      [ -z "$writer" ] || pending_writers=$(( pending_writers + 1 ))
    fi
  done < <(live_reservations)
  if (( count + pending + 1 - confirming > MAX_COQC )); then
    echo "coqc $count with $pending reservations machine-wide"
  elif [ -n "$WRITER_ID" ]; then
    if (( own + 1 - confirming > WRITER_MAX_COQC )); then
      echo "writer $WRITER_ID at its $WRITER_MAX_COQC compiler limit"
    elif (( writers + 1 - confirming > WRITER_RESERVED )); then
      echo "writers at their $WRITER_RESERVED reserved slots"
    fi
  elif lock_live_unlocked >/dev/null 2>&1; then
    nonwriter_limit=$(( MAX_COQC - WRITER_RESERVED ))
    # A reduced total cap cannot reserve sixteen writer slots.
    (( MAX_COQC > WRITER_RESERVED )) || nonwriter_limit=$MAX_COQC
    if (( count - counted_writers + pending - pending_writers + 1 - confirming > nonwriter_limit )); then
      echo "nonwriter compiler limit $nonwriter_limit; $WRITER_RESERVED slots reserved for writers"
    fi
  fi
}

# confirm_coqc holds GATE_MUTEX while this function refreshes live claims.
module_memory_admission_reason() {
  [ -n "${ZESU_MODULE_MEMORY_PROFILE:-}" ] || return 0
  local total used available marker
  local -a markers=()
  while IFS= read -r marker; do
    [ -n "$marker" ] && markers+=("$marker")
  done < <(live_reservations)
  read -r total used available < <(memory)
  python3 "$MEMORY_TOOL" admission --request-bytes "$MEMORY_CLAIM_BYTES" \
    --fallback-bytes "$(( MODULE_LIMIT_GIB * GIB ))" \
    --available-bytes "$available" --headroom-bytes "$(( MEMORY_HEADROOM_GIB * GIB ))" \
    --maximum-compilers "$MAX_COQC" --proc "$PROC_ROOT" "${markers[@]}"
}

reservation_class() {
  if [ -n "${ZESU_IN_GATE:-}" ]; then echo gate
  elif [ -n "${ZESU_IN_BATCH:-}" ]; then echo batch
  elif [ -n "$WRITER_ID" ]; then echo "writer:$WRITER_ID"
  else echo standalone
  fi
}

# A request has no file and holds no slot while it waits.
reserve_coqc() {
  local owner=$1 marker
  if ! [[ "$owner" =~ ^[0-9]+$ ]] || ! kill -0 "$owner" 2>/dev/null; then
    echo "resource guard: invalid reservation owner: $owner" >&2
    return 2
  fi
  marker="$COQC_RESERVATIONS/$owner.$RANDOM.$RANDOM"
  echo "$marker"
}

reservation_path() {
  [[ "$(dirname "$1")" == "$COQC_RESERVATIONS" && -f "$1" ]]
}

reservation_holders() {
  local marker state writer holders=""
  while IFS= read -r marker; do
    read -r state < "$marker" || continue
    writer=$(reservation_writer "$marker")
    holders="${holders:+$holders,}${marker##*/}:$state:${writer:-batch}"
  done < <(live_reservations)
  echo "${holders:-none}"
}

# A confirmed slot remains valid while its owner lives. This read-only
# check lets an admitted launch drain without joining the admission queue.
confirmed_reservation() {
  local marker=$1 owner state
  owner=${marker##*/}; owner=${owner%%.*}
  [[ "$owner" =~ ^[0-9]+$ ]] || return 1
  kill -0 "$owner" 2>/dev/null || return 1
  reservation_path "$marker" || return 1
  read -r state < "$marker" || return 1
  [ "$state" != pending ] || return 1
  [ "$(reservation_writer "$marker")" = "$WRITER_ID" ]
}

# Take the slot atomically immediately before launch. An admitted caller
# can confirm again without waiting for admission while it holds its slot.
confirm_coqc() {
  local marker=$1 reason holder admission owner status state replacement aggregate held=""
  validate_probe_scope || return $?
  confirmed_reservation "$marker" && return 0
  while :; do
    cache_disk_admission || return $?
    exec 7>>"$GATE_MUTEX"
    flock 7 || { echo "resource guard: confirmation mutex failed" >&2; return 2; }
    owner=${marker##*/}; owner=${owner%%.*}
    if [[ "$(dirname "$marker")" != "$COQC_RESERVATIONS" ]] \
       || ! [[ "$owner" =~ ^[0-9]+$ ]] || ! kill -0 "$owner" 2>/dev/null; then
      echo "resource guard: invalid reservation path or dead owner: $marker" >&2
      flock -u 7; exec 7>&-; return 2
    fi
    if reservation_path "$marker"; then
      if [ "$(reservation_writer "$marker")" != "$WRITER_ID" ]; then
        echo "resource guard: reservation writer mismatch: $marker" >&2
        flock -u 7; exec 7>&-; return 2
      fi
      if ! read -r state < "$marker"; then
        echo "resource guard: cannot read reservation: $marker" >&2
        flock -u 7; exec 7>&-; return 2
      fi
      if [ "$state" != pending ]; then
        flock -u 7; exec 7>&-; return 0
      fi
      # Remove requests from the old protocol before any wait.
      rm -f -- "$marker"
    fi
    holder=""
    if [ -z "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}$WRITER_ID" ]; then
      holder=$(lock_live_unlocked 2>/dev/null) || holder=""
    fi
    if [ -n "$holder" ]; then
      echo "resource guard: confirmation refused by gate lock: $holder" >&2
      flock -u 7; exec 7>&-; return 3
    fi
    reason=$(hold_reason no-lock) || {
      status=$?; echo "resource guard: confirmation resource check failed ($status)" >&2
      flock -u 7; exec 7>&-; return "$status"
    }
    admission=$(compiler_admission_reason) || {
      status=$?; echo "resource guard: confirmation admission check failed ($status)" >&2
      flock -u 7; exec 7>&-; return "$status"
    }
    if [ -z "$admission" ]; then
      admission=$(module_memory_admission_reason) || {
        status=$?; echo "resource guard: module memory check failed ($status)" >&2
        flock -u 7; exec 7>&-; return "$status"
      }
    fi
    if diagnostic_probe && (( $(probe_count) >= 6 )); then
      admission="issue10 probes at their six-probe limit"
    fi
    if [ -z "$reason$holder$admission" ]; then
      replacement=$(mktemp "$STATE_DIR/coqc-confirm.XXXXXXXX") || {
        echo "resource guard: cannot create confirmation file" >&2
        flock -u 7; exec 7>&-; return 2
      }
      aggregate=""
      [ -n "$WRITER_ID" ] || aggregate="${ZESU_AGGREGATE_SLICE:-}"
      if ! printf 'confirmed\nwriter=%s\naggregate=%s\n' "$WRITER_ID" "$aggregate" > "$replacement"; then
        rm -f -- "$replacement"
        flock -u 7; exec 7>&-; return 2
      fi
      printf 'memory_claim_bytes=%s\nmemory_fence_bytes=%s\n' \
        "$MEMORY_CLAIM_BYTES" "$(( MODULE_LIMIT_GIB * GIB ))" >> "$replacement" || {
          rm -f -- "$replacement"; flock -u 7; exec 7>&-; return 2;
        }
      if diagnostic_probe; then
        local probe_tag=issue10
        [ "${ZESU_DIAGNOSTIC_PROBE:-0}" != cpu-only ] || probe_tag=issue10-cpu-only
        if ! printf 'probe=%s\nmemory_gib=%s\ncpu=unlimited\nowner_start=%s\n' \
            "$probe_tag" "$MODULE_LIMIT_GIB" "$(process_start "$owner")" >> "$replacement"; then
          rm -f -- "$replacement"
          flock -u 7; exec 7>&-; return 2
        fi
      fi
      if ! mv -f -- "$replacement" "$marker"; then
        echo "resource guard: cannot publish reservation: $marker" >&2
        rm -f -- "$replacement"
        flock -u 7; exec 7>&-; return 2
      fi
      [ -z "$held" ] || note "RESUME reservation launch: $held"
      flock -u 7; exec 7>&-; return 0
    fi
    reason=${reason:-${holder:+gate lock: $holder}}
    reason=${reason:-$admission}
    if [ "$reason" != "$held" ]; then
      note "HOLD reservation launch: class=$(reservation_class) $reason holders=$(reservation_holders)"
      held=$reason
    fi
    flock -u 7; exec 7>&-
    sleep "$POLL_SECONDS"
  done
}

mark_coqc() {
  local marker=$1 child=$2
  [[ "$child" =~ ^[0-9]+$ ]] || { echo "resource guard: invalid compiler PID: $child" >&2; return 2; }
  exec 7>>"$GATE_MUTEX"
  flock 7
  if ! reservation_path "$marker"; then
    echo "resource guard: compiler reservation disappeared: $marker" >&2
    flock -u 7; exec 7>&-; return 2
  fi
  local writer replacement aggregate; writer=$(reservation_writer "$marker")
  aggregate=$(sed -n '3s/^aggregate=//p' "$marker")
  replacement=$(mktemp "$STATE_DIR/coqc-mark.XXXXXXXX")
  printf '%s\nwriter=%s\naggregate=%s\n' "$child" "$writer" "$aggregate" > "$replacement"
  # Preserve the validated probe tag and scope association.
  sed -n '4,$p' "$marker" >> "$replacement"
  # Marking the child must not restart the confirmation's launch window.
  touch -r "$marker" "$replacement"
  mv -f -- "$replacement" "$marker"
  flock -u 7
  exec 7>&-
}

release_coqc() {
  local marker=$1
  exec 7>>"$GATE_MUTEX"
  flock 7
  if reservation_path "$marker"; then rm -f "$marker"; fi
  flock -u 7
  exec 7>&-
}

release_aggregate_reservations() {
  local slice=$1 marker
  exec 7>>"$GATE_MUTEX"
  flock 7
  for marker in "$COQC_RESERVATIONS"/*; do
    [ -f "$marker" ] || continue
    if [ "$(sed -n '3s/^aggregate=//p' "$marker")" = "$slice" ]; then
      rm -f "$marker"
    fi
  done
  flock -u 7
  exec 7>&-
}

run_locked() {
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  case "$name" in
    check-fast|check-iris)
      if [ "${ZESU_TIMING_RUN:-0}" != 1 ]; then exec "$@"; fi ;;
  esac
  # A gate that already holds the lock runs `make`, which comes back here.
  # A benchmark arm's build is batch work, not a gate (ZESU_ARM).
  if [ -n "${ZESU_IN_GATE:-}${ZESU_ARM:-}" ]; then exec "$@"; fi
  lock_acquire "${COORD_AGENT:-$USER}:$name:$PWD" $$ || exit $?
  trap 'lock_release $$' EXIT
  lock_hold $$ || exit $?
  ZESU_IN_GATE=1 "$@"
}

register_run_actor() {
  [ -n "${ZESU_RUN_ID:-}" ] || return 0
  local actor=${1:-$BASHPID} ticks registry
  ticks=$(gate_process_start "$actor") || return 2
  registry=${ZESU_RUN_REGISTRY_TOOL:-$(dirname "$(realpath "$0")")/run_registry.py}
  "${ZESU_REGISTRY_PYTHON:-python3}" "$registry" register-job \
    --run-id "$ZESU_RUN_ID" --pid "$actor" --startticks "$ticks"
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

# Keep the memory headroom when choosing the batch width.
guard_jobs() {
  local limit available budget headroom
  if [ -n "${ZESU_MODULE_MEMORY_PROFILE:-}" ]; then
    echo "$MAX_JOBS"; return 0
  fi
  available=$(available_gib)
  budget=$(( available * 70 / 100 ))
  headroom=$(( available - MEMORY_HEADROOM_GIB ))
  (( budget <= headroom )) || budget=$headroom
  if [ "$MEMORY_POLICY" = used ]; then
    headroom=$(( HOLD_GIB - $(used_gib) ))
    (( budget <= headroom )) || budget=$headroom
  fi
  limit=$(( budget / JOB_GIB ))
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
# Both gates stay at 24 while the writer reservation applies.
# The memory formula stays as the ceiling for both.
GATE_MAX_JOBS=${ZESU_GATE_MAX_JOBS:-24}
if [ -n "${ZESU_MODULE_MEMORY_PROFILE:-}" ]; then
  GATE_MAX_JOBS=${ZESU_GATE_MAX_JOBS:-48}
  FAST_MAX_JOBS=${ZESU_FAST_MAX_JOBS:-48}
fi

gate_jobs() {
  local target=${1:-check-iris} cap allowed
  cap=$GATE_MAX_JOBS
  [ "$target" = check-fast ] && cap=$FAST_MAX_JOBS
  allowed=$(guard_jobs)
  (( cap > GATE_MAX_JOBS )) && cap=$GATE_MAX_JOBS
  (( cap < allowed )) && allowed=$cap
  (( allowed < 1 )) && allowed=1
  echo "$allowed"
}

# Retain identities before a guard requests scope termination. No arguments
# or environments are read. A stop request can produce several signals.
record_scope_termination() {
  local unit=$1 requested=$2 cause=$3 properties
  properties=$(systemctl --user show "$unit" -p ControlGroup -p KillSignal 2>/dev/null) || properties=""
  python3 - "$STATE_DIR/terminations.jsonl" "$PROC_ROOT" "$CGROUP_ROOT" \
    "$unit" "$requested" "$cause" "$properties" "$BASHPID" <<'PY_TERMINATION'
from pathlib import Path
import datetime, fcntl, json, signal, sys
output, proc, root, unit, requested, cause, properties, actor = sys.argv[1:]
values = dict(line.split("=", 1) for line in properties.splitlines() if "=" in line)
kill_signal = requested
if requested == "systemd-stop":
    try:
        kill_signal = signal.Signals(int(values["KillSignal"])).name
    except (KeyError, ValueError):
        kill_signal = None
records = []
errors = []
scopes_in_group = set()
path = values.get("ControlGroup", "")
if path:
    group = Path(root) / path.lstrip("/")
    if Path(root).resolve() not in group.resolve().parents:
        raise SystemExit("resource guard: termination cgroup leaves its root")
    try:
        scopes_in_group = {q.name for q in group.rglob("*")
                           if q.is_dir() and q.name.endswith(".scope")}
        if unit.endswith(".scope"):
            scopes_in_group.add(unit)
        members = {int(pid) for q in group.rglob("cgroup.procs") for pid in q.read_text().split()}
    except OSError as error:
        members = set()
        errors.append(type(error).__name__)
    for pid in sorted(members):
        try:
            fields = (Path(proc) / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
            cgroup = (Path(proc) / str(pid) / "cgroup").read_text()
            membership = next(line.split(":", 2)[2] for line in cgroup.splitlines()
                              if line.startswith("0::"))
            if membership != path and not membership.startswith(path.rstrip("/") + "/"):
                records.append({"pid": pid, "start_ticks": int(fields[19]),
                                "scope": unit, "identity_error": "cgroup-changed"})
                continue
            scopes = [part for part in membership.split("/") if part.endswith(".scope")]
            record = {"pid": pid, "start_ticks": int(fields[19]),
                      "scope": scopes[-1] if scopes else unit}
            try:
                limit_lines = (Path(proc) / str(pid) / "limits").read_text().splitlines()
                stack_line = next(line for line in limit_lines if line.startswith("Max stack size"))
                soft, hard, units = stack_line.split()[-3:]
                record.update(stack_limits={"soft_bytes": None if soft == "unlimited" else int(soft),
                                            "hard_bytes": None if hard == "unlimited" else int(hard)},
                              stack_limits_available=True)
            except (OSError, ValueError, IndexError, StopIteration) as error:
                record.update(stack_limits=None, stack_limits_available=False,
                              stack_limit_error=type(error).__name__)
            records.append(record)
        except (OSError, ValueError, IndexError, StopIteration) as error:
            records.append({"pid": pid, "start_ticks": None, "scope": unit,
                            "identity_error": type(error).__name__})
for empty_scope in sorted(scopes_in_group - {record["scope"] for record in records}):
    records.append({"pid": None, "start_ticks": None, "scope": empty_scope})
if not records:
    records.append({"pid": None, "start_ticks": None, "scope": unit})
for record in records:
    record.setdefault("stack_limits", None)
    record.setdefault("stack_limits_available", False)
    record.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  actor_pid=int(actor), requested_unit=unit, signal=kill_signal,
                  action=requested, cause=cause, phase="before-request",
                  capture_errors=errors)
with open(output, "a") as stream:
    fcntl.flock(stream, fcntl.LOCK_EX)
    for record in records:
        stream.write(json.dumps(record, sort_keys=True) + "\n")
    stream.flush()
PY_TERMINATION
}

stop_scope() {
  record_scope_termination "$1" systemd-stop "$2" || note "termination record failed: $1"
  systemctl --user stop "$1"
}

release_empty_registered_scope() {
  local unit=$1 launcher tasks
  grep -Fxq -- "$unit" "$REGISTRY" || return 1
  if [[ "$unit" =~ -([0-9]+)-[0-9]+\.scope$ ]]; then
    launcher=${BASH_REMATCH[1]}
  elif [[ "$unit" =~ -batch-.*-([0-9]+)\.scope$ ]]; then
    launcher=${BASH_REMATCH[1]}
  else return 1; fi
  kill -0 "$launcher" 2>/dev/null && return 1
  tasks=$(systemctl --user show "$unit" -p TasksCurrent --value 2>/dev/null) || return 1
  [ "$tasks" = 0 ] || return 1
  stop_scope "$unit" empty-scope 2>/dev/null || return 1
  note "STALE empty scope released: $unit launcher $launcher"
}

live_scopes() {
  local unit
  systemctl --user list-units --type=scope --state=active --plain --no-legend \
    "${SCOPE_PREFIX}-*" 2>/dev/null | awk '$1 !~ /-writer-/ {print $1}' |
    while IFS= read -r unit; do
      release_empty_registered_scope "$unit" || printf '%s\n' "$unit"
    done
}

prune_scope_registry() (
  local active replacement unit rest
  exec 8>>"$REGISTRY.lock"
  flock 8
  active=$(systemctl --user list-units --type=scope --state=active --plain \
    --no-legend "${SCOPE_PREFIX}-*" 2>/dev/null) || return 0
  active=$(while read -r unit rest; do
    [ -n "$unit" ] || continue
    release_empty_registered_scope "$unit" || printf '%s\n' "$unit"
  done <<< "$active")
  replacement=$(mktemp "$STATE_DIR/scopes.XXXXXXXX") || return 2
  awk 'NR == FNR { live[$1] = 1; next } live[$0] && !seen[$0]++' \
    <(printf '%s\n' "$active") "$REGISTRY" > "$replacement"
  mv -f -- "$replacement" "$REGISTRY"
)

register_scope() (
  exec 8>>"$REGISTRY.lock"
  flock 8
  printf '%s\n' "$1" >> "$REGISTRY"
)

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
    record_scope_termination "$unit" SIGKILL memory-boundary || note "termination record failed: $unit"
    systemctl --user kill --signal=SIGKILL "$unit" 2>/dev/null
    stop_scope "$unit" memory-boundary-cleanup 2>/dev/null
    echo "$unit"
  fi
}

# Why the guard would hold a launch now, or nothing. A gate's own jobs
# are not held by its own lock.
hold_reason() {
  local memory_reason coqc load blocked holder
  memory_reason=$(memory_hold_reason)
  coqc=$(coqc_count) || return $?
  load=$(load_five); blocked=$(blocked_count)
  if [ -n "$memory_reason" ]; then echo "$memory_reason"
  elif (( coqc >= MAX_COQC )); then echo "coqc $coqc machine-wide"
  elif (( load > MAX_LOAD )); then echo "load5 $load"
  elif (( blocked > MAX_BLOCKED )); then echo "blocked $blocked"
  elif [ "${1:-}" != no-lock ] \
       && [ -z "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}$WRITER_ID" ] \
       && holder=$(lock_live 2>/dev/null); then
    echo "gate lock: $holder"
  fi
}

# A hold is logged once when it starts and once when it ends, with its
# cause, so a report can name every hold.
guard_wait() {
  local reason held="" since
  while :; do
    cache_disk_admission || return $?
    memory_kill_required && kill_youngest > /dev/null
    reason=$(hold_reason) || return $?
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
  local reason held=""
  note "watch start: total $(free -g | awk '/^Mem:/{print $2}') GiB policy=$MEMORY_POLICY"
  while :; do
    record_peak
    reason=$(memory_hold_reason)
    if [ -n "$reason" ] && [ "$reason" != "$held" ]; then
      note "HOLD $reason"; held=$reason
    elif [ -z "$reason" ]; then held=""; fi
    memory_kill_required && kill_youngest > /dev/null
    sleep "$POLL_SECONDS"
  done
}

# A new scope or batch waits while a gate wants or holds the lock. Work
# inside a running batch or gate is not new and goes on.
wait_for_gate() {
  [ -n "${ZESU_IN_GATE:-}${ZESU_IN_BATCH:-}$WRITER_ID" ] && return 0
  local holder held=""
  while holder=$(lock_live 2>/dev/null); do
    [ -z "$held" ] && note "HOLD launch for gate: $holder" && held=1
    sleep "$POLL_SECONDS"
  done
  [ -n "$held" ] && note "RESUME launch after gate"
  return 0
}

# Legacy memory-only wait. Scope and batch launches use guard_wait so
# load, blocked processes, and the compiler count also apply.
wait_for_memory_budget() {
  local reason held=""
  while :; do
    memory_kill_required && kill_youngest > /dev/null
    reason=$(memory_hold_reason)
    if [ -z "$reason" ]; then
      [ -n "$held" ] && note "RESUME memory launch"
      return 0
    fi
    [ "$reason" = "$held" ] || note "HOLD $reason"
    held=$reason
    sleep "$POLL_SECONDS"
  done
}

# Systemd derives the parent from the child slice's dash-separated name.
ensure_workload_parent() {
  systemctl --user set-property --runtime "$WORKLOAD_PARENT_SLICE" \
    "MemoryMax=$WORKLOAD_PARENT_BYTES" MemorySwapMax=0 || return 2
  verify_workload_parent_properties
}

verify_workload_parent_properties() {
  local properties max swap
  properties=$(systemctl --user show "$WORKLOAD_PARENT_SLICE" -p MemoryMax -p MemorySwapMax) || return $?
  max=$(printf '%s\n' "$properties" | awk -F= '$1 == "MemoryMax" {print $2}')
  swap=$(printf '%s\n' "$properties" | awk -F= '$1 == "MemorySwapMax" {print $2}')
  if [ "$max" != "$WORKLOAD_PARENT_BYTES" ] || [ "$swap" != 0 ]; then
    echo "resource guard: shared workload parent lacks its memory fence" >&2
    return 2
  fi
}

verify_workload_ancestor() {
  local group
  group=$(cat /proc/$$/cgroup) || return $?
  if [[ "$group" != *"/$WORKLOAD_PARENT_SLICE/"* ]]; then
    echo "resource guard: workload is outside the shared memory parent" >&2
    return 2
  fi
  verify_workload_parent_properties
}

aggregate_slice() {
  local slice="${ZESU_AGGREGATE_SLICE:-}" limit="${ZESU_AGGREGATE_LIMIT:-}" properties
  if [ -z "$slice" ]; then
    if [ -n "${ZESU_IN_BATCH:-}" ]; then
      echo "resource guard: batch compiler lacks its aggregate slice" >&2
      return 2
    fi
    echo "$WORKLOAD_PARENT_SLICE"
    return 0
  fi
  if [[ ! "$slice" =~ ^zesuworkloads-aggregate[0-9]+p[0-9]+r[0-9]+\.slice$ ]] ||
     [[ ! "$limit" =~ ^(64G|120G|150G)$ ]]; then
    echo "resource guard: invalid aggregate slice or limit" >&2
    return 2
  fi
  properties=$(systemctl --user show "$slice" -p MemoryMax -p MemorySwapMax) || return $?
  local bytes=$(( ${limit%G} * GIB ))
  local max swap
  max=$(printf '%s\n' "$properties" | awk -F= '$1 == "MemoryMax" {print $2}')
  swap=$(printf '%s\n' "$properties" | awk -F= '$1 == "MemorySwapMax" {print $2}')
  if [ "$max" != "$bytes" ] || [ "$swap" != 0 ]; then
    echo "resource guard: aggregate slice lacks its memory fence" >&2
    return 2
  fi
  echo "$slice"
}

# Probe limits are explicit and do not change gate defaults.
diagnostic_probe() {
  case "${ZESU_DIAGNOSTIC_PROBE:-0}" in 1|cpu-only) return 0 ;; *) return 1 ;; esac
}

validate_probe_scope() {
  case "${ZESU_DIAGNOSTIC_PROBE:-0}" in
    0)
      if [[ ! "$GATE_MODULE_LIMIT_GIB" =~ ^([6-9]|[12][0-9]|3[0-2])$ ]]; then
        echo "resource guard: gate module limit must be an integer from 6 through 32 GiB" >&2
        return 2
      fi
      if [ "$MODULE_LIMIT_GIB" != "$GATE_MODULE_LIMIT_GIB" ]; then
        echo "resource guard: ordinary compiler scopes require the configured ${GATE_MODULE_LIMIT_GIB} GiB limit" >&2
        return 2
      fi
      return 0 ;;
    1|cpu-only)
      local memory=64
      [ "${ZESU_DIAGNOSTIC_PROBE:-0}" != cpu-only ] || memory=6
      if [ -n "${ZESU_IN_GATE:-}" ] || [ "$MODULE_LIMIT_GIB" != "$memory" ] ||
         [ "${ZESU_PROOF_CPU_LIMIT:-}" != unlimited ] || [ "${ZESU_PROBE_ISSUE:-}" != 10 ]; then
        echo "resource guard: probe requires issue10, its declared memory fence, and unlimited CPU outside gates" >&2
        return 2
      fi ;;
    *) echo "resource guard: invalid diagnostic probe flag" >&2; return 2 ;;
  esac
}

run_scope() {
  local name=$1 cpu=${ZESU_PROOF_CPU_LIMIT:-2400}; shift
  validate_probe_scope || return $?
  if [ "${1:-}" = "--cpu" ]; then
    cpu=${2:-}; shift 2
    if diagnostic_probe; then
      [ "$cpu" = unlimited ] || { echo "resource guard: probe CPU must be unlimited" >&2; return 2; }
    else
      [[ "$cpu" =~ ^[1-9][0-9]*$ ]] || { echo "resource guard: invalid CPU limit" >&2; return 2; }
    fi
  fi
  [ "${1:-}" = "--" ] && shift
  # An admitted launch must drain before a later gate can acquire its lock.
  if ! reservation_path "${ZESU_COQC_RESERVATION:-}"; then
    wait_for_gate
    guard_wait || return $?
  fi
  ensure_workload_parent || return $?
  local status reservation="${ZESU_COQC_RESERVATION:-}" owned=0 child="" slice
  # Writers never enter a gate or batch aggregate.
  if [ -n "$WRITER_ID" ]; then
    if [ -n "${ZESU_IN_BATCH:-}" ] ||
       { [[ "$(cat /proc/$$/cgroup)" == *"/zesuaggregate"*".slice/"* ]] ||
         [[ "$(cat /proc/$$/cgroup)" == *"/zesuworkloads-aggregate"*".slice/"* ]]; }; then
      echo "resource guard: writer controller must start outside the batch aggregate" >&2
      return 2
    fi
    slice=$WORKLOAD_PARENT_SLICE
  else slice=$(aggregate_slice) || return $?; fi
  if [ -z "$reservation" ]; then
    reservation=$(reserve_coqc $$) || return $?
    owned=1
  fi
  if ! confirm_coqc "$reservation"; then
    [ "$owned" = 0 ] || release_coqc "$reservation"
    return 3
  fi
  # Only scope-exec sets this token after systemd creates the job fence.
  if [ "${ZESU_COQC_SCOPE:-}" = "$reservation" ]; then
    verify_workload_ancestor || return $?
    mark_coqc "$reservation" "$BASHPID" || return $?
    register_run_actor || return $?
    exec "$@"
  fi
  local unit="${SCOPE_PREFIX}-${name}-$$-${RANDOM}"
  if [ -n "$WRITER_ID" ]; then
    unit="${SCOPE_PREFIX}-writer-${WRITER_ID}-${name}-$$-${RANDOM}"
  fi
  if diagnostic_probe; then
    if ! mark_probe_scope "$reservation" "$unit.scope"; then
      [ "$owned" = 0 ] || release_coqc "$reservation"
      return 2
    fi
  fi
  cleanup_scope() {
    if [ -n "$child" ] && kill -0 "$child" 2>/dev/null; then
      stop_scope "$unit.scope" controller-cleanup 2>/dev/null || true
      kill "$child" 2>/dev/null || true
      wait "$child" 2>/dev/null || true
    fi
    [ "$owned" = 0 ] || release_coqc "$reservation"
  }
  trap cleanup_scope EXIT
  trap 'exit 143' TERM
  trap 'exit 130' INT
  ZESU_SCOPE_CPU="$cpu" ZESU_SCOPE_UNIT="$unit.scope" systemd-run --user --scope --quiet --unit="$unit" --slice="$slice" \
    -p "MemoryMax=${MODULE_LIMIT_GIB}G" -p MemorySwapMax=0 -- \
    $(io_class) "$(realpath "$0")" scope-exec "$reservation" -- "$@" &
  child=$!
  wait "$child"
  status=$?
  child=""
  cleanup_scope
  trap - EXIT TERM INT
  return "$status"
}

run_batch() {
  if [ -n "$WRITER_ID" ]; then
    echo "resource guard: writers must use compiler admission or a guarded scope" >&2
    return 2
  fi
  local name=$1; shift
  [ "${1:-}" = "--" ] && shift
  # Nested make wrappers reuse the aggregate created by their parent.
  if [ -n "${ZESU_IN_BATCH:-}" ]; then
    verify_workload_ancestor || return $?
    guard_wait || return $?
    aggregate_slice >/dev/null || return $?
    exec "$@"
  fi
  wait_for_gate
  guard_wait || return $?
  ensure_workload_parent || return $?
  local marker="" status child=""
  if [ -z "${ZESU_IN_GATE:-}" ]; then
    until marker=$(admit_launch); do wait_for_gate; done
  fi
  local unit="${SCOPE_PREFIX}-batch-${name}-$$"
  local slice="zesuworkloads-aggregate${UID}p$$r${RANDOM}.slice"
  local limit=$BATCH_LIMIT
  if [ -n "${ZESU_IN_GATE:-}" ] || [ "${ZESU_IO:-batch}" = gate ]; then limit=$GATE_LIMIT; fi
  # Cap the aggregate before either its parent or a compiler starts.
  if ! systemctl --user set-property --runtime "$slice" "MemoryMax=$limit" MemorySwapMax=0; then
    stop_scope "$slice" aggregate-setup-failure 2>/dev/null || true
    systemctl --user revert "$slice" 2>/dev/null || true
    [ -z "$marker" ] || rm -f "$marker"
    return 2
  fi
  cleanup_batch() {
    local stopped=0
    if stop_scope "$slice" aggregate-cleanup 2>/dev/null; then
      stopped=1
      release_aggregate_reservations "$slice"
    fi
    if [ -n "$child" ] && kill -0 "$child" 2>/dev/null; then
      kill "$child" 2>/dev/null || true
      wait "$child" 2>/dev/null || true
    fi
    if [ "$stopped" = 1 ]; then
      systemctl --user revert "$slice" 2>/dev/null || return 2
      [ -z "$marker" ] || rm -f "$marker"
    else
      echo "resource guard: aggregate stop failed; its memory fence remains" >&2
      return 2
    fi
  }
  trap cleanup_batch EXIT
  trap 'exit 143' TERM
  trap 'exit 130' INT
  echo "$unit.scope" >> "$REGISTRY"
  # Remove private Dune headers before a completed batch returns to its caller.
  env ZESU_IN_BATCH=1 ZESU_AGGREGATE_SLICE="$slice" ZESU_AGGREGATE_LIMIT="$limit" ZESU_BATCH_UNIT="$unit.scope" \
    systemd-run --user --scope --quiet --unit="$unit" --slice="$slice" \
    -p "MemoryMax=$limit" -p MemorySwapMax=0 -- $(io_class) \
    "$(realpath "$0")" batch-exec -- \
    python3 "$(dirname "$(realpath "$0")")/dune_trace_guard.py" --canonical-build-dir -- "$@" &
  child=$!
  wait "$child"
  status=$?
  child=""
  cleanup_batch || status=2
  trap - EXIT TERM INT
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
  local peak holder coqc
  coqc=$(coqc_count) || return $?
  peak=$(cat "$PEAK" 2>/dev/null); peak=${peak:-0}
  holder=$(lock_live 2>/dev/null) || holder=none
  printf 'guard: policy %s; available %s GiB; job %s GiB; used %s GiB (used-policy launch <%s, hold %s, kill %s); coqc %s machine-wide; load5 %s; blocked %s; jobs %s; batch peak %d GiB; gate lock %s; holds %s; guard kills %s\n' \
    "$MEMORY_POLICY" "$(available_gib)" "$MODULE_LIMIT_GIB" "$(used_gib)" "$LAUNCH_GIB" "$HOLD_GIB" "$KILL_GIB" "$coqc" "$(load_five)" "$(blocked_count)" "$(guard_jobs)" \
    $(( peak / GIB )) "$holder" \
    "$(grep -c ' HOLD ' "$LOG" 2>/dev/null | head -1)" \
    "$(grep -c ' KILL ' "$LOG" 2>/dev/null | head -1)"
  python3 "$PROM" now || echo "prometheus unavailable; no machine figures"
}

# Apply proof limits inside the admitted scope, before the command starts.
apply_scope_limits() {
  ulimit -s unlimited || return $?
  ulimit -t "${ZESU_SCOPE_CPU:-${ZESU_PROOF_CPU_LIMIT:-2400}}" || return $?
}

prune_scope_registry

# Register a standalone batch or scope before its detached systemd actors start.
# Nested scopes inherit the exact run ID. A new run never implies replacement.
case "${1:-report}" in
  batch|scope)
    if [ -z "${ZESU_RUN_ID:-}" ] && [ -z "${ZESU_IN_BATCH:-}${ZESU_IN_GATE:-}" ]; then
      registry=${ZESU_RUN_REGISTRY_TOOL:-$(dirname "$(realpath "$0")")/run_registry.py}
      registry_args=(run --kind "stock-$1" --owner "${COORD_AGENT:-$USER}")
      if [ -n "${ZESU_SUPERSEDES_RUN:-}" ]; then
        registry_args+=(--supersedes "$ZESU_SUPERSEDES_RUN")
      fi
      exec "${ZESU_REGISTRY_PYTHON:-python3}" "$registry" "${registry_args[@]}" -- "$(realpath "$0")" "$@"
    fi ;;
esac

case "${1:-report}" in
  parent-check) verify_workload_ancestor ;;
  parent-slice) ensure_workload_parent && aggregate_slice ;;
  parent-exec)
    verify_workload_ancestor || exit $?
    shift; [ "${1:-}" = -- ] && shift
    exec "$@" ;;
  parent-setup) ensure_workload_parent ;;
  gate-module-limit)
    if [[ ! "$GATE_MODULE_LIMIT_GIB" =~ ^([6-9]|[12][0-9]|3[0-2])$ ]]; then
      echo "compiler gate memory limit must be an integer from 6 through 32 GiB" >&2
      exit 2
    fi
    echo "$GATE_MODULE_LIMIT_GIB" ;;
  jobs)   guard_jobs ;;
  coqc-count)
    if [ "${2:-}" = nonwriter ]; then nonwriter_coqc_count; else coqc_count; fi ;;
  gate-jobs) gate_jobs "${2:-check-iris}" ;;
  reset-peak) echo 0 > "$PEAK" ;;
  peak)   awk '{printf "%d", $1 / 1073741824}' "$PEAK" 2>/dev/null; echo ;;
  wait)   guard_wait ;;
  reserve-coqc) reserve_coqc "$2" ;;
  confirm-coqc) confirm_coqc "$2" ;;
  mark-coqc) mark_coqc "$2" "$3" && register_run_actor "$3" ;;
  release-coqc) release_coqc "$2" ;;
  watch)  guard_watch ;;
  scope)  shift; run_scope "$@" ;;
  scope-exec)
    verify_workload_ancestor || exit $?
    validate_probe_scope || exit $?
    if diagnostic_probe && [ "${ZESU_SCOPE_CPU:-unlimited}" != unlimited ]; then
      echo "resource guard: probe CPU must be unlimited" >&2; exit 2
    fi
    token=$2; shift 2; [ "${1:-}" = -- ] && shift
    [ -z "${ZESU_SCOPE_UNIT:-}" ] || register_scope "$ZESU_SCOPE_UNIT"
    confirm_coqc "$token" || exit $?
    mark_coqc "$token" $$ || exit $?
    export ZESU_COQC_RESERVATION="$token" ZESU_COQC_SCOPE="$token"
    apply_scope_limits || exit $?
    register_run_actor || exit $?
    exec "$@" ;;
  batch-exec)
    verify_workload_ancestor || exit $?
    shift; [ "${1:-}" = -- ] && shift
    register_run_actor || exit $?
    exec "$@" ;;
  batch)  shift; run_batch "$@" ;;
  locked) shift; run_locked "$@" ;;
  lock-status) lock_live || echo "no gate lock" ;;
  # A gate script passes its own PID, so the lock lives as long as the gate.
  lock-want) lock_acquire "$3" "$2" ;;
  lock-hold) lock_hold "$2" ;;
  lock-release) lock_release "$2" ;;
  hold)   r=$(hold_reason) || exit $?; echo "${r:-none}" ;;
  window) shift; python3 "$PROM" window "$@" ;;
  report) report ;;
  *) echo "usage: $0 {jobs|gate-jobs [TARGET]|gate-module-limit|native-limit|wait|reserve-coqc PID|confirm-coqc TOKEN|mark-coqc TOKEN PID|release-coqc TOKEN|watch|scope NAME [--cpu SECONDS] -- CMD|batch NAME -- CMD|locked NAME -- CMD|lock-status|lock-want PID HOLDER|lock-hold PID|lock-release PID|hold|report|window ARGS|peak|reset-peak}" >&2; exit 2 ;;
esac
