# Run registry storage

Existing stores and new stores use `zesu.run-registry.v1` by default.
Routine descendant discovery runs at most once every three seconds.
Command completion and stop operations discover descendants immediately.
An unchanged actor set does not cause a write.
Process-state changes alone do not change a recorded actor identity.
Signal delivery still checks the live PID and start ticks through a pidfd.

The optional v2 format stores each run in `runs.d/<sha256(run_id)>.json`.
An update reads and replaces only that run's file.
Explicit history and active listings still read all run files.
Each replacement uses an atomic rename and synchronizes the file and its directory.
Both formats use the same state, transition, and claim-release locks.
The signal handler reads atomic files without taking the state lock.
This prevents a signal from blocking on its interrupted writer's lock.

## Explicit migration

Migration requires an explicit store path:

```sh
python3 tools/run_registry.py --store /absolute/owned/store migrate-per-run
```

This command does not run during ordinary registration or execution.
The operator must update every registry writer before migration.
The command takes the transition lock and the state lock.
It refuses migration when a recorded actor remains live or a claim remains pending.
It copies the closed records and retains a v1 snapshot.
It synchronizes the published run directory before it publishes the protocol marker.
It then replaces `runs.json` with a v2 protocol marker.
Old v1 writers reject that marker before they update a record.
They cannot continue writing the v1 snapshot.

A failure before marker publication leaves v1 authoritative.
The command retains partial files for inspection.
An existing `runs.d` directory blocks a later migration attempt.
The operator must inspect that directory before any recovery action.
The command does not merge partial records or activate them automatically.
Registry operations refuse a v2 marker without its run directory.

No live-store migration is part of the fixture tests or source preparation.

## Launching long jobs

```sh
tools/bg NAME [--] COMMAND [ARGS...]      # prints the run ID; output in ./NAME.log
tools/bg stop RUN_ID                      # or: tools/run_registry.py stop RUN_ID
tools/bg list                             # active runs
```

`tools/bg` runs `run_registry.py launch --name NAME -- COMMAND...`.
Options before NAME: `--dir DIR` (run and working directory), `--log FILE`, `--owner NAME`, `--memory GIB`.
The launcher starts the command in a new session whose parent is init, inside its own
`systemd-run --user --scope` unit `zesubg-<owner>-<name>-<UTC>-<hex>.scope`.
The job is never a child of the caller, so a kill by the caller's parent PID cannot reach it.
The run records owner, unit, scheduler and job PIDs, command, run directory, and log.
The job does not inherit `ZESU_RUN_ID`; guard batches it starts register their own runs.
It gets `ZESU_BG_RUN_ID` instead.

Before it starts anything, the launcher scans the command line, every script it names, and the
scripts those name (four levels) with `tools/kill_scan.py`.
It refuses with exit 3 when an executable line kills by process name, by a pgrep match, or by
the parent PID `$$`. The message names the file, the line, and the safe form.
The proof hygiene check applies the same scan to committed `tools/` scripts.

`stop` records `stop_requested_ns`, closes the recorded actors, and then kills and stops the
run's unit, which ends any process that left the process tree.

## Signal deaths

The reaper runs at every registration, every active listing, and `run_registry.py reap`.
It writes one entry to `signal-deaths.jsonl` in the store for each run that ended without a
stop record in one of these ways:

- by a signal (the scheduler was signalled, or the command died by a signal);
- with exit status 129, 130, 137, or 143 (a shell reporting a child killed by a signal);
- with every actor dead while the row still says `running` (the scheduler was killed).

Each entry names the run, owner, kind, unit, signal, end time, and cause.
The cause is `memory fence` when the guard's fence-kill ledger
(`$XDG_RUNTIME_DIR/zesu-guard/fence-kills.jsonl`) has a kill with the run's ID or unit, or when a
launched run's scope recorded an OOM kill under `--memory`; otherwise it is `unknown`.
Fence-kill rows carry the `ZESU_RUN_ID` of the run that started the guard.

`run_registry.py watchdog --status docs/ai/STATUS.md` reaps and appends one line per new entry.
Its first pass records the ledger position and posts nothing, so historical entries stay in
the ledger only. `make install-run-watchdog` installs and starts a user timer that runs it every
two minutes from the checkout that runs the target.

The timer passes `--follow-main <that checkout>` (`.worktrees/ops-tools`), so the tools checkout follows
main by itself: at the start of each run the watchdog fetches origin and, when the checkout has no
tracked changes and its HEAD is an ancestor of origin/main, runs `git checkout --detach origin/main`.
Each move is printed (journal) and appended to `<store>/follow-main.log`. A checkout held by tracked
changes, local commits, or a refused checkout is posted to STATUS.md once (marker
`<store>/follow-main.held`, cleared when it moves again). Untracked files such as `tools/bg` logs
do not hold it.

## Fixture verification

```sh
python3 -B -m unittest -v tools.test_run_registry tools.test_run_launch
ZESU_RUN_LAUNCH_LIVE=1 python3 -B -m unittest -v tools.test_run_launch   # adds a real user scope
```

The suite repeats actor, stop, release, and supersession tests in both formats.
Additional controls test migration refusal, partial migration, targeted updates, and discovery timing.
`tools.test_run_launch` tests launch outside the caller's tree, refusal of unsafe kills, the
signal-death ledger, the fence label, and the watchdog.
