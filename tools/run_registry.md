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
Options before NAME: `--dir DIR` (run and working directory), `--log FILE`, `--owner NAME`, `--memory GIB`,
`--allow-duplicate`, `--heavy`.

`--heavy` marks a gate, bank build, or column batch. Before it starts, the launcher waits until the user
slice (`/sys/fs/cgroup/user.slice/user-$UID.slice`, or `$ZESU_CGROUP_ROOT/...`) has `anon + shmem`
(memory.stat) under 140 GiB and `memory.pressure` `some avg60` under 5 %. Page cache does not count.
While it waits it prints at most one `notice:` line a minute and rechecks every 15 s
(`ZESU_HEAVY_POLL_SECONDS`). Unreadable slice files are an error (exit 2). The resource guard's own
admission (hold, room, job count) counts the same `anon + shmem`; its kill check still counts
`memory.current` less file LRU and reclaimable slab.

The launcher starts the command in a new session whose parent is init, inside its own
`systemd-run --user --scope` unit `zesubg-<owner>-<name>-<UTC>-<hex>.scope`.
The job is never a child of the caller, so a kill by the caller's parent PID cannot reach it.
The run records owner, unit, scheduler and job PIDs, command, run directory, and log.
The job does not inherit `ZESU_RUN_ID`; guard batches it starts register their own runs.
It gets `ZESU_OWNER` (the run's owner) and `ZESU_PARENT_RUN_ID` (the run's ID) instead.

Before it starts anything, the launcher scans the command line, every script it names, and the
scripts those name (four levels) with `tools/kill_scan.py`.
It refuses with exit 3 when an executable line kills by process name, by a pgrep match, or by
the parent PID `$$`. The message names the file, the line, and the safe form.
The proof hygiene check applies the same scan to committed `tools/` scripts.

`stop` records `stop_requested_ns`, closes the recorded actors, and then kills and stops the
run's unit, which ends any process that left the process tree.

## Owner, worktree and module

Every run records `owner`, `worktree` (the git top level of its working directory) and `modules`
(the module/caller files: payload arguments that name existing non-executable files, e.g. `col.py`
in `python3 col.py`). Without `--owner`, `run` and guard `batch`/`scope` take the owner from, in
order: `ZESU_OWNER`; the owner of the enclosing `tools/bg` run (`ZESU_PARENT_RUN_ID`); the
worktree's branch; the user name. A run inside a `tools/bg` run records `parent_run_id`.
`tools/bg` without `--owner` uses `ZESU_OWNER`, `COORD_AGENT`, the omp session, else the user ID.
`run_registry.py list` (and `tools/bg list`) print `worktree=` and `module=` after each run.

## Duplicate launches

A launch whose identity matches a live registered run is refused with exit 6, before anything starts.
The message starts `refused: duplicate launch:` and names the live run ID and `tools/bg stop <id>`.
Identity survives retries because it never includes the run ID or time:

- `tools/bg` / `launch`: owner and NAME.
- guard `batch` / `scope` (kinds `stock-batch`, `stock-scope`): owner, NAME, the module/caller files
  (payload arguments that name existing files, without the interpreter), and the bank dir (the working
  directory).

The check runs under the registry's transition lock in `run`, so two concurrent launches cannot both
start. After the live run ends (or `tools/bg stop`), the same launch succeeds. `--allow-duplicate`
(`tools/bg --allow-duplicate NAME ...`, `resource_guard.sh batch --allow-duplicate NAME -- ...`, or
`ZESU_ALLOW_DUPLICATE=1` for the guard) starts it anyway.

## Message prefixes and exit codes

Registry and guard messages that do not stop the run start with `notice:`; refusals start with
`refused:` and exit nonzero. Scripts decide by exit status, never by grepping for "refuse".
Launch exit codes: 0 started; 2 invalid use or registry error; 3 unsafe-kill refusal or build-budget
refusal; 5 guard claim above the module fence; 6 duplicate launch. The unified ledger's hold
(`notice: unified memory ledger holds the reservation`) is not a refusal: the guard waits and retries.

## Signal deaths

The reaper runs at every registration, every active listing, and `run_registry.py reap`.
It writes one entry to `signal-deaths.jsonl` in the store for each run that ended without a
stop record in one of these ways:

- by a signal (the scheduler was signalled, or the command died by a signal);
- with exit status 129, 130, 137, or 143 (a shell reporting a child killed by a signal);
- with every actor dead while the row still says `running` (the scheduler was killed).

Each entry names the run, owner, kind, unit, worktree, modules, parent run, signal, sender, end
time, and cause. The sender comes from the signal's siginfo, read while the scheduler waits: for a
systemd stop, `systemd <user|system> stop job <id> for <unit>`; for a process, its PID, name and
command line; `unknown` when the scheduler died without recording one (SIGKILL, or a signal before
the command started).
The cause is `parent stopped` when the run's parent `tools/bg` run got a registry stop within 5 s
of the run's end; such an entry is not a signal death and the watchdog does not post it.
Otherwise the cause is `memory fence` when the guard's fence-kill ledger
(`$XDG_RUNTIME_DIR/zesu-guard/fence-kills.jsonl`) has a kill with the run's ID or unit, or when a
launched run's scope recorded an OOM kill under `--memory`; otherwise it is `unknown`.
Fence-kill rows carry the `ZESU_RUN_ID` of the run that started the guard.

`run_registry.py watchdog --status docs/ai/STATUS.md` reaps and appends one line per new entry.
Its first pass records the ledger position and posts nothing, so historical entries stay in
the ledger only. `make install-run-watchdog` installs and starts a user timer that runs it every
two minutes from the checkout that runs the target.

The timer passes `--follow-main <that checkout>` (`.worktrees/ops-tools`), so the tools checkout follows
main by itself: at the start of each run the watchdog fetches main into `origin/main` and, when the
checkout has no tracked changes and its HEAD is an ancestor of origin/main, runs
`git checkout --detach origin/main`. The user service has no SSH agent, so a GitHub SSH origin is
fetched over HTTPS with the gh credential helper (`gh auth git-credential`). Each move is printed
(journal) and appended to `<store>/follow-main.log`. A checkout that does not follow main (failed
fetch, tracked changes, local commits, or a refused checkout) is posted to STATUS.md once per distinct
reason (marker `<store>/follow-main.held`, cleared when it moves again), and the watchdog exits 1 after
its reap, so `systemctl --user status zesu-run-watchdog` shows the unit failed. Untracked files such as
`tools/bg` logs do not hold it.

## Stalled gates

Each watchdog pass also reports gates that finished with nothing after them. For each ITEM.json branch,
it takes the branch's newest registered run (by registration time). When that run's dir has `gates.out` or
`GATES-DONE` last modified over 30 minutes ago, it asks `gh pr list --head <branch> --state all`. With no
merged PR and no open PR updated since the gates finished, it appends
`gates done at <T> for branch <B>; no PR/merge since (run ..., owner ..., <run dir>).` to STATUS.md, once per
branch (marker `<store>/gates-stall.posted`). A failed PR lookup posts nothing and is retried next pass.

## Fixture verification

```sh
python3 -B -m unittest -v tools.test_run_registry tools.test_run_launch
ZESU_RUN_LAUNCH_LIVE=1 python3 -B -m unittest -v tools.test_run_launch   # adds a real user scope
```

The suite repeats actor, stop, release, and supersession tests in both formats.
Additional controls test migration refusal, partial migration, targeted updates, and discovery timing.
`tools.test_run_launch` tests launch outside the caller's tree, refusal of unsafe kills, the
signal-death ledger, the fence label, and the watchdog.
