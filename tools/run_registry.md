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

## Fixture verification

```sh
python3 -B -m unittest -v tools.test_run_registry
```

The suite repeats actor, stop, release, and supersession tests in both formats.
Additional controls test migration refusal, partial migration, targeted updates, and discovery timing.
