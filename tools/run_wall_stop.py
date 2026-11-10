"""Stop the registered run that contains a process.

A guard scope inside a batch registers no run of its own: the run registry
lists only the batch. A wall-time stop of one scope therefore finds the
batch run whose process tree holds the scope's process and stops that run
with Registry.stop, the supported stop path. A caller inside that run (a
sweep driver is the batch command) cannot stop it in place, because the
stop freezes every actor of the run. It hands the stop to a detached
process outside the run's process tree instead.

Usage: run_wall_stop.py --pid PID [--store DIR]
"""
import argparse
import json
import os
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_registry as R


def run_containing(registry, pid):
    """Return the ID of the active run whose process tree holds pid, or None."""
    target = R.identity(pid)
    if target is None:
        return None
    for row in registry.active():
        if any(R.actor_key(actor) == R.actor_key(target)
               for actor in R.descendants([row['scheduler']] + row['jobs'])):
            return row['id']
    return None


def detach_stop(registry, run_id):
    """Run Registry.stop in a process whose parent is outside the run."""
    child = os.fork()
    if child == 0:
        try:
            os.setsid()
            if os.fork() != 0:
                os._exit(0)
            os.execv(sys.executable, [sys.executable, '-B', str(Path(R.__file__).resolve()),
                                      '--store', str(registry.directory), 'stop', '--run-id', run_id])
        finally:
            os._exit(127)
    os.waitpid(child, 0)


def stop_containing(pid, registry):
    """Stop the run that holds pid. Return (run ID or None, how)."""
    run_id = run_containing(registry, pid)
    if run_id is None:
        return None, 'no_active_run'
    if run_containing(registry, os.getpid()) == run_id:
        detach_stop(registry, run_id)
        return run_id, 'detached'
    registry.stop(run_id)
    return run_id, 'stopped'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pid', type=int, required=True)
    parser.add_argument('--store', type=Path)
    options = parser.parse_args()
    registry = R.Registry(options.store or R.default_store())
    run_id, how = stop_containing(options.pid, registry)
    print(json.dumps({'run_id': run_id, 'how': how}))
    return 0 if run_id is not None else 1


if __name__ == '__main__':
    raise SystemExit(main())
