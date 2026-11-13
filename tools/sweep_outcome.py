"""Outcome of one guarded block compile in a measurement sweep: closed, open, killed or stopped.

A block whose scope ends at its memory fence or at the account backstop measured nothing. It is
"killed", not "open": the compile returns 137 or 143 and its measure wrapper writes no data, and
the guard writes "memory fence kill" to the block's log at a fence kill. Counting such blocks as
open hid every fence kill of the 2026-11-12 held-out columns.

usage: sweep_outcome.py SWEEP_JSONL...  (recount recorded rows; a later row for a case replaces an earlier one)
"""
import json
import sys

KILL_CODES = (137, 143)  # SIGKILL (fence, backstop), SIGTERM (scope stop)
FENCE_KILL_MARK = 'memory fence kill'


def outcome(returncode, measured, stalled=False, log_text=''):
    """Classify one block. measured: the measure wrapper wrote its data. stalled: the sweep's
    wall rule stopped the block. log_text: the block's compile log."""
    if stalled:
        return 'stopped'
    if returncode == 0:
        return 'closed'
    if FENCE_KILL_MARK in log_text or (returncode in KILL_CODES and not measured):
        return 'killed'
    return 'open'


def row_outcome(row):
    """Outcome of a recorded sweep row (status from older sweeps is ignored)."""
    return outcome(row.get('returncode'), row.get('cpu_seconds') is not None, bool(row.get('stall')))


def recount(lines):
    rows = {}
    for line in lines:
        if line.strip():
            row = json.loads(line)
            rows[row['case']] = row
    counts = {'closed': 0, 'open': 0, 'killed': 0, 'stopped': 0}
    for row in rows.values():
        counts[row_outcome(row)] += 1
    return counts


def main(paths):
    for path in paths:
        with open(path) as handle:
            print(path, json.dumps(recount(handle)))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
