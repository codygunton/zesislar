"""Outcome of one guarded block compile in a measurement sweep: closed, uncertified, open, killed,
shared-kill or stopped.

"closed" needs a closure certificate (tools/closure_cert.py, verdict CLOSED in the row). A row with
returncode 0 and no certificate is "uncertified": exit 0 is not a closure. On 2026-11-16 a sample
wrapper printed its own exit (`RUN-DONE rc=0`) for two incomplete proofs; rows now carry coqc's
own status from measure.json and the certificate verdict.

A block whose scope ends at its memory fence or at the account backstop measured nothing. It is
"killed", not "open": the compile returns 137 or 143 and its measure wrapper writes no data, and
the guard writes "memory fence kill" to the block's log at a fence kill. Counting such blocks as
open hid every fence kill of the 2026-11-12 held-out columns.

A "shared-kill" block was killed in its batch's full memory aggregate below its own fence (the
guard names it a shared-slice memory kill). It measured nothing about its own memory either.

usage: sweep_outcome.py SWEEP_JSONL...  (recount recorded rows; a later row for a case replaces an earlier one)
"""
import json
import sys

KILL_CODES = (137, 143)  # SIGKILL (fence, backstop), SIGTERM (scope stop)
FENCE_KILL_MARK = 'memory fence kill'
SHARED_KILL_MARK = 'shared-slice memory kill'


def outcome(returncode, measured, stalled=False, log_text='', certified=False):
    """Classify one block. measured: the measure wrapper wrote its data. stalled: the sweep's
    wall rule stopped the block. log_text: the block's compile log. certified: a CLOSURE.json exists."""
    if stalled:
        return 'stopped'
    if certified:
        return 'closed'
    if returncode == 0:
        return 'uncertified'
    if SHARED_KILL_MARK in log_text:
        return 'shared-kill'
    if FENCE_KILL_MARK in log_text or (returncode in KILL_CODES and not measured):
        return 'killed'
    return 'open'


def row_outcome(row):
    """Outcome of a recorded sweep row (status from older sweeps is ignored)."""
    return outcome(row.get('returncode'), row.get('cpu_seconds') is not None, bool(row.get('stall')),
                   certified=row.get('verdict') == 'CLOSED')


def recount(lines):
    rows = {}
    for line in lines:
        if line.strip():
            row = json.loads(line)
            rows[row['case']] = row
    counts = {'closed': 0, 'uncertified': 0, 'open': 0, 'killed': 0, 'shared-kill': 0, 'stopped': 0}
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
