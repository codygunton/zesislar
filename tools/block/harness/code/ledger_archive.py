"""Move closed ledger records out of the hot LEDGER.json into an archive.

Every admission parses and rewrites LEDGER.json under the global guard
mutex. On 2026-11-10 it held 21.8 MB, mostly closed history, and the mutex
was 61-96% busy. The archive keeps every record as audit evidence (PR #149
reads it through ``lookup``) in append-only JSON lines, rotated by size.
The hot ledger keeps live claims and open records only.

Only records that no live owner can still query move, so an older guard
that reads the hot ledger without this module still finds every record
it can need: released tokens whose markers are gone, gates whose owners
ended and that no recent gate-exit measurement names, ended entry runs,
and collections that no tool reads.
"""
import json
import os
from pathlib import Path
import time

SCHEMA = 'zesu.ledger-archive.v1'
ROTATE_BYTES = 64 * 1024 * 1024
COMPACT_ABOVE_BYTES = 4 * 1024 * 1024
COMPACT_INTERVAL_NS = 600 * 10**9
RECENT_GATE_EXITS = 20
# Top-level collections that no tool reads (test_ledger_archive checks this).
DEAD_COLLECTIONS = frozenset({
    'cleanup_compiler_completions', 'cleanup_compiler_submissions', 'claim_admissions',
    'claim_closures', 'claim_growth', 'entry_diagnostic_growth', 'first_split',
    'historical_block8_adoptions', 'explicit_ended_claim_reviews', 'gate_allocations',
    'loop_claim_growth_receipt', 'previous_region_releases', 'run_B_build_closures',
    'sequential_claim_note', 'sequential_closed_and_released', 'sequential_sampled_peak_bytes',
    'sequential_stop_receipt', 'duplicate_repro_admissions', 'duplicate_repro_releases',
    'h0_activation_trace_admissions', 'h0_activation_trace_continuations',
    'h0_activation_trace_releases', 'infra_a_exact_admissions', 'infra_a_normalizer_admissions',
    'r1_A_output_alias_compliance_admissions', 'r1_compliance_admissions', 'r1_e845_admissions',
    'r1_exact_recovery_admissions', 'r1_output_alias_admissions', 'r1_paired_profile_admissions',
    'r1_paired_profile_final_releases', 'r1_paired_profile_preflight_releases',
    'r1_paired_profile_readmissions', 'r1_paired_profile_runtime003_releases',
    's1_accessor_admissions', 's1_checked_reuse_admissions', 's1_collector_admissions',
    's1_context129_partial_releases', 's1_exact_admissions', 's1_history_admissions',
    's1_native_admissions', 's1_parent_assembly_admissions', 's1_row5_failed_batch_releases',
    's1_run_A_startup_releases', 's1_run_B_closures', 's1_run_B_stream_stop_releases',
    's1_search_admissions', 's1_stall_admissions', 's1_standalone179_admissions',
    's1_state_admissions', 's1_state_controls_admissions', 's1_state_controls_releases',
    's1_target_only_admissions', 's1_unique_observer_admissions', 's1_unique_observer_releases',
})
GATE_FIELDS = ('correctness_gate_admissions', 'correctness_gate_releases', 'correctness_gate_owners',
               'correctness_gate_cold_claims', 'claim_locations', 'claim_fences')
ENTRY_FIELDS = ('entry_pilot_outside_owners', 'entry_pilot_outside_releases', 'claim_locations',
                'claim_fences')


def directory(ledger):
    return Path(ledger).with_name('LEDGER-archive')


def _files(folder):
    return sorted(folder.glob('archive-*.jsonl'))


def append(ledger, rows):
    """Append rows durably before the hot ledger drops them (caller holds the lock)."""
    if not rows:
        return
    folder = directory(ledger)
    folder.mkdir(mode=0o700, exist_ok=True)
    files = _files(folder)
    current = files[-1] if files else folder / 'archive-000001.jsonl'
    if current.exists() and current.stat().st_size >= ROTATE_BYTES:
        current = folder / f'archive-{int(current.stem.split("-")[1]) + 1:06d}.jsonl'
    created = not current.exists()
    payload = ''.join(json.dumps(row, separators=(',', ':'), sort_keys=True) + '\n' for row in rows)
    descriptor = os.open(current, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    try:
        os.write(descriptor, payload.encode())
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    if created:
        handle = os.open(folder, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(handle)
        finally:
            os.close(handle)


def lookup(ledger, collection, key):
    """Return the newest archived value of one record, or None (rare paths only)."""
    for path in reversed(_files(directory(ledger))):
        found = None
        with open(path) as stream:
            for line in stream:
                if f'"{key}"' not in line:
                    continue
                row = json.loads(line)
                if row.get('collection') == collection and row.get('key') == key:
                    found = row['value']
        if found is not None:
            return found
    return None


def _ended(ended, reader, owner):
    try:
        return ended(reader, owner)
    except (KeyError, TypeError, ValueError):
        return False


def due(ledger, data, now_ns=None):
    now_ns = time.time_ns() if now_ns is None else now_ns
    try:
        size = Path(ledger).stat().st_size
    except OSError:
        return False
    marker = data.get('ledger_archive', {})
    return size > COMPACT_ABOVE_BYTES and now_ns - marker.get('compacted_ns', 0) > COMPACT_INTERVAL_NS


def compact(ledger, data, reader, ended, now_ns=None):
    """Move closed records to the archive; return the number of records moved."""
    now_ns = time.time_ns() if now_ns is None else now_ns
    rows = []

    def move(collection, key):
        value = data[collection].pop(key)
        rows.append({'collection': collection, 'key': key, 'value': value, 'archived_ns': now_ns})

    for name in sorted(DEAD_COLLECTIONS & set(data)):
        rows.append({'collection': name, 'key': None, 'value': data.pop(name), 'archived_ns': now_ns})
    fixed = data.get('fixed_claims', {})
    owners = data.get('shell_claim_owners', {})
    # Released tokens: their documents are already in the shell archive; move the index.
    for key in [key for key in data.get('shell_archive', {}) if fixed.get(key, 0) == 0 and key not in owners]:
        move('shell_archive', key)
        if key in fixed:
            move('fixed_claims', key)
    recent = {row.get('claim_key') for row in data.get('gate_exit_peaks', [])[-RECENT_GATE_EXITS:]
              if isinstance(row, dict)}
    for key, release in list(data.get('correctness_gate_releases', {}).items()):
        owner = data.get('correctness_gate_owners', {}).get(key)
        if (key in recent or fixed.get(key, 0) != 0 or release.get('released') is not True
                or not isinstance(owner, dict) or not _ended(ended, reader, owner)):
            continue
        for field in GATE_FIELDS:
            if key in data.get(field, {}):
                move(field, key)
        if key in fixed:
            move('fixed_claims', key)
    protected = {prior for hold in data.get('legacy_kernel_accounts', {}).values()
                 for prior in hold.get('canonical_owners', {})}
    for key in list(data.get('entry_pilot_outside_releases', {})):
        owner = data.get('entry_pilot_outside_owners', {}).get(key)
        if (key in protected or fixed.get(key, 0) != 0 or not isinstance(owner, dict)
                or not _ended(ended, reader, owner)):
            continue
        for field in ENTRY_FIELDS:
            if key in data.get(field, {}):
                move(field, key)
        if key in fixed:
            move('fixed_claims', key)
    append(ledger, rows)
    marker = data.setdefault('ledger_archive', {'schema': SCHEMA, 'moved_records': 0})
    marker.update(schema=SCHEMA, directory=str(directory(ledger)), compacted_ns=now_ns,
                  moved_records=marker.get('moved_records', 0) + len(rows))
    return len(rows)


def archived_shell_digest(data, key, ledger=None):
    """The released-token document digest, from the hot index or the archive."""
    if key in data.get('shell_archive', {}):
        return data['shell_archive'][key]
    if ledger is None or 'ledger_archive' not in data:
        return None
    return lookup(ledger, 'shell_archive', key)
