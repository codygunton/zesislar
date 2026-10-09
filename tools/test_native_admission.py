"""Check the shared admission helper with fake processes and guard responses."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import native_admission as admission
import test_resource_guard


GUARD = Path(__file__).with_name('resource_guard.sh')


def process(root, pid, name, state='S', *, directory=None, start=42):
    entry = root / (directory or str(pid))
    entry.mkdir()
    (entry / 'comm').write_text(name + '\n')
    (entry / 'status').write_text(f'Name:\t{name}\nState:\t{state}\nPid:\t{pid}\n')
    fields = [state] + ['0'] * 18 + [str(start)]
    (entry / 'stat').write_text(f'{pid} ({name}) ' + ' '.join(fields) + '\n')
    return entry


def observed(count=0):
    return {'child': 'B', 'native_limit': 4,
            'live_interpreters': [{'pid': index + 1, 'comm': 'coqc', 'state': 'S'}
                                  for index in range(count)],
            'owned_sessions_for_child': [], 'compiler_count': count,
            'normal_guard_hold': 'none', 'gate_status': 'no gate lock'}


def probe_policy():
    return {'kind': 'probe', 'cpu_seconds': None, 'wall_seconds': None,
            'memory_kib': 64 * 1024 * 1024, 'optimization_debt': 'issue#10'}


class NativeAdmission(unittest.TestCase):
    def test_limit_query_is_read_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary) / 'absent'
            env = dict(os.environ, ZESU_GUARD_STATE=str(state), ZESU_NATIVE_LIMIT='99')
            result = subprocess.run([str(GUARD), 'native-limit'], env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, '4\n')
            self.assertFalse(state.exists())

    def test_limit_query_rejects_arguments_without_writes(self):
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary) / 'absent'
            result = subprocess.run([str(GUARD), 'native-limit', '8'],
                env=dict(os.environ, ZESU_GUARD_STATE=str(state)), capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertFalse(state.exists())

    def test_all_seven_names(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for pid, name in enumerate(sorted(admission.NAMES), 1):
                process(root, pid, name)
            process(root, 99, 'unrelated')
            self.assertEqual(len(admission.inventory(root)), 7)
            self.assertEqual({row['comm'] for row in admission.inventory(root)}, admission.NAMES)

    def test_zombies_dead_processes_and_duplicate_pids(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            process(root, 1, 'pet')
            process(root, 1, 'pet', directory='01')
            process(root, 2, 'coqc', 'Z')
            process(root, 3, 'rocq', 'X')
            self.assertEqual(admission.inventory(root), [{'pid': 1, 'comm': 'pet', 'state': 'S'}])

    def test_inventory_uses_no_arguments_or_environment(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            process(root, 1, 'pet')
            original = Path.read_text
            def checked(path, *args, **kwargs):
                self.assertIn(path.name, ('comm', 'status'))
                return original(path, *args, **kwargs)
            with patch.object(Path, 'read_text', checked):
                self.assertEqual(len(admission.inventory(root)), 1)

    def test_duplicate_records_do_not_occupy_multiple_slots(self):
        snapshot = observed(3)
        snapshot['live_interpreters'] *= 2
        self.assertIsNone(admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB))
        snapshot['live_interpreters'].append({'pid': 1, 'comm': 'pet', 'state': 'S'})
        with self.assertRaises(ValueError):
            admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB)

    def test_four_arm_limit(self):
        for count in (0, 1, 2, 3):
            self.assertIsNone(admission.reason(observed(count), kind='native', requested_memory_bytes=6 * admission.GIB))
        self.assertIn('four native', admission.reason(observed(4), kind='native', requested_memory_bytes=6 * admission.GIB))

    def test_memory_holds_and_gate_lock_remain_effective(self):
        snapshot = observed()
        for hold in ('memory 180GiB', 'load5 81', 'blocked 17'):
            snapshot['normal_guard_hold'] = hold
            self.assertEqual(admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB), hold)
        snapshot['normal_guard_hold'] = 'none'
        snapshot['gate_status'] = 'state=held'
        self.assertIn('gate', admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB))

    def test_existing_memory_hold_and_compiler_cap(self):
        fixture = test_resource_guard.ResourceGuard()
        script = 'used_gib() { echo 181; }; coqc_count() { echo 0; }; load_five() { echo 0; }; blocked_count() { echo 0; }; hold_reason'
        memory = fixture.run_guard(script)
        self.assertEqual(memory.returncode, 0, memory.stderr)
        self.assertIn('memory', memory.stdout)
        script = 'used_gib() { echo 0; }; coqc_count() { echo 48; }; load_five() { echo 0; }; blocked_count() { echo 0; }; hold_reason'
        compilers = fixture.run_guard(script)
        self.assertEqual(compilers.returncode, 0, compilers.stderr)
        self.assertIn('coqc 48', compilers.stdout)

    def test_helper_keeps_forty_eight_compiler_cap(self):
        snapshot = observed()
        snapshot['compiler_count'] = 48
        self.assertIn('forty-eight', admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB))

    def test_default_memory_policy_remains_six_gib(self):
        self.assertIsNone(admission.reason(observed(), kind='native'))
        self.assertIsNone(admission.reason(observed(), kind='native', requested_memory_bytes=1))
        for requested in (6 * admission.GIB + 1, 9 * admission.GIB,
                          10 * admission.GIB, 12 * admission.GIB, 64 * admission.GIB):
            self.assertIn('six GiB', admission.reason(observed(), kind='native',
                                                    requested_memory_bytes=requested))
        for requested in (0, -1, True, 6.0):
            self.assertIn('positive integer', admission.reason(observed(), kind='native',
                                                              requested_memory_bytes=requested))

    def test_unlimited_issue10_probe_is_admitted(self):
        for kind in ('native', 'mcp'):
            self.assertIsNone(admission.reason(observed(), kind=kind,
                requested_memory_bytes=64 * admission.GIB, budget_policy=probe_policy()))

    def test_probe_rejects_changed_or_missing_policy_fields(self):
        policy = probe_policy()
        for field, value in (('kind', 'cpu'), ('cpu_seconds', 14400),
                             ('cpu_seconds', 0), ('wall_seconds', 300),
                             ('memory_kib', 9 * 1024 * 1024),
                             ('optimization_debt', 'issue#11')):
            with self.subTest(field=field, value=value):
                self.assertIn('probe requires', admission.reason(observed(), kind='native',
                    requested_memory_bytes=64 * admission.GIB, budget_policy={**policy, field: value}))
        for field in policy:
            incomplete = {key: value for key, value in policy.items() if key != field}
            self.assertIn('probe requires', admission.reason(observed(), kind='native',
                requested_memory_bytes=64 * admission.GIB, budget_policy=incomplete))
        for invalid in ('probe', True, {}):
            self.assertIn('probe requires', admission.reason(observed(), kind='native',
                requested_memory_bytes=64 * admission.GIB, budget_policy=invalid))
        for requested in (6 * admission.GIB, 9 * admission.GIB, 64 * admission.GIB + 1):
            self.assertIn('probe requires', admission.reason(observed(), kind='native',
                requested_memory_bytes=requested, budget_policy=policy))

    def test_probe_keeps_holds_slots_compiler_cap_and_owned_sessions(self):
        def decision(snapshot, kind='native'):
            return admission.reason(snapshot, kind=kind,
                requested_memory_bytes=64 * admission.GIB, budget_policy=probe_policy())
        snapshot = observed(3)
        self.assertIsNone(decision(snapshot))
        snapshot['normal_guard_hold'] = 'memory 181GiB'
        self.assertEqual(decision(snapshot), 'memory 181GiB')
        snapshot['normal_guard_hold'] = 'none'
        snapshot['gate_status'] = 'state=held'
        self.assertIn('gate', decision(snapshot))
        snapshot['gate_status'] = 'no gate lock'
        snapshot['compiler_count'] = 48
        self.assertIn('forty-eight', decision(snapshot))
        self.assertIn('four native', decision(observed(4)))
        snapshot = observed()
        snapshot['owned_sessions_for_child'] = [{'server_pid': 9}]
        self.assertIn('already owns', decision(snapshot, 'mcp'))

    def test_one_owned_mcp_session_per_child(self):
        snapshot = observed()
        snapshot['owned_sessions_for_child'] = [{'server_pid': 9}]
        self.assertIn('already owns', admission.reason(snapshot, kind='mcp', requested_memory_bytes=6 * admission.GIB))
        self.assertIsNone(admission.reason(snapshot, kind='native', requested_memory_bytes=6 * admission.GIB))

    def test_owned_session_identity_rejects_stale_or_zombie_owner(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            process(root, 1, 'python', start=42)
            owner = {'server_pid': 1, 'server_start_ticks': 42}
            self.assertTrue(admission.owned_session_live(owner, root))
            self.assertFalse(admission.owned_session_live({**owner, 'server_start_ticks': 41}, root))
            (root / '1/status').write_text('State:\tZ\nPid:\t1\n')
            self.assertFalse(admission.owned_session_live(owner, root))
            self.assertFalse(admission.owned_session_live({**owner, 'server_pid': 99}, root))

    def test_snapshot_clears_overrides_and_filters_other_children(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            proc = root / 'proc'
            proc.mkdir()
            process(proc, 1, 'python', start=42)
            guard = root / 'guard'
            guard.write_text('#!/bin/sh\n[ -z "${ZESU_IN_GATE-}${ROCQ_WORKSPACE-}${ZESU_WRITER_ID-}" ] || exit 9\ncase "$1" in native-limit) echo 4;; coqc-count) echo 0;; hold) echo none;; lock-status) echo "no gate lock";; esac\n')
            guard.chmod(0o755)
            owners = [{'child': 'A', 'server_pid': 1, 'server_start_ticks': 42}]
            snapshot = admission.snapshot(guard, 'B', owners, proc=proc,
                environment={'PATH': '/usr/bin:/bin', 'ZESU_IN_GATE': '1', 'ROCQ_WORKSPACE': 'fixture', 'ZESU_WRITER_ID': 'writer'})
            self.assertEqual(snapshot['owned_sessions_for_child'], [])
            owners[0]['child'] = 'B'
            snapshot = admission.snapshot(guard, 'B', owners, proc=proc,
                environment={'PATH': '/usr/bin:/bin'})
            self.assertEqual(snapshot['owned_sessions_for_child'], owners)


if __name__ == '__main__':
    unittest.main()
