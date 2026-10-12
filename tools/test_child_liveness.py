"""Check liveness with retained records and fake process identities."""

import json
from pathlib import Path
import tempfile
import unittest

import child_liveness as live


class ChildLiveness(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.worktree = self.root / 'child-a'
        self.worktree.mkdir()
        self.proc = self.root / 'proc'
        self.proc.mkdir()
        (self.proc / 'stat').write_text('btime 1000\n')

    def process(self, pid, ticks=100, state='S', command=None, cwd=None):
        entry = self.proc / str(pid)
        entry.mkdir()
        fields = [state] + ['0'] * 18 + [str(ticks)]
        (entry / 'stat').write_text(f'{pid} (python) ' + ' '.join(fields))
        (entry / 'cmdline').write_bytes('\0'.join(command or []).encode())
        (entry / 'cwd').symlink_to(cwd or self.worktree)

    def record(self, name, value):
        path = self.worktree / '_build/attempt' / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))
        return path

    def inspect(self):
        return live.inspect(self.worktree, proc=self.proc)

    def test_empty_running_log_is_live_with_verified_watcher(self):
        log = self.root / 'job.log'
        log.touch()
        self.process(1, command=['python', 'ai-coord.py', 'watch-run', '--label', 'proof-a',
                                 '--log', str(log), '--', 'python', str(self.worktree / 'run.py')])
        row = self.inspect()
        self.assertEqual(row['running_jobs'][0]['label'], 'proof-a')
        self.assertEqual(row['running_jobs'][0]['log_bytes'], 0)
        self.assertIn('start=1970-', live.line(row))
        self.assertIn('last_proof=unavailable', live.line(row))

    def test_live_sessions_require_start_identity(self):
        self.process(1, ticks=42)
        self.process(2, ticks=43)
        self.record('session-start-identities.json', {'server': {'pid': 1, 'start_ticks': 42},
                                                      'pet': {'pid': 2, 'start_ticks': 42}})
        self.assertEqual([r['pid'] for r in self.inspect()['running_sessions']], [1])

    def native_session_records(self):
        server = {'pid': 3786852, 'comm': 'python', 'parent': 3786756,
                  'start_ticks': 146162690, 'state': 'S'}
        pet = {'pid': 3786926, 'comm': 'pet', 'parent': 3786852,
               'start_ticks': 146162790, 'state': 'S'}
        self.record('native-697c-SERVER-OWNER.json', server)
        self.record('native-697c-LIVE-PET.json', {
            'client_pid': 3785947, 'pet': pet, 'server': server,
            'ancestry': [server, {'pid': 3786756, 'comm': 'bash', 'parent': 3785947,
                                  'start_ticks': 146162664, 'state': 'S'}]})

    def test_native_server_owner_and_live_pet_schemas(self):
        self.process(3786852, ticks=146162690)
        self.process(3786926, ticks=146162790)
        self.native_session_records()
        self.assertEqual([r['pid'] for r in self.inspect()['running_sessions']],
                         [3786852, 3786926])

    def test_native_live_pet_schema_rejects_pid_reuse(self):
        self.process(3786852, ticks=146162690)
        self.process(3786926, ticks=146162791)
        self.native_session_records()
        self.assertEqual([r['pid'] for r in self.inspect()['running_sessions']], [3786852])

    def test_native_record_suffix_does_not_accept_backups(self):
        self.process(1)
        self.record('native-697c-LIVE-PET.json.old', {'pet': {'pid': 1, 'start_ticks': 100}})
        self.assertEqual(self.inspect()['running_sessions'], [])

    def test_absent_and_zombie_sessions_are_not_live(self):
        self.process(1, state='Z')
        self.record('OWNER.json', {'pid': 1, 'start_ticks': 100})
        self.assertEqual(self.inspect()['running_sessions'], [])
        self.assertIsNone(live.process_identity(self.proc, 2))

    def test_current_request_survives_empty_job_log(self):
        self.record('CURRENT-CALL.json', {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00Z',
                                          'arguments': {'body': 'try zesu_block.'}})
        last = self.inspect()['last_proof_request']
        self.assertEqual(last['command'], 'try zesu_block.')

    def test_last_proof_excludes_health_startup_and_queries(self):
        self.record('raw-calls.json', [
            {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00+00:00', 'arguments': {'body': 'lia.'}},
            {'tool': 'rocq_health', 'started_utc': '2026-10-12T01:00:00Z'},
            {'tool': 'rocq_start', 'started_utc': '2026-10-12T01:00:00Z'},
            {'tool': 'rocq_query', 'started_utc': '2026-10-12T01:00:00Z'},
            {'tool': 'rocq_step_multi', 'request_utc': '2026-10-12T00:00:01Z', 'arguments': {'tactics': ['simpl.']}}])
        self.assertEqual(self.inspect()['last_proof_request']['command'], ['simpl.'])

    def test_recorded_request_UTC_spelling_is_supported(self):
        self.record('RAW-CALLS.json', [{'tool': 'rocq_check', 'request_UTC': '2026-10-12T00:00:00Z',
                                       'arguments': {'body': 'try zesu_block.'}}])
        self.assertEqual(self.inspect()['last_proof_request']['utc'], '2026-10-12T00:00:00Z')

    def test_bad_and_large_records_are_explicitly_unavailable(self):
        path = self.record('CURRENT-CALL.json', {})
        path.write_text('{')
        large = self.record('calls.json', {})
        with large.open('wb') as stream:
            stream.truncate(live.MAX_RECORD_BYTES + 1)
        self.assertEqual(len(self.inspect()['unavailable_records']), 2)

    def test_other_worktree_with_shared_prefix_is_not_owned(self):
        other = self.root / 'child-ab'
        other.mkdir()
        self.process(1, cwd=other, command=['python', 'watch-run', '--label', 'other',
                                          '--log', '/absent', '--', str(other / 'run.py')])
        self.assertEqual(self.inspect()['running_jobs'], [])

    def test_artifact_symlinks_are_not_traversed(self):
        outside = self.root / 'outside'
        outside.mkdir()
        (outside / 'CURRENT-CALL.json').write_text('{')
        build = self.worktree / '_build'
        build.mkdir()
        (build / 'default').symlink_to(outside)
        self.assertEqual(list(live.record_paths(self.worktree)), [])

    def test_duplicate_session_records_count_one_identity(self):
        self.process(1)
        owner = {'pid': 1, 'start_ticks': 100}
        self.record('session-start-identities.json', {'server': owner})
        self.record('CURRENT-CALL.json', {'owner': {'server': owner}})
        self.assertEqual(len(self.inspect()['running_sessions']), 1)

    def test_gate_owner_is_a_job_and_not_a_proof_session(self):
        self.process(1)
        self.record('OWNER.json', {'pid': 1, 'start_ticks': 100})
        row = self.inspect()
        self.assertEqual(row['running_sessions'], [])
        self.assertEqual(row['running_jobs'][0]['label'], 'attempt')

    def test_naive_time_is_unavailable_instead_of_an_assumed_timezone(self):
        self.record('CURRENT-CALL.json', {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00',
                                          'arguments': {'body': 'lia.'}})
        self.assertIsNone(self.inspect()['last_proof_request'])
        self.assertEqual(len(self.inspect()['unavailable_records']), 1)

    def test_command_newline_stays_on_one_output_line(self):
        self.record('CURRENT-CALL.json', {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00Z',
                                          'arguments': {'body': 'simpl.\nlia.'}})
        self.assertEqual(len(live.line(self.inspect()).splitlines()), 1)

    def test_malformed_request_does_not_hide_an_independent_live_session(self):
        self.process(1)
        self.record('session-start-identities.json', {'server': {'pid': 1, 'start_ticks': 100}})
        self.record('CURRENT-CALL.json', {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00Z',
                                          'arguments': None})
        row = self.inspect()
        self.assertEqual(len(row['running_sessions']), 1)
        self.assertEqual(len(row['unavailable_records']), 1)

    def test_line_bounds_long_commands_but_json_keeps_the_exact_command(self):
        command = 'idtac. ' * 100
        self.record('CURRENT-CALL.json', {'tool': 'rocq_check', 'started_utc': '2026-10-12T00:00:00Z',
                                          'arguments': {'body': command}})
        row = self.inspect()
        self.assertEqual(row['last_proof_request']['command'], command)
        self.assertLess(len(live.line(row)), 500)


if __name__ == '__main__':
    unittest.main()
