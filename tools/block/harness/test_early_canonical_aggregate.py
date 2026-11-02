"""Early entry associations use temporary process, token, and kernel fixtures."""
import hashlib
import json
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE / 'code')]
import admission_memory as M
import test_admission_memory as Fixtures


class EarlyCanonicalAggregate(unittest.TestCase):
    write = Fixtures.ScopeTests.write
    process = Fixtures.ScopeTests.process

    def setUp(self):
        Fixtures.ScopeTests.setUp(self)
        self.group.rename(self.group.with_name(f'zesuworkloads-aggregate{os.getuid()}p14r1.slice'))
        self.group = self.group.with_name(f'zesuworkloads-aggregate{os.getuid()}p14r1.slice')
        (self.group / 'memory.max').write_text(str(64 * M.GIB))
        (self.group / 'memory.swap.max').write_text('0')
        (self.group / 'cgroup.events').write_text('populated 1\n')
        self.guard = self.out / 'workspace/tools/resource_guard.sh'
        self.guard.parent.mkdir(parents=True)
        self.guard.write_bytes((HERE.parents[1] / 'resource_guard.sh').read_bytes())
        self.guard.chmod(0o700)
        self.command = [str(self.guard), 'batch', 'entry-chain-block', '--',
                        str(self.guard), 'scope', 'entry-chain-client', '--',
                        'python', '-B', '/tools/entry_chain_run.py', '--inside', str(self.out)]
        self.wrapper = ['python3', '-B', str(self.guard.with_name('run_registry.py')),
                        'run', '--kind', 'stock-batch', '--owner', 'fixture', '--', *self.command]
        self.process(self.owner, 1, ['python', '-B', '/tools/entry_chain_run.py',
                                    'runtime', 'hash', 'block', str(self.out)], '/outside')
        self.process(self.batch, 11, self.wrapper, '/outside')
        self.creator = {'pid': 14, 'startticks': 104}
        self.pending = {'pid': 16, 'startticks': 106}
        self.process(self.creator, 12, ['bash', *self.command], '/outside')
        self.process({'pid': 15, 'startticks': 105}, 14, ['python', 'dune_trace_guard.py'],
                     str(self.group.relative_to(self.reader.root)))
        self.process(self.pending, 15, ['bash', *self.command[4:]],
                     str(self.group.relative_to(self.reader.root)))
        self.process(self.actor, 15, ['python', '/tools/entry_chain_run.py', '--inside', str(self.out)],
                     str(self.group.relative_to(self.reader.root)))
        info = self.group.stat()
        self.bound.update(aggregate_path=str(self.group), aggregate_device=info.st_dev,
                          aggregate_inode=info.st_ino)
        (self.out / 'BATCH-IDENTITY.json').unlink()
        self.write(self.out / 'LAUNCH.json', {'owner': self.owner, 'argv': self.command})
        self.tokens = self.root / 'tokens'; self.tokens.mkdir()
        self.generation = '17f05bf4-ef22-461d-8dbf-7857615d965b'
        self.marker = self.tokens / ('16.' + self.generation)
        self.token = self.root / 'replacement'
        self.fields = {'writer': '', 'aggregate': self.group.name,
                       'memory_claim_bytes': str(64 * M.GIB),
                       'memory_fence_bytes': str(64 * M.GIB), 'owner_start': '106',
                       'reservation_generation': self.generation,
                       'guard_source_path': str(self.guard),
                       'guard_source_sha256': hashlib.sha256(self.guard.read_bytes()).hexdigest()}
        self.save_token()
        self.data['fixed_claims'][self.key] = 64 * M.GIB
        self.data['shell_marker_directory'] = str(self.tokens)
        self.ledger = self.root / 'LEDGER.json'
        self.write(self.ledger, self.data)
        env = patch.dict(os.environ, {'ZESU_GATE_LOCK': str(self.root / 'gate.lock')})
        env.start(); self.addCleanup(env.stop)

    def save_token(self):
        self.token.write_text('confirmed\n' + ''.join(k + '=' + v + '\n' for k, v in self.fields.items()))
        self.token.chmod(0o600)

    def observation(self):
        return self.reader.claim(self.data, self.key, pending_shell=(self.marker, self.token))

    def assert_refused(self):
        row = self.observation()
        self.assertFalse(row['verified'], row)
        result = M.projection(self.data, M.ledger_claims(self.data), 64 * M.GIB, 100 * M.GIB,
                              reader=self.reader, new_observation=self.reader.shell(self.token, owner=self.pending),
                              pending_shell=(self.marker, self.token))
        self.assertFalse(result['fits'])
        self.assertEqual(result['accounted_active_bytes'], 128 * M.GIB)

    def test_same_job_confirmation_counts_one_booking_and_preserves_both_records(self):
        result = M.confirm_shell(self.marker, self.token, 64 * M.GIB, 100 * M.GIB,
                                 ledger=self.ledger, reader=self.reader)
        self.assertTrue(result['fits'], result)
        self.assertEqual(result['active_claim_bytes'], 64 * M.GIB)
        self.assertEqual(result['raw_claim_bytes'], 128 * M.GIB)
        self.assertEqual(result['claim_observations'][self.key]['members'], [self.key, '__new_claim__'])
        data = json.loads(self.ledger.read_text())
        self.assertEqual(data['fixed_claims'][self.key], 64 * M.GIB)
        self.assertEqual(data['fixed_claims'][M.shell_key(self.marker)], 64 * M.GIB)
        later = M.projection(data, M.ledger_claims(data), 0, 100 * M.GIB, reader=self.reader)
        self.assertEqual(later['active_claim_bytes'], 64 * M.GIB)
        self.assertTrue(later['fits'])

    def test_exact_claim_location_works(self):
        self.data['claim_locations'] = {self.key: dict(owner=self.owner, kind='entry', output_path=str(self.out))}
        self.assertTrue(self.observation()['verified'])

    def test_unrelated_claim_location_refuses(self):
        self.data['claim_locations'] = {self.key: dict(owner=dict(self.owner, token='wrong'), kind='entry', output_path=str(self.out))}
        self.assert_refused()

    def test_unrelated_started_owner_refuses(self):
        self.write(self.out / 'STARTED.json', {'owner': dict(self.owner, token='wrong')})
        self.assert_refused()

    def test_unrelated_wrapper_owner_refuses(self):
        self.process(self.batch, 99, self.wrapper, '/outside')
        self.assert_refused()

    def test_changed_wrapper_command_refuses(self):
        self.process(self.batch, 11, self.wrapper[:-1] + ['/another/output'], '/outside')
        self.assert_refused()

    def test_changed_launch_refuses(self):
        self.write(self.out / 'LAUNCH.json', {'owner': self.owner, 'argv': self.command[:-1] + ['/another/output']})
        self.assert_refused()

    def test_changed_creator_ancestry_refuses(self):
        self.process(self.creator, 99, ['bash', *self.command], '/outside')
        self.assert_refused()

    def test_changed_creator_command_refuses(self):
        self.process(self.creator, 12, ['bash', *self.command[:-1], '/another/output'], '/outside')
        self.assert_refused()

    def test_changed_pending_command_refuses(self):
        self.process(self.pending, 15, ['bash', *self.command[4:-1], '/another/output'],
                     str(self.group.relative_to(self.reader.root)))
        self.assert_refused()

    def test_reused_pending_owner_refuses(self):
        self.fields['owner_start'] = '999'; self.save_token()
        self.assert_refused()

    def test_changed_generation_refuses(self):
        self.fields['reservation_generation'] = 'another-generation-1234'; self.save_token()
        self.assert_refused()

    def test_different_claim_booking_refuses(self):
        self.fields['memory_claim_bytes'] = str(32 * M.GIB); self.save_token()
        self.assert_refused()

    def test_missing_public_guard_binding_refuses(self):
        del self.fields['guard_source_sha256']; self.save_token()
        self.assert_refused()

    def test_changed_guard_source_refuses(self):
        self.guard.write_text('# altered public guard\n')
        self.assert_refused()

    def test_changed_fence_refuses(self):
        (self.group / 'memory.max').write_text(str(32 * M.GIB))
        self.assert_refused()

    def test_changed_swap_fence_refuses(self):
        (self.group / 'memory.swap.max').write_text('1')
        self.assert_refused()

    def test_wrong_aggregate_membership_refuses(self):
        (self.proc / '16/cgroup').write_text('0::/outside\n')
        self.assert_refused()

    def test_existing_invalid_receipt_never_uses_early_fallback(self):
        self.write(self.out / 'BATCH-IDENTITY.json', dict(self.bound, aggregate_inode=0))
        self.assert_refused()

    def test_existing_malformed_receipt_never_uses_early_fallback(self):
        (self.out / 'BATCH-IDENTITY.json').write_text('not json')
        self.assert_refused()

    def test_dangling_receipt_never_uses_early_fallback(self):
        (self.out / 'BATCH-IDENTITY.json').symlink_to(self.root / 'absent')
        self.assert_refused()

    def test_existing_valid_receipt_keeps_strict_path(self):
        self.write(self.out / 'BATCH-IDENTITY.json', self.bound)
        self.write(self.out / 'LAUNCH.json', {'invalid': True})
        self.assertTrue(self.observation()['verified'])
        self.assertEqual(self.observation()['reason'], 'exact owner and batch scope')

    def test_receipt_arrival_during_early_sampling_refuses_fallback(self):
        original = self.reader.scope
        def sample(*args, **kwargs):
            row = original(*args, **kwargs)
            self.write(self.out / 'BATCH-IDENTITY.json', dict(self.bound, aggregate_inode=0))
            return row
        with patch.object(self.reader, 'scope', side_effect=sample):
            self.assert_refused()

    def test_token_inode_replacement_during_sampling_refuses(self):
        original = self.reader.scope
        def sample(*args, **kwargs):
            row = original(*args, **kwargs)
            replacement = self.root / 'swapped-token'
            replacement.write_bytes(self.token.read_bytes()); replacement.chmod(0o600)
            replacement.replace(self.token)
            return row
        with patch.object(self.reader, 'scope', side_effect=sample):
            self.assert_refused()

    def test_wrapper_reparenting_during_sampling_refuses(self):
        original = self.reader.scope
        def sample(*args, **kwargs):
            row = original(*args, **kwargs)
            self.process(self.batch, 99, self.wrapper, '/outside')
            return row
        with patch.object(self.reader, 'scope', side_effect=sample):
            self.assert_refused()


if __name__ == '__main__':
    unittest.main()
