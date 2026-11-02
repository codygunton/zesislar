"""Temporary guard identities. These controls start no compiler or proof."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M
import stock_scope_stdin_relay as relay
import test_admission_memory as fixtures


class OwnedGuardScope(unittest.TestCase):
    write = fixtures.ScopeTests.write
    process = fixtures.ScopeTests.process

    def setUp(self):
        fixtures.ScopeTests.setUp(self)
        self.owner = {'pid': 14, 'startticks': 104}
        self.actor = {'pid': 15, 'startticks': 105}
        self.generation = '12345678-1234-1234-1234-123456789abc'
        self.tokens = self.root / 'tokens'; self.tokens.mkdir()
        self.marker = self.tokens / ('14.' + self.generation)
        self.ledger = self.root / 'LEDGER.json'
        self.guard = self.root / 'public/resource_guard.sh'; self.guard.parent.mkdir()
        self.guard.write_bytes((HERE.parents[1] / 'resource_guard.sh').read_bytes())
        self.guard.chmod(0o700)
        self.source = self.reader.guard_source(str(self.guard), hashlib.sha256(self.guard.read_bytes()).hexdigest())
        self.leaf = self.group / 'zesudet-client-14-1.scope'; self.leaf.mkdir()
        (self.leaf / 'memory.current').write_text('5')
        (self.leaf / 'cgroup.events').write_text('populated 1\n')
        (self.group / 'cgroup.events').write_text('populated 1\n')
        self.process(self.owner, 12, ['bash', str(self.guard), 'scope', 'client'], str(self.group.relative_to(self.reader.root)))
        self.argv = ['bash', str(self.guard), 'scope-exec', str(self.marker), '--', '/fixture/client']
        self.process(self.actor, 14, self.argv, str(self.leaf.relative_to(self.reader.root)))
        (self.proc / '15/environ').write_bytes(b'')
        self.text = ('15\nwriter=\naggregate=' + self.group.name + '\nowner_start=104\nchild_start=105\n'
                     'reservation_generation=' + self.generation + '\n')
        self.marker.write_text(self.text); self.marker.chmod(0o600)
        self.lock_environment = patch.dict(os.environ, {'ZESU_GATE_LOCK': str(self.root / 'gate.lock')})
        self.lock_environment.start(); self.addCleanup(self.lock_environment.stop)

    def seal(self):
        return self.reader.scope_exec(self.marker, self.source)[1]

    def post_exec(self, token=None):
        (self.proc / '15/cmdline').write_bytes(b'/fixture/client\0')
        (self.proc / '15/environ').write_bytes(('ZESU_OWNED_GUARD_TOKEN=' + str(token or self.marker) + '\0').encode())

    def test_pre_exec_accepts_exact_public_scope_without_compiler_reuse(self):
        row, attestation = self.reader.scope_exec(self.marker, self.source)
        self.assertTrue(row['verified'])
        self.assertEqual(attestation['owner'], self.owner)
        self.assertEqual(attestation['actor'], self.actor)
        self.assertFalse(self.reader.compiler(self.marker)['verified'])

    def test_scope_identity_is_not_compiler_slot_permission(self):
        attestation = self.seal(); self.post_exec()
        self.assertTrue(self.reader.owned_scope(self.marker, attestation)['verified'])
        self.assertFalse(self.reader.compiler(self.marker)['verified'])
        (self.proc / '15/environ').write_bytes(('ZESU_COQC_SCOPE=' + str(self.marker) + '\0ZESU_COQC_RESERVATION=' + str(self.marker) + '\0').encode())
        self.assertTrue(self.reader.compiler(self.marker)['verified'])

    def test_post_exec_does_not_accept_outer_or_missing_identity(self):
        attestation = self.seal(); self.post_exec(self.tokens / 'outer')
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])
        (self.proc / '15/environ').write_bytes(b'')
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_pre_exec_refuses_registry_wrapper_with_guard_argument(self):
        (self.proc / '15/cmdline').write_bytes(('python\0registry.py\0' + '\0'.join(self.argv) + '\0').encode())
        with self.assertRaisesRegex(ValueError, 'scope-exec command'): self.seal()

    def test_pre_exec_refuses_other_token_and_mode(self):
        for index, value in ((2, 'scope'), (3, str(self.tokens / 'outer'))):
            argv = self.argv.copy(); argv[index] = value
            (self.proc / '15/cmdline').write_bytes(('\0'.join(argv) + '\0').encode())
            with self.subTest(index=index), self.assertRaises(ValueError): self.seal()

    def test_pre_exec_refuses_source_mutation_or_replacement(self):
        self.guard.write_bytes(b'changed public guard')
        with self.assertRaises(ValueError): self.seal()

    def test_pre_exec_refuses_same_bytes_source_replacement(self):
        raw = self.guard.read_bytes(); self.guard.unlink(); self.guard.write_bytes(raw); self.guard.chmod(0o700)
        with self.assertRaises(ValueError): self.seal()

    def test_pre_exec_refuses_symlink_source(self):
        alias = self.root / 'alias/resource_guard.sh'; alias.parent.mkdir(); alias.symlink_to(self.guard)
        source = dict(self.source, path=str(alias))
        with self.assertRaises(ValueError): self.reader.scope_exec(self.marker, source)

    def test_pre_exec_refuses_owner_or_child_pid_reuse(self):
        for actor in (self.owner, self.actor):
            path = self.proc / str(actor['pid']) / 'stat'; before = path.read_bytes()
            self.process(dict(actor, startticks=999), 12 if actor == self.owner else 14, self.argv, str(self.leaf.relative_to(self.reader.root)))
            with self.subTest(actor=actor), self.assertRaises(ValueError): self.seal()
            path.write_bytes(before)

    def test_pre_exec_refuses_generation_change(self):
        self.marker.write_text(self.text.replace(self.generation, '11111111-1111-1111-1111-111111111111'))
        with self.assertRaises(ValueError): self.seal()

    def test_post_exec_refuses_changed_actor_or_leaf(self):
        attestation = self.seal(); self.post_exec()
        for field, value in (('actor', {'pid': 99, 'startticks': 99}), ('leaf', {'scope': str(self.group), 'device': 1, 'inode': 1})):
            changed = copy.deepcopy(attestation); changed[field] = value
            with self.subTest(field=field): self.assertFalse(self.reader.owned_scope(self.marker, changed)['verified'])

    def test_post_exec_refuses_marker_mutation(self):
        attestation = self.seal(); self.post_exec()
        self.marker.write_text(self.text.replace('child_start=105', 'child_start=106'))
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_post_exec_refuses_replaced_kernel_leaf(self):
        attestation = self.seal(); self.post_exec()
        self.leaf.rename(self.leaf.with_name('retained-old-leaf.scope'))
        self.leaf.mkdir(); (self.leaf / 'memory.current').write_text('5')
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_pre_exec_refuses_child_outside_owner_ancestry(self):
        self.process(self.actor, 12, self.argv, str(self.leaf.relative_to(self.reader.root)))
        with self.assertRaises(ValueError): self.seal()

    def test_post_exec_refuses_changed_source_attestation(self):
        attestation = self.seal(); self.post_exec()
        attestation['source'] = dict(self.source, sha256='0' * 64)
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_pre_exec_rechecks_source_after_leaf_sampling(self):
        original = self.reader.guard_leaf
        def changed(marker):
            result = original(marker)
            self.guard.write_bytes(b'changed during sampling')
            return result
        with patch.object(self.reader, 'guard_leaf', changed), self.assertRaises(ValueError): self.seal()

    def test_mark_seals_pre_exec_then_claim_accepts_post_exec_identity(self):
        data = {'fixed_claims': {M.shell_key(self.marker): 8 * M.GIB}, 'shell_claim_owners': {
            M.shell_key(self.marker): {'owner': self.owner, 'generation': self.generation,
                'marker': str(self.marker), 'guard_source': self.source}}}
        self.ledger.write_text(json.dumps(data))
        self.assertTrue(M.mark_shell(self.marker, ledger=self.ledger, reader=self.reader))
        data = json.loads(self.ledger.read_text())
        self.assertIn('guard_attestation', data['shell_claim_owners'][M.shell_key(self.marker)])
        self.post_exec()
        self.assertTrue(self.reader.claim(data, M.shell_key(self.marker))['verified'])
        self.assertFalse(self.reader.compiler(self.marker)['verified'])
        self.assertFalse(self.reader.shell(self.marker, owner=self.owner)['verified'])

    def test_confirm_authenticates_guard_source_before_booking(self):
        self.marker.unlink()
        replacement = self.root / 'replacement'
        replacement.write_text('confirmed\nwriter=\naggregate=' + self.group.name + '\nowner_start=104\n'
            'reservation_generation=' + self.generation + '\nmemory_claim_bytes=8589934592\n'
            'guard_source_path=' + str(self.guard) + '\nguard_source_sha256=' + self.source['sha256'] + '\n')
        data = {'fixed_claims': {}, 'shell_marker_directory': str(self.tokens)}
        self.ledger.write_text(json.dumps(data))
        self.assertTrue(M.confirm_shell(self.marker, replacement, 8*M.GIB, 200*M.GIB,
                                      ledger=self.ledger, reader=self.reader)['fits'])
        actual = json.loads(self.ledger.read_text())['shell_claim_owners'][M.shell_key(self.marker)]
        self.assertEqual(actual['guard_source'], self.source)


class RelayIdentity(unittest.TestCase):
    def test_staged_helper_uses_its_own_installed_guard_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            tools = Path(temporary) / 'tools'; block = tools / 'block'; block.mkdir(parents=True)
            module = block / 'admission_memory.py'
            module.write_bytes((HERE / 'code/admission_memory.py').read_bytes())
            guard = tools / 'resource_guard.sh'
            guard.write_bytes((HERE / 'runtime-tools/resource_guard.sh').read_bytes())
            spec = importlib.util.spec_from_file_location('_fixture_owned_guard', module)
            staged = importlib.util.module_from_spec(spec); spec.loader.exec_module(staged)
            result = staged.ScopeReader().guard_source(str(guard), hashlib.sha256(guard.read_bytes()).hexdigest())
            self.assertEqual(result['path'], str(guard))
            with self.assertRaises(ValueError):
                staged.ScopeReader().guard_source(str(HERE.parents[1] / 'resource_guard.sh'),
                    hashlib.sha256((HERE.parents[1] / 'resource_guard.sh').read_bytes()).hexdigest())

    def test_later_compiler_reserves_own_slot_despite_guard_identity(self):
        guard = HERE.parents[1] / 'resource_guard.sh'
        library = guard.read_text().split('\nprune_scope_registry\n', 1)[0]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            environment = {k: v for k, v in os.environ.items() if not k.startswith('ZESU_')}
            environment.update(ZESU_GUARD_STATE=str(root), ZESU_GATE_LOCK=str(root / 'gate.lock'),
                               ZESU_OWNED_GUARD_TOKEN='outer-identity')
            script = r'''
validate_probe_scope() { :; }
diagnostic_probe() { return 1; }
reservation_path() { return 1; }
wait_for_gate() { :; }
guard_wait() { :; }
ensure_workload_parent() { :; }
aggregate_slice() { echo fixture.slice; }
reserve_coqc() { echo reserved >> "$STATE_DIR/events"; echo fresh-compiler-token; }
confirm_coqc() { [ "$1" = fresh-compiler-token ]; }
release_coqc() { echo "released $1" >> "$STATE_DIR/events"; }
io_class() { :; }
systemd-run() {
  [ -z "$ZESU_OWNED_GUARD_TOKEN" ] || return 91
  echo launched >> "$STATE_DIR/events"
}
run_scope fixture -- /fixture/compiler || exit $?
cat "$STATE_DIR/events"
'''
            result = subprocess.run(['bash', '-c', library + script, str(guard)], env=environment,
                                    text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.splitlines(), ['reserved', 'launched', 'released fresh-compiler-token'])

    def test_enter_preserves_only_inner_identity_and_removes_reuse_keys(self):
        read_fd, write_fd = os.pipe()
        self.addCleanup(os.close, read_fd); self.addCleanup(os.close, write_fd)
        original = os.dup(0); self.addCleanup(os.close, original)
        info = os.fstat(read_fd)
        try:
            with patch.dict(os.environ, {'ZESU_COQC_SCOPE': 'inner', 'ZESU_COQC_RESERVATION': 'inner',
                                         'ZESU_OWNED_GUARD_TOKEN': 'inner'}, clear=True), patch.object(relay.os, 'execve') as execute:
                relay.enter(os.getpid(), relay.startticks(os.getpid()), read_fd, info.st_dev, info.st_ino, ['/fixture/client'])
                environment = execute.call_args.args[2]
                self.assertEqual(environment, {'ZESU_OWNED_GUARD_TOKEN': 'inner'})
            with patch.dict(os.environ, {'ZESU_COQC_SCOPE': 'outer', 'ZESU_COQC_RESERVATION': 'outer'}, clear=True), patch.object(relay.os, 'execve') as execute:
                relay.enter(os.getpid(), relay.startticks(os.getpid()), read_fd, info.st_dev, info.st_ino, ['/fixture/client'])
                self.assertEqual(execute.call_args.args[2], {})
        finally: os.dup2(original, 0)

    def test_guard_sets_current_inner_identity_after_mark_and_clears_outer_before_launch(self):
        guard = (HERE.parents[1] / 'resource_guard.sh').read_text()
        self.assertIn('ZESU_OWNED_GUARD_TOKEN="" ZESU_SCOPE_CPU=', guard)
        branch = guard.split('\n  scope-exec)', 1)[1].split('\n  batch-exec)', 1)[0]
        self.assertLess(branch.index('mark_coqc "$token"'), branch.index('ZESU_OWNED_GUARD_TOKEN="$token"'))
        relay_source = (HERE / 'code/stock_scope_stdin_relay.py').read_text()
        self.assertIn("environment.pop('ZESU_COQC_SCOPE', None)", relay_source)
        self.assertIn("environment.pop('ZESU_COQC_RESERVATION', None)", relay_source)


if __name__ == '__main__': unittest.main()
