"""Cross-route guard variants use private tokens, processes, and kernel fixtures."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE / 'code')]
import admission_memory as M
import test_owned_guard_scope as Fixtures


class PublicGuardVariants(unittest.TestCase):
    setUp = Fixtures.OwnedGuardScope.setUp
    write = Fixtures.OwnedGuardScope.write
    process = Fixtures.OwnedGuardScope.process
    post_exec = Fixtures.OwnedGuardScope.post_exec
    seal = Fixtures.OwnedGuardScope.seal

    def runtime_variant(self):
        self.guard.write_bytes((HERE / 'runtime-tools/resource_guard.sh').read_bytes())
        self.source = self.reader.guard_source(str(self.guard), hashlib.sha256(self.guard.read_bytes()).hexdigest())

    def test_stock_guard_keeps_exact_source_record(self):
        expected = {'path': str(self.guard), 'sha256': hashlib.sha256(self.guard.read_bytes()).hexdigest(),
                    'identity': list(self.reader.file_identity(self.guard.lstat()))}
        self.assertEqual(self.reader.guard_source(str(self.guard), expected['sha256']), expected)

    def test_runtime_guard_keeps_exact_source_record(self):
        self.runtime_variant()
        self.assertEqual(self.source['sha256'], hashlib.sha256((HERE / 'runtime-tools/resource_guard.sh').read_bytes()).hexdigest())
        self.assertEqual(self.source['identity'], list(self.reader.file_identity(self.guard.lstat())))

    def test_runtime_marked_token_authenticates_across_canonical_route(self):
        self.runtime_variant()
        self.marker.write_text(self.text + 'memory_claim_bytes=8589934592\n'
                               'memory_fence_bytes=68719476736\n')
        key = M.shell_key(self.marker)
        data = copy.deepcopy(self.data)
        data['fixed_claims'] = {self.key: 8 * M.GIB, key: 8 * M.GIB}
        data['shell_marker_directory'] = str(self.tokens)
        data['shell_claim_owners'] = {key: {'owner': self.owner, 'generation': self.generation,
                                          'marker': str(self.marker), 'guard_source': self.source}}
        self.ledger.write_text(json.dumps(data))
        self.assertTrue(M.mark_shell(self.marker, ledger=self.ledger, reader=self.reader))
        sealed = json.loads(self.ledger.read_text())
        self.post_exec()
        observation = self.reader.claim(sealed, key)
        self.assertTrue(observation['verified'], observation)
        self.assertTrue(observation['aggregate_verified'])
        self.assertFalse(self.reader.compiler(self.marker)['verified'])
        result = M.projection(sealed, M.ledger_claims(sealed), 0, 100 * M.GIB, reader=self.reader)
        self.assertTrue(result['fits'])
        self.assertEqual(result['raw_claim_bytes'], 16 * M.GIB)
        self.assertEqual(result['active_claim_bytes'], 8 * M.GIB)
        self.assertEqual(len(result['aggregate_groups']), 1)
        self.assertEqual(sealed['shell_claim_owners'][key]['guard_attestation']['source'], self.source)

    def test_other_variant_hash_cannot_replace_expected_hash(self):
        stock_hash = self.source['sha256']
        self.runtime_variant()
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.reader.guard_source(str(self.guard), stock_hash)

    def test_rehashed_tampered_runtime_guard_refuses(self):
        self.runtime_variant()
        self.guard.write_bytes(self.guard.read_bytes() + b'\n# unapproved change\n')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.reader.guard_source(str(self.guard), hashlib.sha256(self.guard.read_bytes()).hexdigest())

    def test_arbitrary_guard_bytes_refuse_even_with_matching_hash(self):
        self.guard.write_bytes(b'#!/bin/bash\nexit 0\n')
        with self.assertRaisesRegex(ValueError, 'source bytes changed'):
            self.reader.guard_source(str(self.guard), hashlib.sha256(self.guard.read_bytes()).hexdigest())

    def test_runtime_inode_replacement_breaks_sealing(self):
        self.runtime_variant(); attestation = self.seal(); self.post_exec()
        replacement = self.guard.with_name('replacement')
        replacement.write_bytes(self.guard.read_bytes()); replacement.chmod(0o700)
        replacement.replace(self.guard)
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_runtime_mutation_breaks_sealing(self):
        self.runtime_variant(); attestation = self.seal(); self.post_exec()
        self.guard.write_bytes(self.guard.read_bytes() + b'\n# changed after sealing\n')
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])

    def test_runtime_symlink_refuses(self):
        self.runtime_variant()
        alias = self.root / 'alias/resource_guard.sh'; alias.parent.mkdir(); alias.symlink_to(self.guard)
        with self.assertRaisesRegex(ValueError, 'source path changed'):
            self.reader.guard_source(str(alias), self.source['sha256'])

    def test_runtime_group_writable_source_refuses(self):
        self.runtime_variant(); self.guard.chmod(0o720)
        with self.assertRaisesRegex(ValueError, 'source is not owned'):
            self.reader.guard_source(str(self.guard), self.source['sha256'])

    def test_runtime_filename_refuses(self):
        self.runtime_variant()
        other = self.guard.with_name('unapproved-name.sh'); other.write_bytes(self.guard.read_bytes())
        with self.assertRaisesRegex(ValueError, 'source path changed'):
            self.reader.guard_source(str(other), self.source['sha256'])

    def test_runtime_token_generation_stays_sealed(self):
        self.runtime_variant(); attestation = self.seal(); self.post_exec()
        self.marker.write_text(self.text.replace(self.generation, '11111111-1111-1111-1111-111111111111'))
        self.assertFalse(self.reader.owned_scope(self.marker, attestation)['verified'])


if __name__ == '__main__':
    unittest.main()
