"""Closed ledger records move to the append-only archive and stay readable."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'code'))
import admission_memory as M
import ledger_archive as A

GIB = M.GIB


def ended_if_odd(_reader, owner):
    return owner['pid'] % 2 == 1


class LedgerArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.ledger = Path(self.temp.name) / 'LEDGER.json'

    def data(self):
        return {
            'fixed_claims': {'shell:released': 0, 'shell:live': GIB, 'Gate_old': 0, 'Gate_recent': 0,
                             'Gate_live': 0, 'Entry_old': 0, 'Entry_protected': 0, 'Entry_live': 0},
            'region_claims': {},
            'shell_claim_owners': {'shell:live': {'marker': '/x', 'owner': {'pid': 2}}},
            'shell_archive': {'shell:released': 'a' * 64},
            'correctness_gate_releases': {key: {'released': True} for key in ('Gate_old', 'Gate_recent', 'Gate_live')},
            'correctness_gate_owners': {'Gate_old': {'pid': 1}, 'Gate_recent': {'pid': 3}, 'Gate_live': {'pid': 2}},
            'correctness_gate_admissions': {'Gate_old': {'claim_bytes': 5}},
            'gate_exit_peaks': [{'claim_key': 'Gate_recent'}],
            'entry_pilot_outside_releases': {key: {'bytes': 1} for key in ('Entry_old', 'Entry_protected', 'Entry_live')},
            'entry_pilot_outside_owners': {'Entry_old': {'pid': 5}, 'Entry_protected': {'pid': 7},
                                           'Entry_live': {'pid': 4}},
            'legacy_kernel_accounts': {'k': {'canonical_owners': {'Entry_protected': {'pid': 7}}}},
            'cleanup_compiler_completions': [1, 2, 3],
        }

    def test_compaction_moves_only_closed_records_and_keeps_them_readable(self):
        data = self.data()
        moved = A.compact(self.ledger, data, None, ended_if_odd, now_ns=10)
        self.assertEqual(moved, 10)
        # Live, protected and recently measured records stay hot.
        self.assertEqual(set(data['fixed_claims']),
                         {'shell:live', 'Gate_recent', 'Gate_live', 'Entry_protected', 'Entry_live'})
        self.assertEqual(set(data['correctness_gate_releases']), {'Gate_recent', 'Gate_live'})
        self.assertEqual(set(data['entry_pilot_outside_owners']), {'Entry_protected', 'Entry_live'})
        self.assertNotIn('cleanup_compiler_completions', data)
        self.assertEqual(data['shell_archive'], {})
        self.assertEqual(data['ledger_archive']['schema'], A.SCHEMA)
        # Every moved record remains evidence in the archive.
        self.assertEqual(A.lookup(self.ledger, 'correctness_gate_admissions', 'Gate_old'), {'claim_bytes': 5})
        self.assertEqual(A.lookup(self.ledger, 'shell_archive', 'shell:released'), 'a' * 64)
        self.assertEqual(M.archived_shell_digest(data, 'shell:released', self.ledger), 'a' * 64)
        self.assertIsNone(M.archived_shell_digest(data, 'shell:unknown', self.ledger))

    def test_an_older_reader_still_finds_every_live_record(self):
        data = self.data()
        A.compact(self.ledger, data, None, ended_if_odd)
        for field in ('fixed_claims', 'region_claims', 'shell_claim_owners'):
            self.assertIsInstance(data[field], dict)
        self.assertEqual(M.ledger_claims(data), {'shell:live': GIB, 'Gate_recent': 0, 'Gate_live': 0,
                                                 'Entry_protected': 0, 'Entry_live': 0})

    def test_archive_rotates_by_size(self):
        original = A.ROTATE_BYTES
        A.ROTATE_BYTES = 10
        try:
            A.append(self.ledger, [{'collection': 'c', 'key': 'one', 'value': 1}])
            A.append(self.ledger, [{'collection': 'c', 'key': 'two', 'value': 2}])
        finally:
            A.ROTATE_BYTES = original
        self.assertEqual(len(list(A.directory(self.ledger).glob('archive-*.jsonl'))), 2)
        self.assertEqual((A.lookup(self.ledger, 'c', 'one'), A.lookup(self.ledger, 'c', 'two')), (1, 2))

    def test_release_after_compaction_still_writes_its_audit_record(self):
        data = self.data()
        data['shell_claim_owners']['shell:new'] = {'owner': {'pid': 9}, 'marker': str(self.ledger) + '.m'}
        data['shell_releases'] = {'shell:new': {'owner': {'pid': 9}, 'marker': str(self.ledger) + '.m'}}
        data['fixed_claims']['shell:new'] = 0
        A.compact(self.ledger, data, None, ended_if_odd)
        import shell_archive
        digest = shell_archive._archive_released_record(data, 'shell:new', Path(self.temp.name) / 'docs')
        self.assertEqual(data['shell_archive']['shell:new'], digest)
        A.compact(self.ledger, data, None, ended_if_odd, now_ns=A.COMPACT_INTERVAL_NS * 3)
        self.assertNotIn('shell:new', data['shell_archive'])
        self.assertEqual(M.archived_shell_digest(data, 'shell:new', self.ledger), digest)
        document = shell_archive.document_path(Path(self.temp.name) / 'docs', 'shell:new', digest)
        self.assertEqual(json.loads(document.read_text())['records']['shell_releases']['owner'],
                         {'pid': 9})

    def test_compaction_is_due_only_for_a_large_stale_ledger(self):
        self.ledger.write_text('{}')
        self.assertFalse(A.due(self.ledger, {}))
        self.ledger.write_text(' ' * (A.COMPACT_ABOVE_BYTES + 1))
        self.assertTrue(A.due(self.ledger, {}, now_ns=A.COMPACT_INTERVAL_NS + 1))
        self.assertFalse(A.due(self.ledger, {'ledger_archive': {'compacted_ns': 5}}, now_ns=6))

    def test_dead_collections_have_no_reader(self):
        tools = HERE.parent.parent
        for name in sorted(A.DEAD_COLLECTIONS):
            readers = subprocess.run(
                ['git', 'grep', '-l', '-w', name, '--', '*.py', ':!**/test_*', ':!**/_historical*',
                 ':!**/ledger_archive.py'], cwd=tools, capture_output=True, text=True).stdout.split()
            with self.subTest(name=name):
                self.assertEqual(readers, [])


if __name__ == '__main__':
    unittest.main()
