"""Authenticate the green baseline before omitting tool suites."""
from copy import deepcopy
import unittest
from unittest.mock import patch

import gate_exit_peaks as P
import gate_scope as S
from test_gate_exit_peaks import GatePeaks
from block.harness.code.entry_chain import binding, save


class GateScopeTests(GatePeaks):
    def setUp(self):
        super().setUp()
        self.digest = 'a'*64
        self.request['code_identity']['tools_tree_sha256'] = self.digest
        save(self.f.out/'REQUEST.json', self.request)
        result = P.read_bound(binding(self.f.out/'RESULT.json'))
        result['code_identity_after'] = deepcopy(self.request['code_identity'])
        save(self.f.out/'RESULT.json', result)
        self.ledger['correctness_gate_releases']['gate']['receipt_sha256'] = binding(self.f.out/'REQUEST.json')['sha256']
        self.ledger['gate_exit_peaks'] = []
        P.endorse(self.f.out, self.request, self.ledger, closed=True)

    def unchanged(self, ledger=None):
        return S.tools_unchanged(self.ledger if ledger is None else ledger,
            self.digest, closed=lambda batch: True, guard_reader=self.f.reader)

    def test_unchanged_tools_with_complete_green_authentication_skip_suites(self):
        self.assertTrue(self.unchanged())

    def test_absent_or_legacy_baseline_runs_suites(self):
        self.assertFalse(self.unchanged({}))
        data = deepcopy(self.ledger)
        data['gate_exit_peaks'][-1]['code_identity'].pop('tools_tree_sha256')
        self.assertFalse(self.unchanged(data))

    def test_different_tools_run_suites(self):
        self.assertFalse(S.tools_unchanged(self.ledger, 'b'*64,
            closed=lambda batch: True, guard_reader=self.f.reader))

    def test_tampered_result_or_request_runs_suites(self):
        for field in ['request', 'result', 'closure']:
            data = deepcopy(self.ledger)
            data['gate_exit_peaks'][-1][field]['sha256'] = '0'*64
            self.assertFalse(self.unchanged(data))

    def test_unreleased_or_live_baseline_runs_suites(self):
        data = deepcopy(self.ledger)
        data['correctness_gate_releases']['gate']['released'] = False
        self.assertFalse(self.unchanged(data))
        self.assertFalse(S.tools_unchanged(self.ledger, self.digest,
            closed=lambda batch: False, guard_reader=self.f.reader))

    def test_invalid_latest_evidence_cannot_fall_back_to_older_green(self):
        bad = deepcopy(self.ledger['gate_exit_peaks'][-1])
        bad['result']['sha256'] = '0'*64
        self.ledger['gate_exit_peaks'].append(bad)
        self.assertFalse(self.unchanged())


class ToolsDigestTests(unittest.TestCase):
    def test_source_changes_additions_deletions_and_modes_change_digest(self):
        import tempfile
        import subprocess
        from pathlib import Path
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(['git', 'init', '--quiet', root], check=True)
            source = root/'tools/check.py'
            source.parent.mkdir()
            source.write_text('first')
            subprocess.run(['git', '-C', root, 'add', '.'], check=True)
            initial = S.tools_digest(root)
            source.write_text('second')
            self.assertNotEqual(S.tools_digest(root), initial)
            source.write_text('first')
            source.chmod(0o755)
            self.assertNotEqual(S.tools_digest(root), initial)
            source.chmod(0o644)
            added = root/'tools/new.py'
            added.write_text('new')
            self.assertNotEqual(S.tools_digest(root), initial)
            added.unlink()
            self.assertEqual(S.tools_digest(root), initial)
            source.unlink()
            self.assertIsNone(S.tools_digest(root))
