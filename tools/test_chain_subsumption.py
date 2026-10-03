"""Focused safety tests for the loop subsumption adapter."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).parent / "block"))

from chain_subsumption import check_subsumption, subsumption_source


class SubsumptionTests(unittest.TestCase):
    def setUp(self):
        self.state = {'binders': '`{!islaG Sigma}', 'coq': [],
                      'spatial': ['True'], 'outcome': 'reached',
                      'root_provenance': {'entry': '0x14d30', 'sha256': 'root'}}

    def test_identity_keeps_qed(self):
        source = subsumption_source(self.state, self.state)
        self.assertIn('ChainPost  -∗ ChainHeader .', source)
        self.assertIn('Qed.', source)
        self.assertNotIn('Admitted', source)

    def test_reject_substitution(self):
        changed = dict(self.state, arguments='unknown')
        self.assertFalse(check_subsumption(self.state, changed, '/tmp', 1)['closed'])

    def test_reject_binder_change(self):
        changed = dict(self.state, binders='`{!islaG Sigma} (n : nat)')
        self.assertRaises(ValueError, subsumption_source, self.state, changed)

    def test_reject_unreached(self):
        changed = dict(self.state, outcome='stalled')
        self.assertRaises(ValueError, subsumption_source, self.state, changed)

    def test_compile_failure_preserves_residual(self):
        def fail(*args, **kwargs):
            if args[0][-1] == "wait":
                return subprocess.CompletedProcess(args[0], 0)
            kwargs['stdout'].write('Error: incomplete proof\n')
            return subprocess.CompletedProcess(args[0], 1)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', fail):
            result = check_subsumption(self.state, self.state, directory, 1)
            self.assertFalse(result['closed'])
            self.assertIn('incomplete proof', result['residual'])
            self.assertTrue(Path(result['log']).exists())

    def test_zero_exit_requires_assumption_audit(self):
        def success(*args, **kwargs):
            if args[0][-1] == "wait":
                return subprocess.CompletedProcess(args[0], 0)
            return subprocess.CompletedProcess(args[0], 0)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', success):
            self.assertFalse(check_subsumption(self.state, self.state, directory, 1)['closed'])

    def test_admission_wait_is_outside_proof_timeout(self):
        commands = []
        def success(command, **kwargs):
            commands.append(command)
            if 'stdout' in kwargs:
                kwargs['stdout'].write('Closed under the global context\n')
            return subprocess.CompletedProcess(command, 0)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', success):
            self.assertTrue(check_subsumption(self.state, self.state, directory, 1)['closed'])
        self.assertEqual(commands[0][-1], 'wait')
        self.assertNotIn('timeout', commands[0])
        self.assertEqual(commands[1][0], 'timeout')

    def test_reject_provenance_change(self):
        changed = dict(self.state, root_provenance={'sha256': 'different'})
        self.assertRaises(ValueError, subsumption_source, self.state, changed)

    def test_reject_missing_provenance(self):
        changed = dict(self.state)
        changed.pop('root_provenance')
        self.assertRaises(ValueError, subsumption_source, changed, changed)

    def test_render_captured_widths(self):
        state = dict(self.state, spatial=['address ↦ₘ 0'],
                     memory_word_widths={'address': 64})
        source = subsumption_source(state, state)
        self.assertIn('address ↦ₘ (BV 64 0)', source)

    def test_reject_missing_width(self):
        state = dict(self.state, spatial=['address ↦ₘ 0'])
        self.assertRaises(ValueError, subsumption_source, state, state)

    def test_inherited_debt_is_conditional(self):
        def success(*args, **kwargs):
            if args[0][-1] == "wait":
                return subprocess.CompletedProcess(args[0], 0)
            kwargs['stdout'].write('Closed under the global context\n')
            return subprocess.CompletedProcess(args[0], 0)
        for key in ('pending_goals', 'shelved_goals'):
            changed = dict(self.state, **{key: [{'conclusion': 'False'}]})
            with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', success):
                result = check_subsumption(changed, self.state, directory, 1)
                self.assertEqual(result['outcome'], 'conditional')
                self.assertFalse(result['closed'])
                self.assertTrue(result['entailment_closed'])
                self.assertEqual(result['debts'][0]['kind'], key)

    def test_clean_entailment_closes(self):
        def success(*args, **kwargs):
            if args[0][-1] == "wait":
                return subprocess.CompletedProcess(args[0], 0)
            kwargs['stdout'].write('Closed under the global context\n')
            return subprocess.CompletedProcess(args[0], 0)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', success):
            result = check_subsumption(self.state, self.state, directory, 1)
            self.assertTrue(result['closed'])


if __name__ == '__main__':
    unittest.main()
