"""Focused safety tests for the loop subsumption adapter."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import subprocess

from chain_subsumption import check_subsumption, subsumption_source


class SubsumptionTests(unittest.TestCase):
    def setUp(self):
        self.state = {'binders': '`{!islaG Sigma}', 'coq': [],
                      'spatial': ['True'], 'outcome': 'reached'}

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
            kwargs['stdout'].write('Error: incomplete proof\n')
            return subprocess.CompletedProcess(args[0], 1)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', fail):
            result = check_subsumption(self.state, self.state, directory, 1)
            self.assertFalse(result['closed'])
            self.assertIn('incomplete proof', result['residual'])
            self.assertTrue(Path(result['log']).exists())

    def test_zero_exit_requires_assumption_audit(self):
        def success(*args, **kwargs):
            return subprocess.CompletedProcess(args[0], 0)
        with tempfile.TemporaryDirectory() as directory, patch('chain_subsumption.subprocess.run', success):
            self.assertFalse(check_subsumption(self.state, self.state, directory, 1)['closed'])


if __name__ == '__main__':
    unittest.main()
