#!/usr/bin/env python3
"""Check the frozen-source boundary used by the authorized fallback."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from setup_fallback import load_slice


class LoadSliceTests(unittest.TestCase):
    def test_preserves_imports_entry_and_statement(self):
        prefix = 'Require Import Example.\nDefinition entry := True.\nLemma test : entry.'
        source = prefix + '\nProof.\ntry zesu_block.\nAbort.\n'
        result = load_slice(source)
        self.assertEqual(result, prefix + '\nProof.\nAbort.\n')
        self.assertNotIn('zesu_block', result)

    def test_rejects_missing_proof_boundary(self):
        with self.assertRaises(ValueError):
            load_slice('Require Import Example.\n')

    def test_rejects_ambiguous_proof_boundary(self):
        with self.assertRaises(ValueError):
            load_slice('Lemma a : True.\nProof.\nAbort.\nLemma b : True.\nProof.\nAbort.\n')


if __name__ == '__main__':
    unittest.main()
