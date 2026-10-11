#!/usr/bin/env python3
"""Check the frozen-source boundary used by the authorized fallback."""
import sys
import unittest
import tempfile
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent / 'block'))
from setup_fallback import load_slice, write_interactive_source


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

    def test_separates_interactive_and_compilation_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Boundary.v'
            original = 'Lemma boundary : True.\nProof.\n  try zesu_block.\nQed.\n'
            source.write_text(original)
            interactive = write_interactive_source(source)
            self.assertEqual(interactive.name, 'Boundary_interactive.v')
            self.assertEqual(interactive.read_text(), 'Lemma boundary : True.\nProof.\nAbort.\n')
            self.assertEqual(source.read_text(), original)
            self.assertEqual(write_interactive_source(source), interactive)
            source.write_text(original.replace('True', 'False'))
            with self.assertRaisesRegex(ValueError, 'different contents'):
                write_interactive_source(source)


if __name__ == '__main__':
    unittest.main()
