import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent/'block'))
import marginal_switches


class MarginalSwitchTests(unittest.TestCase):
    def test_only_one_import_changes_and_primary_body_remains(self):
        source = 'Require Import Base.\nRequire Import Switch.\nLemma test : True.\nProof.\ntry zesu_block.\nAbort.\n'
        result = marginal_switches.exclude_switch(source, 'Switch')
        self.assertEqual(result, source.replace('Require Import Switch.\n', ''))
        self.assertEqual(marginal_switches.comparison.primary_body(result), 'try zesu_block.\n')

    def test_missing_switch_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'must import'):
            marginal_switches.exclude_switch('Proof.\nAbort.\n', 'Switch')

    def test_repeated_imports_remove_only_the_selected_module(self):
        source = ('Require Import Switch.\nRequire Import Other.\n'
                  'Require Import Switch.\nLemma test : True.\nProof.\ntry zesu_block.\nAbort.\n')
        result = marginal_switches.exclude_switch(source, 'Switch')
        self.assertNotIn('Require Import Switch.', result)
        self.assertIn('Require Import Other.', result)
        self.assertEqual(marginal_switches.comparison.primary_body(result),
                         marginal_switches.comparison.primary_body(source))

    def test_qualified_activation_requires_only_removed_class_inactive(self):
        with patch.object(marginal_switches.comparison, 'switch_class', side_effect=lambda m: 'Qualified.'+m):
            marginal_switches.validate_activation('SCOPE Qualified.A INACTIVE\nSCOPE Qualified.B ACTIVE', ['A', 'B'], 'A')
            with self.assertRaisesRegex(ValueError, 'differs'):
                marginal_switches.validate_activation('SCOPE Qualified.A ACTIVE\nSCOPE Qualified.B ACTIVE', ['A', 'B'], 'A')
            with self.assertRaisesRegex(ValueError, 'differs'):
                marginal_switches.validate_activation('SCOPE A INACTIVE\nSCOPE Qualified.B ACTIVE', ['A', 'B'], 'A')
