"""The controlled comparison must change only switch imports."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).parent/'block'))
from compare_ram_fault import SWITCH, activation_source, verify_pair


class RamFaultComparisonTests(unittest.TestCase):
    def fixture(self):
        common = 'Require Import ZesuSsz.Automation.All.\nLemma infer_boundary : True.\nProof.\ntry zesu_block.\nAbort.\n'
        on = 'Require Import ' + SWITCH + '.\n' + common
        return common, on

    def test_only_switch_import_changes_the_pair(self):
        off, on = self.fixture()
        self.assertEqual(len(verify_pair(off, on, on)), 64)

    def test_resource_change_in_one_arm_prevents_the_comparison(self):
        off, on = self.fixture()
        with self.assertRaisesRegex(ValueError, 'beyond the RamFault import'):
            verify_pair(off.replace(': True.', ': False.'), on, on)

    def test_changed_primary_tactic_prevents_the_comparison(self):
        off, on = self.fixture()
        with self.assertRaisesRegex(ValueError, 'frozen primary body changed'):
            verify_pair(off, on, on.replace('try zesu_block.', 'try zesu_liAStep.'))

    def test_off_arm_cannot_retain_the_switch(self):
        _, on = self.fixture()
        with self.assertRaisesRegex(ValueError, 'beyond the RamFault import'):
            verify_pair(on, on, on)

    def test_activation_queries_require_the_expected_switch_state(self):
        self.assertTrue(activation_source([SWITCH], True).startswith(
            'Require Import ZesuSsz.Automation.All.\n'))
        self.assertIn('Fail Check', activation_source(['ZesuSsz.Automation.All'], False))
        self.assertNotIn('Fail Check', activation_source([SWITCH], True))
        with self.assertRaisesRegex(ValueError, 'do not match'):
            activation_source([SWITCH], False)


if __name__ == '__main__':
    unittest.main()
