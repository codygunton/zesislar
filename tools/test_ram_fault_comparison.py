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

    def test_approved_arm_preserves_the_historical_ram_fault_import(self):
        _, baseline = self.fixture()
        module = 'ZesuSsz.Automation.Switches.IntegerArrayAddress'
        on = 'Require Import ' + module + '.\n' + baseline
        self.assertEqual(len(verify_pair(baseline, on, baseline, [module, SWITCH])), 64)
        with self.assertRaisesRegex(ValueError, 'unauthorized'):
            verify_pair(baseline, on, baseline, [SWITCH])
        with self.assertRaisesRegex(ValueError, 'beyond approved'):
            verify_pair(baseline, on.replace(': True.', ': False.'), baseline, [module, SWITCH])

    def test_scope_query_records_each_approved_class(self):
        modules = [SWITCH, 'ZesuSsz.Automation.Switches.RecordWitness']
        source = activation_source(modules, True, modules)
        self.assertIn('SCOPE ZesuSsz.Automation.Hooks.ZesuStepRecordWitness ACTIVE', source)
        self.assertIn('SCOPE ZesuSsz.Automation.Hooks.ZesuStepRecordWitness INACTIVE', source)
        self.assertIn('Check ZesuSsz.Automation.Hooks.ZesuStepRecordWitness.', source)
        self.assertTrue(source.endswith('exact I.\nQed.\n'))

    def test_activation_queries_require_the_expected_switch_state(self):
        self.assertTrue(activation_source([SWITCH], True).startswith(
            'Require Import ZesuSsz.Automation.All.\n'))
        self.assertIn('Fail Check', activation_source(['ZesuSsz.Automation.All'], False))
        self.assertNotIn('Fail Check', activation_source([SWITCH], True))
        with self.assertRaisesRegex(ValueError, 'do not match'):
            activation_source([SWITCH], False)


if __name__ == '__main__':
    unittest.main()
