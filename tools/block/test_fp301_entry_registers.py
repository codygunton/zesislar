"""Check the approved dead-register declaration and its rendering boundary."""
import json
from pathlib import Path
import unittest

from render_fp301_statements import render_entry_registers

ROOT = Path(__file__).resolve().parents[2]


class EntryRegisterDeclarations(unittest.TestCase):
    def setUp(self):
        self.rule = json.loads((ROOT / 'tools/block/fixtures/fp301-entry-registers.json').read_text())['rows'][0]
        # The approved form is committed; its sources are the committed 0180 modules before the rule.
        self.sources = []
        for name in ('Pilot0180Entries.v', 'Pilot0180Structural.v'):
            committed = (ROOT / 'ZesuSsz/Generated/DecodeItem/FP301' / name).read_text()
            self.sources.append(committed.replace('(∃ (machine_x11 : bv 64) ', '(∃ ', 1).replace(
                self.rule['new_resource'], self.rule['old_resource'], 1))

    def test_only_the_dead_register_and_its_binder_change(self):
        self.assertEqual(len(self.sources), 2)
        for source in self.sources:
            rendered = render_entry_registers(source, 'decodeItem')
            self.assertEqual(rendered.count('(machine_x11 : bv 64)'), 1)
            self.assertEqual(rendered.count(self.rule['new_resource']), 1)
            self.assertNotIn(self.rule['old_resource'], rendered)
            restored = rendered.replace('(∃ (machine_x11 : bv 64) ', '(∃ ', 1).replace(
                self.rule['new_resource'], self.rule['old_resource'], 1)
            self.assertEqual(restored, source)

    def test_other_entry_owners_remain_unchanged(self):
        for source in self.sources:
            source = source.replace(self.rule['entry'], 'another_entry')
            self.assertEqual(render_entry_registers(source, 'decodeItem'), source)

    def test_an_entry_of_the_same_name_in_another_function_is_unchanged(self):
        for source in self.sources:
            changed = source.replace(self.rule['old_resource'], 'changed_resource', 1)
            self.assertEqual(render_entry_registers(changed, 'keysEnsureCapacity'), changed)

    def test_entry_already_in_the_approved_form_is_kept(self):
        for source in self.sources:
            rendered = render_entry_registers(source, 'decodeItem')
            self.assertEqual(render_entry_registers(rendered, 'decodeItem'), rendered)

    def test_changed_resource_refuses_the_old_authorization(self):
        for source in self.sources:
            source = source.replace(self.rule['old_resource'], 'changed_resource', 1)
            with self.assertRaisesRegex(ValueError, 'approved register declaration changed'):
                render_entry_registers(source, 'decodeItem')


if __name__ == '__main__':
    unittest.main()
