"""Design-table callers: committed outputs, hash binding, and exit premises."""
import copy
import json
import unittest

import render_design_callers as design_callers
from function_profiles import load_profile
from render_fp301_statements import return_precondition, successor_precondition


class DesignCallers(unittest.TestCase):
    def setUp(self):
        self.profile = load_profile()
        self.design = design_callers.load_design(self.profile)

    def test_committed_callers_match_the_design_table(self):
        self.assertEqual(design_callers.check(self.profile), [])

    def test_a_changed_design_hash_is_refused(self):
        data = copy.deepcopy(self.profile.data)
        fixture = json.loads((design_callers.ROOT / data['design_callers']['fixture']).read_text())
        fixture['design']['sha256'] = '0' * 64
        original = design_callers.ROOT / data['design_callers']['fixture']
        text = original.read_text()
        try:
            original.write_text(json.dumps(fixture))
            self.assertIn('The design table changed since the callers were rendered.',
                          design_callers.check(self.profile))
        finally:
            original.write_text(text)

    def test_exit_premises_follow_the_design_table(self):
        premises, imports = design_callers.exits(self.profile, self.design, '00d8')
        self.assertEqual(premises, [successor_precondition(self.profile, '0180'),
                                    successor_precondition(self.profile, '00e0')])
        self.assertEqual(imports[:2], [self.profile.qualified('Pilot00d8Entries'),
                                       self.profile.qualified('Pilot00d8Structural')])
        premises, imports = design_callers.exits(self.profile, self.design, '0180')
        self.assertEqual(premises, [return_precondition(self.profile)])
        self.assertIn(self.profile.qualified('FunctionReturnStructural'), imports)

    def test_loop_head_callers_render_byte_for_byte(self):
        rows = design_callers.compare(self.profile, self.profile['loop_heads'])
        self.assertTrue(all(row['byte_identical'] for row in rows), rows)


if __name__ == '__main__':
    unittest.main()
