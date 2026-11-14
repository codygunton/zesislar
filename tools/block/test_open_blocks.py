"""Block obligations of a compliance theorem: open, closed and entry-less blocks."""
import unittest

import render_open_blocks as open_blocks
from function_profiles import load_profile


def row(case, pc, successors, status='rendered'):
    return {'case': case, 'pc': pc, 'successors': successors, 'status': status,
            'preconditions': [], 'lemma': 'DesignedBoundary_' + pc[2:]}


class OpenBlocks(unittest.TestCase):
    def setUp(self):
        self.profile = load_profile('decodeParentHeader')
        # a -> b (no caller) -> c (no entry) -> d (no entry); b -> e; a closed.
        self.rows = [row('5cb8', '0x800d5cb8', ['5cf8']),
                     row('5cf8', '0x800d5cf8', ['5d68', '5d00'], 'refused'),
                     row('5d00', '0x800d5d00', []),
                     row('5d68', '0x800d5d68', ['5f2c'], 'refused'),
                     row('5f2c', '0x800d5f2c', [], 'refused')]
        self.entry = lambda case: case not in ('5d68', '5f2c')

    def test_closed_open_and_regions(self):
        entries, open_fields, closed_fields, _ = open_blocks.plan(
            self.profile, self.rows, {'5cb8'}, self.entry)
        self.assertEqual(entries, ['5cb8', '5cf8', '5d00'])
        self.assertEqual([case for case, _, _ in closed_fields], ['5cb8'])
        fields = {case: region for case, _, region in open_fields}
        self.assertEqual(set(fields), {'5cf8', '5d00'})
        self.assertIsNone(fields['5d00'])
        self.assertEqual(fields['5cf8']['region'], ['5cf8', '5d68', '5f2c'])
        self.assertEqual(fields['5cf8']['successors'], ['5d00'])

    def test_region_call_sites(self):
        # The memcpy tail call lies in 5d68; its block ends at the next block start (5da4).
        rows = self.rows + [row('5da4', '0x800d5da4', [])]
        _, open_fields, _, _ = open_blocks.plan(self.profile, rows, set(), self.entry)
        region = next(region for case, _, region in open_fields if case == '5cf8')
        premises, modules = open_blocks.call_premises(self.profile, 0x800d5d68, region['ends']['5d68'])
        self.assertEqual(modules, ['ZesuSsz.Contracts.ParentHeaderMemcpyService'])
        self.assertEqual(premises, ['instr_pre 0x800e06c0 '
                                    '(ZesuSsz.Contracts.ParentHeaderMemcpyService.memcpyCallSpec2)%I'])


if __name__ == '__main__':
    unittest.main()
