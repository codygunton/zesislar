"""Check the authenticated loop-head selection and its fixed backedge owners."""
import hashlib
import json
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header
from render_fp301_statements import render_loop_head

ROOT = Path(__file__).resolve().parents[2]


class LoopHeads(unittest.TestCase):
    def test_source_classes_and_committed_outputs(self):
        fixture = json.loads((ROOT / 'tools/block/fixtures/fp301-loop-heads.json').read_text())
        header = pilot_header(load_profile())
        self.assertEqual([r['block'] for r in fixture['rows']], ['6a24', '6ac4'])
        for row in fixture['rows']:
            self.assertEqual(len(row['classes']), 4)
            for source in row['classes']:
                for name in ['machine_x13', 'machine_x15', 'machine_x16', 'machine_x11']:
                    self.assertIn('(' + name + ' : bv 64)', source)
                self.assertIn('(i : lvar "zesuLoopIndex" Z)', source)
            for structural in [False, True]:
                path = ROOT / ('ZesuSsz/Generated/DecodeItem/FP301/Pilot' + row['block']
                               + ('Structural' if structural else 'Entries') + '.v')
                self.assertEqual(path.read_text(), render_loop_head(row['block'], header, structural))

    def test_predecessor_and_backedge_owner_names(self):
        fixture = json.loads((ROOT / 'tools/block/fixtures/fp301-generation.json').read_text())
        for block, predecessor in [('6a24', '6a14'), ('6ac4', '6ab4')]:
            source = next(r['canonical_source'] for r in fixture['callers']
                          if r['output'].endswith('Caller' + predecessor + '.v'))
            self.assertIn('Pilot' + block + 'Entries.fp_machineAt' + block, source)
