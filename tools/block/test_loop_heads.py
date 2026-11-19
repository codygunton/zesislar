"""Check the authenticated loop-head selection and its fixed backedge owners."""
import copy
import hashlib
import json
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header
from render_fp301_statements import render_loop_head
import entry_hist

ROOT = Path(__file__).resolve().parents[2]


class LoopHeads(unittest.TestCase):
    def test_source_classes_and_committed_outputs(self):
        fixture = json.loads((ROOT / 'tools/block/fixtures/fp301-loop-heads.json').read_text())
        header = pilot_header(load_profile())
        self.assertEqual([r['block'] for r in fixture['rows']], ['00c4', '0164'])
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
        for block, predecessor in [('00c4', '00b4'), ('0164', '0154')]:
            source = next(r['canonical_source'] for r in fixture['callers']
                          if r['output'].endswith('Caller' + predecessor + '.v'))
            self.assertIn('Pilot' + block + 'Entries.fp_machineAt' + block, source)


class WrapLoopHeads(unittest.TestCase):
    """The `entry_hist: wrap` shape of the same loop heads: each class keeps its loop binders and
    resources, its hidden facts move into one sealed `_Hist` proposition, and no proof appears."""

    def setUp(self):
        self.addCleanup(entry_hist.configure, None)

    def test_each_class_applies_its_sealed_history(self):
        profile = copy.deepcopy(load_profile())
        profile.data.update({'entry_hist': 'wrap', 'frame_slots': False})
        fixture = json.loads((ROOT / 'tools/block/fixtures/fp301-loop-heads.json').read_text())
        for row in fixture['rows']:
            for structural in [False, True]:
                text = render_loop_head(row['block'], pilot_header(profile), structural, profile)
                self.assertIn('Require Import ZesuSsz.Automation2.Hist.', text)
                self.assertNotRegex(text, r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b')
                for index in range(len(row['classes'])):
                    name = 'fp_machineAt%s_LoopClass%d' % (row['block'], index)
                    if structural:
                        self.assertIn('Typeclasses Opaque ' + name + '_Hist.', text)
                        continue
                    self.assertEqual(text.count('Definition ' + name + '_Hist '), 1)
                    body = text[text.index('Definition ' + name + ' '):]
                    body = body[:body.index('%I.')]
                    self.assertIn('⌜zesu_hist (' + name + '_Hist', body)
                    self.assertIn('(i : lvar "zesuLoopIndex" Z)', body)
                # The legacy render of the same row is unchanged by the wrap render before it.
                self.assertEqual(render_loop_head(row['block'], pilot_header(load_profile()), structural),
                                 (ROOT / ('ZesuSsz/Generated/DecodeItem/FP301/Pilot' + row['block']
                                          + ('Structural' if structural else 'Entries') + '.v')).read_text())
