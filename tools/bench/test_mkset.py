"""Check the per-member CPU caps tools/bench/mkset.py writes, on a small fake CFG."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

import bench
import mkset

ENTRY = 0x1000


def row(offset, kind, successors, **extra):
    return dict(pc=ENTRY + offset, kind=kind, successors=[ENTRY + s for s in successors], **extra)


def fake_cfg():
    rows = [row(0x0, 'plain', [0x4]), row(0x4, 'branch', [0x8, 0x10]),       # 0000: branch to 0008 or 0010
            row(0x8, 'call', [0xc], target=0x9000),                          # 0008: a call
            row(0xc, 'jump', [0x10]),                                        # 000c: jump into 0010
            row(0x10, 'plain', [0x14]), row(0x14, 'return', []),              # 0010: inlined return block
            row(0x18, 'plain', [0x1c]), row(0x1c, 'branch', [0x18, 0x20]),    # 0018: loop on itself
            row(0x20, 'return', [])]                                          # 0020: return
    rows += [row(0x100 + 4 * index, 'plain', [0x104 + 4 * index]) for index in range(29)]
    rows += [row(0x100 + 4 * 29, 'return', [])]                               # 0100: 30 instructions to ret
    return {'schema': 1, 'functions': [{'name': 'mod.decodeParentHeader', 'entry': ENTRY, 'end': 0x2000,
                                        'rows': rows}]}


CASES = [('0000', ['0008', '0010']), ('0008', ['000c']), ('000c', ['0010']), ('0010', None),
         ('0018', ['0018', '0020']), ('0020', []), ('0100', [])]
MODULE = 'ZesuSsz.Generated.Fake.FP301.Pilot%sEntries'
# 0018's premises: its own entry and 0020's (two successor entries), plus a callee spec, which is no entry.
PRECONDITIONS = {'0018': ['instr_pre 0x1018 (%s.fp_machineAt0018 (args) (K))%%I' % (MODULE % '0018'),
                          'instr_pre 0x1020 (%s.fp_machineAt0020 (args) (K))%%I' % (MODULE % '0020'),
                          'instr_pre 0x9000 (ZesuSsz.Interfaces.Fake.calleeSpec)%I'],
                 # 0020 ends at the function's return: its return package is a successor entry.
                 '0020': ['instr_pre returnAddress (ZesuSsz.Generated.Fake.FP301.FunctionReturnEntries.'
                          'fp_machineReturn_slot0 args returnAddress K)']}
# Binders counted: fp_machineAt0018_Hist 2 + fp_machineAt0018 1 (fp_machineAt00180 is another entry),
# fp_machineAt0020 2: five in all.
ENTRIES = {'0018': 'Definition fp_machineAt0018_Hist (a : Z) : Prop := (∃ (x : bv 64) (y : list byte), x = x).\n'
                   'Definition fp_machineAt0018 (a : Z) : iProp Σ := (∃ (z : bv 64), ⌜z = z⌝)%I.\n'
                   'Definition fp_machineAt00180 (a : Z) : Prop := (∃ (u : Z) (v : Z), u = v).\n',
           '0020': 'Definition fp_machineAt0020 (a : Z) : Prop := (∃ (p : Z), ∃ (q : bv 8), p = p).\n'}
# 0020's return package: fp_machineReturn_slot0_Hist 2 + fp_machineReturn_slot0 1 (slot1 is another package).
RETURN_ENTRIES = ('Definition fp_machineReturn_slot0_Hist (a : Z) : Prop := (∃ (x : Z) (y : Z), x = y).\n'
                  'Definition fp_machineReturn_slot0 (a : Z) : iProp Σ := (∃ (z : bv 64), ⌜z = z⌝)%I.\n'
                  'Definition fp_machineReturn_slot1 (a : Z) : Prop := (∃ (u : Z), u = u).\n')


class MakeSet(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='mkset-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.callers = self.root / 'tools' / 'block' / 'generated' / 'fake_callers'
        self.callers.mkdir(parents=True)
        rows = []
        for case, successors in CASES:
            pc = '%#x' % (ENTRY + int(case, 16))
            if successors is None:
                rows.append({'case': case, 'pc': pc, 'successors': [], 'status': 'inlined'})
                continue
            rows.append({'case': case, 'pc': pc, 'successors': successors, 'status': 'rendered',
                         'preconditions': PRECONDITIONS.get(case, [])})
            (self.callers / ('Caller%s.v' % case)).write_text('')
        entries = self.root / 'ZesuSsz' / 'Generated' / 'Fake' / 'FP301'
        entries.mkdir(parents=True)
        for case, text in ENTRIES.items():
            (entries / ('Pilot%sEntries.v' % case)).write_text(text)
        (entries / 'FunctionReturnEntries.v').write_text(RETURN_ENTRIES)
        (self.callers / 'CALLERS.json').write_text(json.dumps({'function': 'decodeParentHeader', 'rows': rows}))
        self.cfg = self.root / 'cfg.json'
        self.cfg.write_text(json.dumps(fake_cfg()))
        self.output = self.root / 'FAKE.json'

    def make(self, *extra):
        with contextlib.redirect_stdout(io.StringIO()) as printed:
            mkset.main(['decodeParentHeader', str(self.callers), '--name', 'FAKE', '--cfg', str(self.cfg),
                        '--output', str(self.output), *extra])
        return bench.load_set(str(self.output)), printed.getvalue()

    def test_members_and_caps(self):
        data, printed = self.make()
        got = {member['case']: (member['instructions'], member['cpu_seconds'], member['claim_gib'])
               for member in data['members']}
        self.assertEqual(got, {
            '0000': (4, 2400, 9),      # heavy block; walks through the inlined 0010 to its ret; claim from 7.01 GiB
            '0008': (1, 165, 3),       # ends at the call
            '000c': (3, 255, 3),       # jump into the inlined return block
            '0018': (2, 425, 3),       # loop back to its own start; 120 + 45 x 2 + 100 x 2 + 3 x 5
            '0020': (1, 274, 3),       # ends at the return: 120 + 45 x 1 + 100 x 1 + 3 x 3
            '0100': (30, 1200, 3)})    # 120 + 45 x 30 = 1470, capped at 1200
        self.assertEqual(data['caps'], {'cpu_seconds': 2400, 'limit_gib': 24})
        self.assertEqual(data['overlays'], [])
        self.assertTrue(all(member['callers'] == 'fake_callers' and member['why'] for member in data['members']))
        self.assertIn('6 members', printed)

    def test_heavy_patterns(self):
        self.assertTrue(mkset.is_heavy('decodeParentHeader', '0514_slot3'))
        self.assertTrue(mkset.is_heavy('decodeParentHeader', '04ec'))
        self.assertFalse(mkset.is_heavy('decodeParentHeader', '0514'))
        self.assertTrue(mkset.is_heavy('nextUint64', '0000'))
        self.assertFalse(mkset.is_heavy('nextUint64', '0044'))
        self.assertFalse(mkset.is_heavy('decodeItem', '0000'))

    def test_overlay_copied_from_set(self):
        source = self.root / 'SRC.json'
        overlay = {'name': 'decodeParentHeader', 'commit': 'c' * 40, 'branch': 'b', 'why': 'w'}
        source.write_text(json.dumps({'overlays': [overlay, dict(overlay, name='other')]}))
        data, _ = self.make('--overlays-from', str(source))
        self.assertEqual(data['overlays'], [overlay])

    def test_callers_outside_generated_refused(self):
        with self.assertRaises(SystemExit):
            mkset.main(['decodeParentHeader', str(self.root), '--name', 'FAKE', '--cfg', str(self.cfg),
                        '--output', str(self.output)])

    def test_missing_entry_module_refused(self):
        (self.root / 'ZesuSsz' / 'Generated' / 'Fake' / 'FP301' / 'Pilot0020Entries.v').unlink()
        with self.assertRaises(SystemExit):
            self.make()

    def test_profile_name_finds_a_rust_symbol(self):
        symbol = '_RNvNtNtCs1r1jF4enR2T_6ziskos7zisklib2lt'
        cfg = fake_cfg()
        cfg['functions'][0]['name'] = symbol
        self.cfg.write_text(json.dumps(cfg))
        profiles = self.root / 'tools' / 'block' / 'functions'
        profiles.mkdir(parents=True)
        (profiles / 'decodeParentHeader.json').write_text(json.dumps({'cfg_function': symbol}))
        data, _ = self.make()
        self.assertEqual(len(data['members']), 6)
        self.assertTrue(all(member['function'] == 'decodeParentHeader' for member in data['members']))
        (profiles / 'decodeParentHeader.json').write_text(json.dumps({'symbol': symbol}))
        self.assertEqual(len(self.make()[0]['members']), 6)
        (profiles / 'decodeParentHeader.json').unlink()
        with self.assertRaises(SystemExit):
            self.make()


if __name__ == '__main__':
    unittest.main()
