"""Machine runs of run.py: the recorded decodeParentHeader evidence, txAccessList and the array-list regions."""
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
try:
    import run  # noqa: E402
except ImportError as missing:  # unicorn or pyelftools absent
    run, MISSING = None, str(missing)
else:
    MISSING = ''

ROOT = HERE.parents[2]
EVIDENCE = ROOT / 'ZesuSsz' / 'Evidence' / 'PARENT_HEADER_EMULATION.json'


def rows(function):
    return json.loads((HERE / 'inputs' / f'{function}.json').read_text())['inputs']


@unittest.skipIf(run is None, f'machine runs need unicorn and pyelftools: {MISSING}')
class MachineRuns(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.elf = run.Elf(run.DEFAULT_ELF)

    def results(self, function, **kw):
        return {r['id']: run.run_one(self.elf, function, r, **kw).result() for r in rows(function)}

    def test_parent_header_reproduces_recorded_evidence(self):
        evidence = json.loads(EVIDENCE.read_text())
        self.assertEqual(evidence['elf_sha256'], self.elf.sha256)
        entry = self.elf.sym('rlp_decode.decodeParentHeader')
        relative = lambda text: re.sub(r'0x([0-9a-f]{8})',  # noqa: E731
                                       lambda m: f'+{int(m.group(1), 16) - entry:#06x}', text)
        got = self.results('decodeParentHeader')
        recorded = [r for group in ('controls', 'witnesses', 'outer_wraps') for r in evidence[group]]
        self.assertEqual(sorted(got), sorted(r['label'] for r in recorded))
        for rec in recorded:
            with self.subTest(rec['label']):
                res = got[rec['label']]
                self.assertEqual(res['stop'], 'returned')
                self.assertEqual(res['outcome']['result'], rec['result'])
                self.assertEqual(res['outcome']['result_hex'], rec['result_hex'])
                self.assertEqual(res['outcome']['exit'], relative(rec['exit']))
                self.assertEqual(res['oob_reads'], rec['oob_reads'])
                self.assertTrue(res['sp_restored'] and res['callee_saved_ok'])

    def test_tx_access_list_inputs(self):
        for rid, res in self.results('txAccessList').items():
            with self.subTest(rid):
                self.assertEqual(res['stop'], 'returned')
                self.assertTrue(res['expect_ok'], res['outcome'])
                self.assertEqual((res['oob_reads'], res['writes_oob']), (0, []))
                self.assertTrue(res['sp_restored'] and res['callee_saved_ok'])
        got = self.results('txAccessList')
        self.assertEqual(got['two_entries_1_3_keys']['outcome']['key_counts'], [1, 3])
        for rid in ('not_a_list', 'address_19_bytes', 'key_31_bytes', 'truncated_entry', 'trailing_byte'):
            self.assertEqual(got[rid]['outcome']['kind'], 'Error')

    def test_tx_access_list_allocation_failure(self):
        for rid, res in self.results('txAccessList', alloc_fail=1).items():
            with self.subTest(rid):
                allocates = any(a['op'] == 'alloc' for a in res['allocator'])
                self.assertEqual(res['alloc_failed'], allocates)
                if allocates:
                    self.assertIn(0, [a['ptr'] for a in res['allocator'] if a['op'] == 'alloc'])
                    self.assertEqual(res['outcome']['kind'], 'Error')
                self.assertTrue(res['expect_ok'], res['outcome'])

    def test_snapshots_one_row_per_visit(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            chosen = [r for r in rows('txAccessList') if r['id'] in ('two_entries_1_3_keys', 'three_entries_0_keys')]
            run.write_run(self.elf, 'txAccessList', chosen, out, [0xc4, 0x18c, 0x2ec], None, 'top', 2_000_000)
            snap = json.loads((out / 'exec' / 'two_entries_1_3_keys' / 'STATE-018c.json').read_text())
            self.assertEqual((snap['schema'], snap['offset'], len(snap['visits'])), ('oblig-exec-snapshot/1', '+0x018c', 4))
            visit = snap['visits'][1]
            self.assertEqual(len(visit['regs']), 32)
            self.assertEqual(visit['regs']['pc'], self.elf.sym('rlp_decode.txAccessList') + 0x18c)
            names = {m['name'] for m in visit['memory']}
            self.assertLessEqual({'input', 'rest', 'allocator', 'vtable', 'result', 'frame', 'zisk-scratch'}, names)
            frame = next(m for m in visit['memory'] if m['name'] == 'frame')
            self.assertEqual(len(bytes.fromhex(frame['hex'])), frame['size'])
            self.assertFalse((out / 'exec' / 'two_entries_1_3_keys' / 'STATE-02ec.json').exists())
            self.assertTrue((out / 'exec' / 'three_entries_0_keys' / 'STATE-02ec.json').exists())

    def test_array_list_regions(self):
        for function in ('keysToOwnedSlice', 'entriesToOwnedSlice', 'keysEnsureCapacity'):
            for kw in ({}, {'alloc_fail': 1, 'remap': 'never'}):
                for rid, res in self.results(function, **kw).items():
                    with self.subTest(function=function, input=rid, **kw):
                        self.assertEqual(res['stop'], 'returned')
                        self.assertTrue(res['expect_ok'], res['outcome'])
                        self.assertEqual((res['oob_reads'], res['writes_oob']), (0, []))
                        self.assertTrue(all('note' not in a for a in res['allocator']), res['allocator'])

    def test_decode_item_inputs(self):
        got = self.results('decodeItem', at=[0xc4, 0x164])
        for rid, res in got.items():
            with self.subTest(rid):
                self.assertEqual(res['stop'], 'returned')
                self.assertIsNot(res['expect_ok'], False, res['outcome'])
                self.assertEqual((res['oob_reads'], res['writes_oob']), (0, []))
                self.assertTrue(res['sp_restored'] and res['callee_saved_ok'])
        # Both length-of-length loops run once per length byte, 8 at most; the longest run fetches 75.
        self.assertEqual(got['long_string_lol8_too_long']['visits']['+0x00c4'], 8)
        self.assertEqual(got['long_list_lol8_too_long']['visits']['+0x0164'], 8)
        self.assertEqual(max(res['insns'] for res in got.values()), 75)

    def test_offsets_outside_function_refused(self):
        size = self.elf.symbols['rlp_decode.txAccessList'][1]
        self.assertEqual(run.parse_offsets('+0xc4,0x18c', size), [0xc4, 0x18c])
        with self.assertRaises(SystemExit):
            run.parse_offsets(f'+{size:#x}', size)


if __name__ == '__main__':
    unittest.main()
