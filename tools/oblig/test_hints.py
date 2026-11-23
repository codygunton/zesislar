"""Tests of the hint pack builder (tools/oblig/hints.py)."""
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hints  # noqa: E402

ADDRESS = re.compile(r'0x800[0-9a-f]{5}|2148[0-9]{6}|21474[0-9]{5}')


def expr(ops):
    from elftools.dwarf.dwarf_expr import DWARFExprParser
    from elftools.dwarf.structs import DWARFStructs
    structs = DWARFStructs(little_endian=True, dwarf_format=32, address_size=8)
    return DWARFExprParser(structs).parse_expr(ops)


def i_type(rd, rs1, imm, op=0x13, f3=0):
    return (imm & 0xfff) << 20 | rs1 << 15 | f3 << 12 | rd << 7 | op


def row(pc, word, **extra):
    fields = {'pc': pc, 'size': 4, 'word': word, 'rd': word >> 7 & 31, 'rs1': word >> 15 & 31,
              'rs2': word >> 20 & 31, 'kind': 'plain'}
    fields.update(extra)
    return fields


class LocationTests(unittest.TestCase):
    def test_register(self):
        self.assertEqual(hints.decode_location(expr([0x50 + 9]), 's0'),
                         {'kind': 'register', 'register': 's1'})

    def test_frame_base_slot(self):
        location = hints.decode_location(expr([0x91, 0xc0, 0x7c]), 's0')  # fbreg -448
        self.assertEqual(location, {'kind': 'frame', 'base': 's0', 'offset': -448,
                                    'text': '[s0-0x1c0]'})

    def test_breg_value_and_constant(self):
        self.assertEqual(hints.decode_location(expr([0x72, 0x10, 0x9f]), None),  # breg2 16, stack_value
                         {'kind': 'value', 'text': 'sp+0x10'})
        self.assertEqual(hints.decode_location(expr([0x30, 0x9f]), None),  # lit0, stack_value
                         {'kind': 'constant', 'value': 0})

    def test_pieces(self):
        location = hints.decode_location(expr([0x5a, 0x93, 8, 0x5b, 0x93, 8]), None)
        self.assertEqual(location['kind'], 'pieces')
        self.assertEqual(hints.location_text(location), '{8B: a0, 8B: a1}')


class LivenessTests(unittest.TestCase):
    def test_use_before_def_and_call_clobber(self):
        entry = 0x1000
        rows = [row(entry, i_type(10, 11, 1)),            # addi a0, a1, 1
                row(entry + 4, 0x000080e7, kind='call'),  # jalr ra, 0(ra)
                row(entry + 8, i_type(9, 10, 0)),          # addi s1, a0, 0
                row(entry + 12, 0x00008067, kind='return')]
        function = {'rows': rows, 'calls': [{'pc': entry + 4, 'target': 0x2000}],
                    'blocks': [{'start': entry, 'end': entry + 8, 'successors': [entry + 8]},
                               {'start': entry + 8, 'end': entry + 16, 'successors': []}]}
        live = hints.liveness(function)
        names = lambda regs: {hints.reg_name(r) for r in regs}
        self.assertIn('a1', names(live[entry]))
        self.assertIn('ra', names(live[entry]))
        self.assertIn('a0', names(live[entry + 8]))  # read by the addi and by the return
        self.assertIn('s2', names(live[entry]))      # callee-saved, live at return


class SourceTests(unittest.TestCase):
    TEXT = ('const std = @import("std");\n'
            'fn f(a: u8) !struct { x: u8 } {\n'
            '    if (a > 1) {\n'
            '        return .{ .x = a };\n'
            '    }\n'
            '    return error.Bad;\n'
            '}\n'
            'fn g() void {}\n')

    def test_extent(self):
        self.assertEqual(hints.function_extent(self.TEXT, 'mod.f', 2), (2, 7))
        self.assertEqual(hints.function_extent(self.TEXT, 'g', 8), (8, 8))
        self.assertIsNone(hints.function_extent(self.TEXT, 'h', 2))

    def test_source_key(self):
        self.assertEqual(hints.source_key('/x/_build/p0c-zesu-source/src/a.zig'), 'src/a.zig')
        self.assertEqual(hints.source_key('/usr/lib/zig/std/array_list.zig'), 'std/array_list.zig')


class SliceTests(unittest.TestCase):
    def test_slice_cuts_block_variables_and_types(self):
        entry = 0x10000
        locations = {'function': 'mod.f', 'entry': entry, 'variables': [
            {'name': 'list', 'kind': 'param', 'scope': ['mod.f'], 'type': '*List', 'decl': 'src/a.zig:2',
             'ranges': [{'start': '+0x0', 'end': '+0x8', 'start_address': entry,
                         'end_address': entry + 8, 'location': {'kind': 'register', 'register': 'a0'}}]},
            {'name': 'late', 'kind': 'var', 'scope': ['mod.f'], 'type': 'u8', 'decl': 'src/a.zig:3',
             'ranges': [{'start': '+0x8', 'end': '+0xc', 'start_address': entry + 8,
                         'end_address': entry + 12, 'location': {'kind': 'register', 'register': 'a1'}}]}]}
        types = {'types': {
            'List': {'kind': 'structure', 'byte_size': 24, 'members': [
                {'name': 'items', 'offset': 0, 'size': 16, 'type': '[]u8'},
                {'name': 'capacity', 'offset': 16, 'size': 8, 'type': 'usize'}]},
            '[]u8': {'kind': 'structure', 'byte_size': 16, 'members': [
                {'name': 'ptr', 'offset': 0, 'size': 8, 'type': '*u8'},
                {'name': 'len', 'offset': 8, 'size': 8, 'type': 'usize'}]},
            'Other': {'kind': 'structure', 'byte_size': 1, 'members': []}}}
        blocks = ('# Blocks\n\n## block +0x0..+0x8\n\nfirst\n\n## block +0x8..+0xc\n\nsecond\n')
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp, 'LOCATIONS.json').write_text(json.dumps(locations))
            Path(tmp, 'TYPES.json').write_text(json.dumps(types))
            Path(tmp, 'BLOCKS.md').write_text(blocks)
            text = hints.slice_pack(tmp, ['mod.f+0x4'])
            self.assertIn('first', text)
            self.assertNotIn('second', text)
            self.assertIn('`list`', text)
            self.assertNotIn('`late`', text)
            self.assertIn('`List`', text)
            self.assertIn('`[]u8`', text)
            self.assertNotIn('Other', text)
            with self.assertRaises(SystemExit):
                hints.slice_pack(tmp, ['+0x40'])
            with self.assertRaises(SystemExit):
                hints.slice_pack(tmp, ['other.g+0x4'])


def real_inputs():
    try:
        recipe = json.loads(hints.resolve(hints.RECIPE).read_text())
        obj = hints.resolve(recipe['inputs']['object']['path'])
        source = hints.resolve(recipe['sources']['zesu']['path'])
    except (OSError, KeyError, ValueError):
        return None
    if not (obj.exists() and (source / 'src/stateless/rlp_decode.zig').exists()
            and hints.resolve(hints.ELF).exists() and hints.resolve(hints.CFG).exists()):
        return None
    return obj


@unittest.skipIf(real_inputs() is None, 'stock object or zesu source absent; run fetch_inputs.py')
class RealObjectTests(unittest.TestCase):
    def test_counts(self):
        obj = hints.open_elf(real_inputs())
        self.assertEqual(hints.counts(obj.get_dwarf_info(relocate_dwarf_sections=False)),
                         {'structure_types': 502, 'members': 1640, 'location_entries': 23301})

    def test_tx_access_list_pack(self):
        with tempfile.TemporaryDirectory() as tmp:
            hints.main(['build', '--function', 'txAccessList', '--run', tmp])
            out = Path(tmp, 'hints')
            source = (out / 'SOURCE.md').read_text()
            self.assertIn('src/stateless/rlp_decode.zig:485-538', source)
            self.assertIn('return entries.toOwnedSlice(alloc)', source)
            locations = json.loads((out / 'LOCATIONS.json').read_text())
            own = {v['name'] for v in locations['variables'] if v['scope'] == ['rlp_decode.txAccessList']}
            self.assertTrue({'alloc', 'rest', 'entries', 'keys', 'al', 'kp'} <= own, own)
            types = json.loads((out / 'TYPES.json').read_text())['types']
            entry = types['input.AccessListEntry']
            self.assertEqual({m['name'] for m in entry['members']}, {'address', 'storage_keys'})
            blocks = (out / 'BLOCKS.md').read_text()
            self.assertEqual(blocks.count('\n## block '), 53)
            self.assertIn('call rlp.decodeItem', blocks)
            for name in ('SOURCE.md', 'BLOCKS.md'):
                self.assertIsNone(ADDRESS.search((out / name).read_text()), name)
            text = hints.slice_pack(out, ['+0x1f4'])
            self.assertIn('ensureTotalCapacity', text)


if __name__ == '__main__':
    unittest.main()
