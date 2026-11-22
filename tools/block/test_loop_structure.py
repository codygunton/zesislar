"""Natural loops of nested CFGs, and stop reachability that does not cross a back edge."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from boundary_guards import BoundaryRefused, annotate_reaching_stops, require_complete_boundary
from loop_design import cursor_extent, cursor_stride
from loop_infer import infer_designs
from loop_structure import back_edges, cursor_width, forward_successors, loop_heads, natural_loops


def function(edges, entry=0, loops=()):
    starts = sorted({pc for pc in edges} | {t for targets in edges.values() for t in targets})
    return {'name': 'nest', 'entry': entry, 'end': starts[-1] + 4,
            'rows': [{'pc': pc} for pc in starts],
            'blocks': [{'start': pc, 'end': pc + 4, 'successors': edges.get(pc, [])} for pc in starts],
            'loops': list(loops)}


# The shape of one mem.rotate nest: outer head 16, inner head 32 that loops on itself, outer latch 48.
NEST = function({0: [16], 16: [32], 32: [32, 48], 48: [16, 64], 64: []},
                loops=[{'minimum_pc': hex(16)}])
# An inner loop with two exits (to the outer latch and out of both loops) and an outer head with
# two back edges.
TWO_EXITS = function({0: [16], 16: [32], 32: [40, 80], 40: [32, 48], 48: [16, 56], 56: [16, 64],
                      64: [], 80: []})
# Three deep.
DEEP = function({0: [8], 8: [16], 16: [24], 24: [24, 32], 32: [16, 40], 40: [8, 48], 48: []})


def rows(func):
    return {row['head']: row for row in natural_loops(func)}


class NaturalLoops(unittest.TestCase):
    def test_inner_head_is_its_own_loop(self):
        loops = rows(NEST)
        self.assertEqual(sorted(loops), [16, 32])
        self.assertEqual(loops[32]['parent'], 16)
        self.assertEqual(loops[32]['depth'], 2)
        self.assertEqual(loops[32]['entry_edges'], [(16, 32)])
        self.assertEqual(loops[32]['exit_edges'], [(32, 48)])
        self.assertEqual(loops[32]['back_edges'], [(32, 32)])
        self.assertEqual(loops[16]['back_edges'], [(48, 16)])
        self.assertEqual(loops[16]['entry_edges'], [(0, 16)])
        self.assertEqual(loops[16]['body'], [16, 32, 48])
        # The SCC row names only the outer head; the inner head is a loop head too.
        self.assertEqual(loop_heads(NEST), {16, 32})

    def test_two_back_edges_and_two_inner_exits(self):
        loops = rows(TWO_EXITS)
        self.assertEqual(sorted(loops), [16, 32])
        self.assertEqual(loops[16]['back_edges'], [(48, 16), (56, 16)])
        self.assertEqual(loops[32]['back_edges'], [(40, 32)])
        self.assertEqual(loops[32]['exit_edges'], [(32, 80), (40, 48)])
        self.assertEqual(loops[32]['parent'], 16)
        self.assertEqual(loops[16]['exit_edges'], [(32, 80), (56, 64)])

    def test_three_deep(self):
        loops = rows(DEEP)
        self.assertEqual({head: row['depth'] for head, row in loops.items()}, {8: 1, 16: 2, 24: 3})
        self.assertEqual({head: row['parent'] for head, row in loops.items()}, {8: None, 16: 8, 24: 16})

    def test_forward_cfg_is_acyclic(self):
        for func in (NEST, TWO_EXITS, DEEP):
            successors = forward_successors(func)
            state = {}

            def visit(node):
                state[node] = 'open'
                for child in successors[node]:
                    self.assertNotEqual(state.get(child), 'open', 'cycle through %d' % child)
                    if child not in state:
                        visit(child)
                state[node] = 'done'
            visit(func['entry'])
            self.assertEqual(sum(len(v) for v in successors.values()) + len(back_edges(func)),
                             sum(len(b['successors']) for b in func['blocks']))


def report(func, stops, seeded):
    return {'boundaries': [{'pc': hex(b['start']), 'status': 'generated',
                            'alternatives': [{'predecessor_pc': None if b['start'] in seeded else '0x0'}]}
                           for b in func['blocks']], 'stops': stops}


def cut(block, target):
    return {'reason': 'handwritten_cut', 'block_pc': hex(block), 'instruction_pc': hex(block),
            'seed_pc': hex(block), 'path': [], 'target_pc': hex(target)}


def refused(result, pc):
    try:
        require_complete_boundary(next(row for row in result['boundaries'] if row['pc'] == hex(pc)))
    except BoundaryRefused:
        return True
    return False


class NestedReachability(unittest.TestCase):
    def test_unseeded_inner_head_does_not_block_its_entry(self):
        # The outer head 16 is seeded; the pass stops at the unseeded inner head 32. The inner
        # head's entry edge (from 16) is complete: the stop reaches 16 only through the outer
        # back edge, which no longer counts. The inner head itself and what follows it are refused.
        result = annotate_reaching_stops(report(NEST, [cut(16, 32)], {0, 16}), NEST)
        self.assertFalse(refused(result, 16))
        for pc in (32, 48, 64):
            self.assertTrue(refused(result, pc), pc)
        # Once the inner head has its seed, nothing is refused.
        result = annotate_reaching_stops(report(NEST, [cut(16, 32), cut(32, 32)], {0, 16, 32}), NEST)
        self.assertEqual([pc for pc in (0, 16, 32, 48, 64) if refused(result, pc)], [])

    def test_stop_in_inner_body_reaches_the_outer_exit_not_the_outer_head(self):
        stop = {'reason': 'state_check', 'block_pc': hex(40), 'instruction_pc': hex(40), 'seed_pc': hex(32),
                'path': []}
        result = annotate_reaching_stops(report(TWO_EXITS, [stop], {0, 16, 32}), TWO_EXITS)
        self.assertEqual([pc for pc in (16, 32, 40, 48, 56, 64, 80) if refused(result, pc)], [40, 48, 56, 64])


def word_loop(load, stride):
    """A one-block loop at 16: `load` at x13 (and at x15), both cursors advanced by `stride`."""
    rows = [{'pc': 0, 'mnemonic': 'addi', 'rd': 5, 'rs1': 0, 'imm': 0},
            {'pc': 16, 'mnemonic': load, 'rd': 6, 'rs1': 13, 'imm': 0},
            {'pc': 20, 'mnemonic': load, 'rd': 7, 'rs1': 15, 'imm': 0},
            {'pc': 24, 'mnemonic': 'addi', 'rd': 13, 'rs1': 13, 'imm': stride},
            {'pc': 28, 'mnemonic': load, 'rd': 8, 'rs1': 13, 'imm': -stride},
            {'pc': 32, 'mnemonic': 'bne', 'rd': 0, 'rs1': 6, 'rs2': 7, 'imm': 0},
            {'pc': 36, 'mnemonic': 'ret'}]
    return {'name': 'words', 'entry': 0, 'end': 40, 'rows': rows,
            'blocks': [{'start': 0, 'end': 16, 'successors': [16]},
                       {'start': 16, 'end': 36, 'successors': [16, 36]},
                       {'start': 36, 'end': 40, 'successors': []}], 'loops': []}


def design(stride, **cursor):
    link = 'bv_unsigned loop_x13 = (bv_unsigned {x13} + %si)%%Z' % ('' if stride == 1 else '%d * ' % stride)
    return {'head': '16', '_head': 16, 'index': 'i', 'registers': {'x13': 'loop_x13'},
            'facts': [{'kind': 'index_link', 'coq': link}], 'array_cursor': [{'register': 'x13', **cursor}]}


class CursorWidth(unittest.TestCase):
    def test_byte_cursor_unchanged(self):
        func = word_loop('lbu', 1)
        self.assertEqual(cursor_stride(design(1), 'x13'), 1)
        self.assertEqual(cursor_width(func, 16, 'x13', 1), 1)
        self.assertEqual(cursor_extent(design(1), design(1)['array_cursor'][0], func), 1)
        # Without the function's rows (an old caller) the extent stays one byte.
        self.assertEqual(cursor_extent(design(1), design(1)['array_cursor'][0], None), 1)

    def test_word_cursor_covers_its_window(self):
        func = word_loop('ld', 8)
        self.assertEqual(cursor_stride(design(8), 'x13'), 8)
        # The load after the increment (offset -8 from the new value) does not count: the
        # register no longer holds the cursor there.
        self.assertEqual(cursor_width(func, 16, 'x13', 8), 8)
        self.assertEqual(cursor_extent(design(8), design(8)['array_cursor'][0], func), 8)
        self.assertEqual(cursor_width(func, 16, 'x15', 8), 8)

    def test_window_wider_than_stride_is_refused(self):
        func = word_loop('ld', 1)
        with self.assertRaisesRegex(ValueError, r'accesses 8 bytes at its cursor x13 per iteration with stride 1'):
            cursor_extent(design(1), design(1)['array_cursor'][0], func)
        # A design that states the window takes responsibility for its bound.
        self.assertEqual(cursor_extent(design(1), design(1, width=8)['array_cursor'][0], func), 8)

    def test_access_before_the_cursor_is_refused(self):
        func = word_loop('lbu', 1)
        func['rows'][1] = {**func['rows'][1], 'imm': -1}
        with self.assertRaisesRegex(ValueError, 'before its cursor x13'):
            cursor_width(func, 16, 'x13', 1)


def compare_loop():
    """mem.eql's word loop: two 8-byte loads, both cursors advance by 8, `bltu x13, x14` back."""
    rows = [{'pc': 0, 'mnemonic': 'addi', 'rd': 5, 'rs1': 0, 'imm': 0},
            {'pc': 16, 'mnemonic': 'ld', 'rd': 6, 'rs1': 13, 'imm': 0},
            {'pc': 20, 'mnemonic': 'ld', 'rd': 7, 'rs1': 15, 'imm': 0},
            {'pc': 24, 'mnemonic': 'addi', 'rd': 13, 'rs1': 13, 'imm': 8},
            {'pc': 28, 'mnemonic': 'addi', 'rd': 15, 'rs1': 15, 'imm': 8},
            {'pc': 32, 'mnemonic': 'bltu', 'rs1': 13, 'rs2': 14, 'imm': 9, 'size': 4, 'successors': [16, 36]},
            {'pc': 36, 'mnemonic': 'ret'}]
    return {'name': 'cmp', 'entry': 0, 'end': 40, 'rows': rows,
            'blocks': [{'start': 0, 'end': 16, 'successors': [16]},
                       {'start': 16, 'end': 36, 'successors': [16, 36]},
                       {'start': 36, 'end': 40, 'successors': []}], 'loops': []}


class InferredDesign(unittest.TestCase):
    def test_cursor_loop_structure(self):
        func = compare_loop()
        designs, refusals = infer_designs(func, [], liveness={hex(16): {'x6', 'x7', 'x13', 'x14', 'x15'}})
        self.assertEqual(refusals, {})
        design, = designs
        self.assertEqual((design['head'], design['entry_predecessor'], design['index']), ('0x10', '0x0', 'i'))
        self.assertEqual(design['registers'], {'x6': 'loop_x6', 'x7': 'loop_x7', 'x13': 'loop_x13',
                                               'x15': 'loop_x15'})
        self.assertEqual([row['coq'] for row in design['facts']], [
            '(0 <= i)%Z',
            'bv_unsigned loop_x13 = ((bv_unsigned {x13} + 8 * i) mod 2 ^ 64)%Z',
            'bv_unsigned loop_x15 = ((bv_unsigned {x15} + 8 * i) mod 2 ^ 64)%Z',
            '(i = 0 \\/ bv_unsigned loop_x13 < bv_unsigned {x14})%Z'])
        self.assertEqual([(row['register'], row['array'], row['stride']) for row in design['array_cursor']],
                         [('x13', None, 8), ('x15', None, 8)])
        cursor = design['array_cursor'][0]
        self.assertEqual(cursor_extent({**design, '_head': 16}, cursor, func), 8)

    def test_hand_design_wins_and_dead_registers_drop(self):
        func = compare_loop()
        self.assertEqual(infer_designs(func, [{'head': '0x10'}]), ([], {}))
        design, = infer_designs(func, [], liveness={hex(16): {'x13', 'x14'}})[0]
        self.assertEqual(sorted(design['registers']), ['x13'])

    def test_nested_inner_index_and_refusal(self):
        func = function({0: [16], 16: [32], 32: [32, 48], 48: [16, 64], 64: []})
        designs, refusals = infer_designs(func, [])
        self.assertEqual([(row['head'], row['index'], row['entry_predecessor']) for row in designs],
                         [('0x10', 'i', '0x0'), ('0x20', 'i2', '0x10')])
        two_entries = function({0: [8, 16], 8: [16], 16: [16, 24], 24: []})
        designs, refusals = infer_designs(two_entries, [])
        self.assertEqual(designs, [])
        self.assertRegex(refusals['0x10'], 'has 2 entry edges')


class InferredRows(unittest.TestCase):
    def test_unseeded_inferred_head_is_refused_not_fatal(self):
        import json, tempfile
        from loop_design import loop_head_rows

        class Profile(dict):
            def pc(self, key):
                return key
        report = {'boundaries': [{'pc': '0x10', 'alternatives': []}]}
        inferred = {'head': '0x10', 'entry_predecessor': '0x0', 'registers': {}, 'index': 'i', 'facts': [],
                    'inferred': True}
        with tempfile.TemporaryDirectory() as directory:
            forward = Path(directory) / 'FORWARD.json'
            forward.write_text(json.dumps(report))
            (Path(directory) / 'LOOP-DESIGNS.json').write_text(json.dumps({'designs': [inferred], 'refusals': {}}))
            rows = loop_head_rows(report, forward, Profile())
            self.assertEqual(rows['rows'], [])
            self.assertRegex(rows['inferred_refusals']['0x10'], 'exactly one entry edge')
            # A hand design with the same defect still stops the render.
            with self.assertRaisesRegex(ValueError, 'exactly one entry edge'):
                loop_head_rows(report, forward, Profile(loop_designs=[{**inferred, 'inferred': False}]))
            (Path(directory) / 'LOOP-DESIGNS.json').unlink()
            self.assertEqual(loop_head_rows(report, forward, Profile()),
                             {'schema': 'fp301-authenticated-loop-heads-v1', 'rows': []})


if __name__ == '__main__':
    unittest.main()
