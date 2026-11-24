"""Check the authenticated loop-head selection and its fixed backedge owners."""
import copy
import hashlib
import json
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header
from render_fp301_statements import qualified_fold, render_loop_head
import entry_hist

ROOT = Path(__file__).resolve().parents[2]


class FoldSpelling(unittest.TestCase):
    def test_one_spelling_of_the_fold_in_loop_classes(self):
        short = 'x = ByteWindowFold.zesu_byte_window_fold b n i'
        full = 'x = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold b n i'
        self.assertEqual(qualified_fold(short), full)
        # A fact already in the full spelling (a profile fact a source block states) is kept.
        self.assertEqual(qualified_fold(full), full)
        self.assertEqual(qualified_fold(short + ' /\\ ' + full), full + ' /\\ ' + full)


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
        for block, predecessor in [('00c4', '00b4'), ('0164', '0154')]:
            source = (ROOT / 'tools/block/generated/fp301_callers' / ('Caller' + predecessor + '.v')).read_text()
            self.assertIn('Pilot' + block + 'Entries.fp_machineAt' + block, source)


class WrapLoopHeads(unittest.TestCase):
    """The `entry_hist: wrap` shape of the same loop heads: every fact of a decodeItem loop class is
    visible (no ghost binder, no hidden fact), so the class has no history and keeps the plain shape."""

    def setUp(self):
        self.addCleanup(entry_hist.configure, {'entry_hist': 'wrap'})

    def test_a_class_without_history_keeps_the_plain_shape(self):
        profile = copy.deepcopy(load_profile())
        profile.data.update({'entry_hist': 'wrap', 'frame_slots': False, 'hist_visible': []})
        fixture = json.loads((ROOT / 'tools/block/fixtures/fp301-loop-heads.json').read_text())
        for row in fixture['rows']:
            for structural in [False, True]:
                text = render_loop_head(row['block'], pilot_header(profile), structural, profile)
                self.assertNotIn('Require Import ZesuSsz.Automation2.Hist.', text)
                self.assertNotIn('zesu_hist', text)
                self.assertNotRegex(text, r'\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b')
                committed = (ROOT / ('ZesuSsz/Generated/DecodeItem/FP301/Pilot' + row['block']
                                     + ('Structural' if structural else 'Entries') + '.v')).read_text()
                self.assertEqual(text, committed)

    def test_a_class_shows_the_newest_call_record_and_hides_older_ones(self):
        # The 039c shape: call 13's payload is the loop's input; call 12's record and the named
        # equation of call 13's cursor over call 12's kept length stay in the class history, so the
        # class pins no binder its entry predecessor hides.
        entry_hist.configure({'entry_hist': 'wrap', 'frame_slots': False})
        binders = ('(call12_kept_x20 : bv 64) (call12_after : list byte) (call13_after : list byte) '
                   '(call13_kept_x18 : bv 64) (machine_x11 : bv 64)')
        old = 'decodeItemCallMeaning (f call12_kept_x20) call12_after'
        new = 'decodeItemCallMeaning (f call13_kept_x18) call13_after'
        named = 'zesu_named_eq call13_kept_x18 (bv_sub call12_kept_x20 (g call12_after))'
        guard = 'bv_unsigned (h call13_after) <> (0%Z)'
        link = 'bv_unsigned machine_x11 = (bv_unsigned (w call13_after) + 0)%Z'
        _, _, meta = entry_hist.seal_class(
            'C', 'Definition C ', binders, ['"x11" ↦ᵣ RVal_Bits (machine_x11 : bv 64%N)'],
            [old, new, named, guard, link], [{'name': 'args', 'type': 'A'}],
            {'registers': {'x11': 'machine_x11'}, 'facts': []})
        self.assertEqual(meta['visible'], [new, guard, link])
        self.assertEqual(meta['hidden'], [old, named])
        self.assertIn('call12_kept_x20', [binder['name'] for binder in meta['ghost']])


class LoopClassAccounting(unittest.TestCase):
    """A loop class keeps every pure fact and path condition of its entry edge, or drops it under a
    named rule (join_generalize.check_fact_accounting): no fact vanishes in the class construction."""

    def test_each_entry_fact_is_kept_or_dropped_under_a_named_rule(self):
        from loop_design import class_components
        from symbolic_state import Expr, input_expr, operation
        order = ['x18', 'domain', 'record', 'placeholder', 'array']
        sources = {'x18': '"x18" ↦ᵣ RVal_Bits (k : bv 64%N)', 'domain': '⌜domain args⌝',
                   'record': '⌜zesu_named_eq k (f args)⌝', 'placeholder': '⌜True⌝', 'array': 'a ↦ₘ∗ bytes'}
        kept = operation('=', input_expr('k'), input_expr('args_len'))
        outside = operation('=', input_expr('k'), input_expr('forward_witness_1'))
        unrenderable = Expr('unrendered', (input_expr('k'),), 1)
        owned, pure, conditions, accounting = class_components(
            order, sources, {'x18': 'cursor'}, [kept, outside, unrenderable], {'k', 'cursor', 'i'})
        self.assertEqual(owned, ['"x18" ↦ᵣ RVal_Bits (cursor : bv 64%N)', 'a ↦ₘ∗ bytes'])
        self.assertEqual(pure, ['⌜domain args⌝', '⌜zesu_named_eq k (f args)⌝', '⌜True⌝'])
        self.assertEqual(len(conditions), 1)
        self.assertEqual(accounting['dropped'],
                         [{'component': 'path_condition:1', 'rule': 'outside_class_scope:forward_witness_1'},
                          {'component': 'path_condition:2', 'rule': 'trace_local_witness'}])
        self.assertEqual(accounting['kept'], 3)

    def test_the_closing_continuation_leaf_is_framed_outside_the_class(self):
        # A seed below a loop-owned root closes with the continuation `K`, as a root seed closes with `True`.
        from loop_design import class_components
        sources = {'x18': '"x18" ↦ᵣ RVal_Bits (k : bv 64%N)', 'close': 'K', 'array': 'a ↦ₘ∗ bytes'}
        owned, pure, _, _ = class_components(['x18', 'array', 'close'], sources, {'x18': 'cursor'}, [], {'k', 'cursor'})
        self.assertEqual(owned, ['"x18" ↦ᵣ RVal_Bits (cursor : bv 64%N)', 'a ↦ₘ∗ bytes'])
        self.assertEqual(pure, [])
