"""Generated block callers end with their theorem's assumptions; the wrap entry shape.

The committed decodeItem outputs are pinned against the driver's steps in
test_render_function_steps.py."""
import re
from pathlib import Path
import unittest

import entry_hist

ROOT = Path(__file__).resolve().parents[2]


class GeneratedFP301(unittest.TestCase):
    def test_every_generated_caller_prints_its_theorem_assumptions(self):
        # closure_cert needs `Print Assumptions <theorem>.` last; 16 decodeItem callers lacked it.
        callers = sorted((ROOT / "tools/block/generated").glob("*/Caller*.v"))
        self.assertTrue(callers)
        for path in callers:
            with self.subTest(caller=path.name, directory=path.parent.name):
                text = path.read_text()
                theorem = re.findall(r"^(?:Lemma|Theorem) ([A-Za-z_][A-Za-z0-9_']*)", text, re.M)[-1]
                self.assertTrue(text.endswith("\nPrint Assumptions " + theorem + ".\n"))


class WrapEntryShape(unittest.TestCase):
    """`entry_hist: wrap` on a small entry variant: live binders and visible facts stay in the
    entry, the rest is one sealed history proposition."""

    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap'})

    def test_ghost_binders_and_hidden_facts_move_into_the_history(self):
        plain = [{"name": "args", "type": "A"}, {"name": "returnAddress", "type": "Z"}]
        binders = [{"name": "x", "type": "bv 64"}, {"name": "g", "type": "bv 64"}]
        declarations, body, meta = entry_hist.seal_alternative(
            "e", " (args : A) (returnAddress : Z)", plain, binders, ['reg "x10" x'],
            ["bv_unsigned x < 8", "g = x", "decodeItemCallDomain args"], ["CallDomain"])
        self.assertEqual(declarations, [("e_Hist", "Definition e_Hist (args : A) (returnAddress : Z) (x : bv 64)"
                                         " : Prop := (∃ (g : bv 64), (bv_unsigned x < 8) /\\ (g = x)).\n", "hist")])
        self.assertEqual(body, '(∃ (x : bv 64), (reg "x10" x ∗ ⌜decodeItemCallDomain args⌝'
                               ' ∗ ⌜zesu_hist (e_Hist (args) (returnAddress) (x))⌝))')
        self.assertEqual([binder["name"] for binder in meta["ghost"]], ["g"])

    def test_an_entry_with_every_fact_visible_keeps_the_plain_shape(self):
        plain = [{"name": "args", "type": "A"}, {"name": "returnAddress", "type": "Z"}]
        binders = [{"name": "x", "type": "bv 64"}, {"name": "u", "type": "bv 64"}]
        facts = ["bv_unsigned x < 8", "decodeItemCallDomain args"]
        # Every fact visible and no ghost binder: nothing to seal (decodeItem, hist_pinned [".*"]).
        self.assertIsNone(entry_hist.seal_alternative(
            "e", " (args : A) (returnAddress : Z)", plain, binders, ['reg "x10" x'], facts, [".*"]))
        # One hidden fact: the history is rendered.
        self.assertIsNotNone(entry_hist.seal_alternative(
            "e", " (args : A) (returnAddress : Z)", plain, binders, ['reg "x10" x'], facts, ["CallDomain"]))

    def test_a_loop_class_with_every_fact_visible_keeps_the_plain_shape(self):
        plain = [{"name": "args", "type": "A"}, {"name": "returnAddress", "type": "Z"}]
        arguments = ("c", "Definition c (args : A) (returnAddress : Z) ", "(x : bv 64)",
                     ['reg "x10" x'], ["bv_unsigned x < 8"], plain, {})
        self.assertIsNone(entry_hist.seal_class(*arguments, visible=[".*"]))
        self.assertIsNotNone(entry_hist.seal_class(*arguments, visible=[]))

    def test_a_profile_without_entry_hist_is_refused(self):
        with self.assertRaisesRegex(ValueError, "required key"):
            entry_hist.configure({"frame_slots": False})
        with self.assertRaisesRegex(ValueError, "unknown mode"):
            entry_hist.configure({"entry_hist": "opaque"})

    def _package(self, pieces):
        plain = [{"name": "args", "type": "A"}, {"name": "returnAddress", "type": "Z"}]
        binders = [{"name": "x", "type": "bv 64"}]
        resources = ['r x'] + [address + ' ↦ₘ? ' + value for _, address, value in pieces]
        _, _, meta = entry_hist.seal_alternative(
            "e", " (args : A) (returnAddress : Z)", plain, binders, resources,
            ["bv_unsigned x < 8", "decodeItemCallDomain args"], ["CallDomain"])
        return entry_hist.result_declarations("e", " (args : A) (returnAddress : Z)", plain, meta, pieces,
                                              {"pointer": "R args", "size": 4})

    def test_return_package_renders_its_result_bytes_and_exit_meaning(self):
        declarations = self._package([
            ("unknown_byte_array", "(Z.add (bv_unsigned (R args)) 2%Z)", "(2%Z)"),
            ("byte_array", "(bv_unsigned (R args))", "[bv_extract 0 8 x; bv_extract 8 8 x]"),
            ("unknown_byte_array", "(bv_unsigned (S args))", "(8%Z)")])
        self.assertEqual(declarations, [
            ("e_ResultBytes", "Definition e_ResultBytes (args : A) (returnAddress : Z) (x : bv 64)"
             " (unwritten_2 : list byte) : list byte := (([bv_extract 0 8 x; bv_extract 8 8 x]) ++ unwritten_2).\n",
             "aux"),
            ("e_ExitMeaning", "Definition e_ExitMeaning (M : A -> list byte -> Prop) : Prop := forall"
             " (args : A) (returnAddress : Z) (x : bv 64) (unwritten_2 : list byte),"
             " (zesu_hist (e_Hist (args) (returnAddress) (x))) -> (decodeItemCallDomain args)"
             " -> (length unwritten_2 = 2%nat) -> M args (e_ResultBytes (args) (returnAddress) (x) (unwritten_2)).\n",
             "aux")])

    def test_result_region_with_a_gap_or_an_overlap_is_refused(self):
        with self.assertRaisesRegex(ValueError, "without gap or overlap at 3"):
            self._package([("unknown_byte_array", "(bv_unsigned (R args))", "(2%Z)"),
                           ("unknown_byte_array", "(Z.add (bv_unsigned (R args)) 3%Z)", "(1%Z)")])
        with self.assertRaisesRegex(ValueError, "without gap or overlap at 1"):
            self._package([("unknown_byte_array", "(bv_unsigned (R args))", "(2%Z)"),
                           ("unknown_byte_array", "(Z.add (bv_unsigned (R args)) 1%Z)", "(3%Z)")])
        with self.assertRaisesRegex(ValueError, "cover 2 of 4"):
            self._package([("unknown_byte_array", "(bv_unsigned (R args))", "(2%Z)")])
        with self.assertRaisesRegex(ValueError, "not pointer plus a numeral"):
            self._package([("unknown_byte_array", "(Z.add (bv_unsigned (R args)) k)", "(4%Z)")])

    def test_result_piece_rendered_through_the_array_declaration(self):
        spine = ("Coq.Init.Datatypes.cons ((bv_extract 0%N 8%N x) : bv 8%N)"
                 " (Coq.Init.Datatypes.cons ((bv_extract 8%N 8%N x) : bv 8%N) (@Coq.Init.Datatypes.nil (bv 8%N)))")
        piece = entry_hist.array_definition_piece(
            "isla.ghost_state.mem_mapsto_array_def ((bv_unsigned (R args))) ((DfracOwn 1)) ((" + spine + "))")
        self.assertEqual(piece, ("(bv_unsigned (R args))", "(" + spine + ")"))
        declarations = self._package([("byte_array",) + piece,
                                      ("unknown_byte_array", "(Z.add (bv_unsigned (R args)) 2%Z)", "(2%Z)")])
        self.assertIn("list byte := ((" + spine + ") ++ unwritten_2)", declarations[0][1])


class LiteralWordFold(unittest.TestCase):
    """A word loaded from a frame slot that the forward pass packs as a literal byte list is the
    slot cell's word (`entry_hist.fold_literal_words`)."""

    @staticmethod
    def load(items, start):
        text = '(List.nth ' + str(start + 7) + '%nat ([' + '; '.join(items) + ']) (BV 8%N 0%Z))'
        for index in range(6, -1, -1):
            byte = '(List.nth ' + str(start + index) + '%nat ([' + '; '.join(items) + ']) (BV 8%N 0%Z))'
            text = '(bv_concat ' + str(64 - 8 * index) + '%N ' + text + ' ' + byte + ')'
        return text

    def test_slot_word_folds_to_the_cell_word(self):
        items = ['(bv_extract ' + str(8 * i) + '%N 8%N (saved' + str(w) + ' args))'
                 for w in range(2) for i in range(8)]
        text = '"x8" ↦ᵣ (RVal_Bits (' + self.load(items, 8) + ' : bv 64%N))'
        self.assertEqual(entry_hist.fold_literal_words(text), '"x8" ↦ᵣ (RVal_Bits ((saved1 args) : bv 64%N))')

    def test_unaligned_or_mixed_words_keep_their_bytes(self):
        items = ['(bv_extract ' + str(8 * i) + '%N 8%N (saved' + str(w) + ' args))'
                 for w in range(2) for i in range(8)]
        folded = entry_hist.fold_literal_words(self.load(items, 4))
        # The elements are read (by computation); the bytes of two words stay a concatenation.
        self.assertNotIn('List.nth', folded)
        self.assertTrue(folded.startswith('(bv_concat 64%N'))
        self.assertIn('(bv_extract 24%N 8%N (saved1 args))', folded)
        self.assertIn('(bv_extract 32%N 8%N (saved0 args))', folded)

    def test_symbolic_lists_and_out_of_range_indices_stay(self):
        for text in ['(List.nth 3%nat (nextResultBytes r) (BV 8%N 0%Z))',
                     '(List.nth 2%nat ([a; b]) (BV 8%N 0%Z))',
                     '(List.nth 0%nat ([]) (BV 8%N 0%Z))']:
            self.assertEqual(entry_hist.fold_literal_words(text), text)
        self.assertEqual(entry_hist.fold_literal_words('(List.nth 1%nat ([a; (f [b; c])]) d)'), '(f [b; c])')


if __name__ == "__main__":
    unittest.main()
