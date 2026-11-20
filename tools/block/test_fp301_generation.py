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


if __name__ == "__main__":
    unittest.main()
