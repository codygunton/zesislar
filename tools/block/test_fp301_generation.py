"""Reject stale committed FP301 declarations and generated block callers."""
import hashlib
import json
import re
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header, return_header
from render_fp301_statements import render_caller, render_declaration
import entry_hist

ROOT = Path(__file__).resolve().parents[2]


class GeneratedFP301(unittest.TestCase):
    def test_committed_outputs_match_renderer(self):
        inputs = json.loads((ROOT / "tools/block/fixtures/fp301-generation.json").read_text())
        self.assertEqual(len(inputs["callers"]), 16)
        profile = load_profile()
        headers = {"pilot": pilot_header(profile), "return": return_header(profile)}
        for group in ["callers", "declarations"]:
            for row in inputs[group]:
                with self.subTest(output=row["output"]):
                    source = row["canonical_source"]
                    self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                                     row["canonical_sha256"])
                    expected = (render_caller(source) if group == "callers" else
                                render_declaration(source, headers[row["header_kind"]]))
                    self.assertEqual((ROOT / row["output"]).read_text(), expected)

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
    entry, the rest is one sealed history proposition; the legacy shape is the pinned test above."""

    def setUp(self):
        entry_hist.configure({'entry_hist': 'wrap'})
        self.addCleanup(entry_hist.configure, None)

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


if __name__ == "__main__":
    unittest.main()
