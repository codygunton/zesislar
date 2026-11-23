"""Relocatable residual modules: ZesuSsz/Residuals/<function>/Block<offset>.v beside the original form."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "residuals"))
sys.path.insert(0, str(ROOT / "tools" / "block"))

from check_decode_item_hints import residual_errors
from check_proof_hygiene import residual_module_failures
from render_residual_module import (RenderError, module_file, module_name, module_of_rows, parse_module,
                                    render_from_goals)

HEADER = "Require Import ZesuSsz.Automation2.All.\nFrom Coq Require Import ZArith.ZArith.\nLocal Open Scope Z_scope.\n\n"
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"
PROOF = "intros.\n  lia.\nQed.\n"
OLD = "Lemma residual_1234_{h} :\n  forall (x : Z) (H0 : 0 <= x), 0 <= x + {n}.\nProof.\n"
NEW = "Lemma residual_txAccessList_00c4_{h} :\n  forall (x : Z) (H0 : 0 <= x), 0 <= x + {n}.\nProof.\n"


def goal_dir(root, label, statement):
    d = Path(root) / label
    d.mkdir()
    (d / "goal.v").write_text(HEADER + statement + SLOT)
    (d / "proof.v").write_text(HEADER + statement + PROOF)


class RelocatableRenderTests(unittest.TestCase):
    def test_module_paths_of_both_forms(self):
        self.assertEqual(module_name("6960"), "Block800d6960")
        self.assertEqual(module_file("6960"), "ZesuSsz/Residuals/Block800d6960.v")
        self.assertEqual(module_name("00c4", "txAccessList"), "txAccessList.Block00c4")
        self.assertEqual(module_file("00c4", "txAccessList"), "ZesuSsz/Residuals/txAccessList/Block00c4.v")
        for function, block in (("tx_access", "00c4"), ("txAccessList", "c4"), ("9x", "00c4")):
            with self.subTest(function=function, block=block), self.assertRaises(RenderError):
                module_name(block, function)

    def test_new_form_renders_round_trips_and_passes_hygiene(self):
        with tempfile.TemporaryDirectory() as root:
            for n in (1, 2):
                goal_dir(root, "00c4-%d" % n, NEW.format(h="%016x" % n, n=n))
            text = render_from_goals("00c4", root, function="txAccessList")
        block, _, rows = parse_module(text)
        self.assertEqual((block, len(rows)), ("00c4", 2))
        self.assertEqual(module_of_rows(rows), ("00c4", "txAccessList"))
        self.assertEqual(text.count("#[export] Hint Resolve residual_txAccessList_00c4_"), 2)
        self.assertEqual(residual_module_failures("ZesuSsz/Residuals/txAccessList/Block00c4.v", text), [])
        for wrong in ("ZesuSsz/Residuals/Block800d00c4.v", "ZesuSsz/Residuals/txAccessList/Block00c8.v",
                      "ZesuSsz/Residuals/keysToOwnedSlice/Block00c4.v"):
            with self.subTest(wrong=wrong):
                self.assertTrue(residual_module_failures(wrong, text))

    def test_old_form_still_renders(self):
        with tempfile.TemporaryDirectory() as root:
            goal_dir(root, "1234-1", OLD.format(h="0001", n=1))
            text = render_from_goals("1234", root)
        self.assertEqual(module_of_rows(parse_module(text)[2]), ("1234", None))
        self.assertEqual(residual_module_failures("ZesuSsz/Residuals/Block800d1234.v", text), [])
        self.assertTrue(residual_module_failures("ZesuSsz/Residuals/x/Block1234.v", text))

    def test_names_must_match_the_requested_form(self):
        cases = [("txAccessList", OLD.format(h="0001", n=1), "00c4-1"),  # old name in a new module
                 (None, NEW.format(h="%016x" % 1, n=1), "00c4-1"),        # new name in an old module
                 ("keysToOwnedSlice", NEW.format(h="%016x" % 1, n=1), "00c4-1"),
                 ("txAccessList", NEW.format(h="0001", n=1), "00c4-1")]   # short hash
        for function, statement, label in cases:
            with self.subTest(function=function, statement=statement[:40]), tempfile.TemporaryDirectory() as root:
                goal_dir(root, label, statement)
                with self.assertRaises(RenderError):
                    render_from_goals("00c4", root, function=function)

    def test_a_module_mixing_forms_is_refused(self):
        with tempfile.TemporaryDirectory() as root:
            for n in (1, 2):
                goal_dir(root, "00c4-%d" % n, NEW.format(h="%016x" % n, n=n))
            text = render_from_goals("00c4", root, function="txAccessList")
        mixed = text.replace("residual_txAccessList_00c4_0000000000000002", "residual_00c4_0000000000000002")
        with self.assertRaises(RenderError):
            parse_module(mixed)
        self.assertTrue(residual_module_failures("ZesuSsz/Residuals/txAccessList/Block00c4.v", mixed))

    def test_existing_residual_modules_stay_accepted(self):
        files = sorted((ROOT / "ZesuSsz/Residuals").glob("*.v"))
        self.assertEqual(len(files), 16)
        for path in files:
            name = str(path.relative_to(ROOT))
            with self.subTest(name=name):
                self.assertEqual(residual_module_failures(name, path.read_text()), [])


class RelocatablePolicyTests(unittest.TestCase):
    MODULE = ("Require Import ZesuSsz.Automation2.All.\n"
              "#[export] Hint Resolve residual_txAccessList_00c4_0123456789abcdef : zesu_residual.\n")

    def tree(self, files):
        root = Path(tempfile.mkdtemp())
        for name, text in files.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text)
        return root

    def test_new_form_module_is_a_residual_module(self):
        root = self.tree({"ZesuSsz/Residuals/txAccessList/Block00c4.v": self.MODULE})
        self.assertEqual(residual_errors(root), [])

    def test_other_layouts_and_importers_are_refused(self):
        root = self.tree({
            "ZesuSsz/Residuals/txAccessList/Block00c4.v": self.MODULE + "#[export] Hint Resolve foo : core.\n",
            "ZesuSsz/Residuals/tx_access/Block00c4.v": self.MODULE,
            "ZesuSsz/Residuals/a/b/Block00c4.v": self.MODULE,
            "ZesuSsz/Residuals/Block00c4.v": self.MODULE,
            "ZesuSsz/Proofs/P.v": "Require Import ZesuSsz.Residuals.txAccessList.Block00c4.\n",
        })
        errors = "\n".join(residual_errors(root))
        self.assertIn("ZesuSsz.Residuals.txAccessList.Block00c4 registers a hint other than", errors)
        self.assertIn("not Block<address> or <function>/Block<offset>: ZesuSsz.Residuals.tx_access.Block00c4", errors)
        self.assertIn("ZesuSsz.Residuals.a.b.Block00c4", errors)
        self.assertIn("not Block<address> or <function>/Block<offset>: ZesuSsz.Residuals.Block00c4.", errors)
        self.assertIn("ZesuSsz.Proofs.P imports residual module ZesuSsz.Residuals.txAccessList.Block00c4", errors)


if __name__ == "__main__":
    unittest.main()
