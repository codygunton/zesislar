"""Residual lemma modules: renderer, caller import, and policy checks."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "residuals"))
sys.path.insert(0, str(ROOT / "tools" / "block"))

from check_decode_item_hints import residual_errors
from check_proof_hygiene import residual_module_failures
from render_residual_module import (RenderError, parse_module, parse_shared_module, render_from_goals,
                                    render_shared_from_goals)
from render_fp301_statements import residual_import

HEADER = """Require Import ZesuSsz.Automation2.All.
From Coq Require Import ZArith.ZArith.
Local Open Scope Z_scope.

Definition DesignedEntry_800d1234 (x : Z) : Prop := True.

"""
STATEMENT = "Lemma residual_1234_{h} :\n  forall (x : Z) (H0 : 0 <= x), 0 <= x + {n}.\nProof.\n"
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"
PROOF = "intros.\n  (* copied as is *) lia.\nQed.\n"


def goal_dir(root, n, proof=PROOF, header=HEADER):
    d = Path(root) / ("1234-%d" % n)
    d.mkdir()
    statement = header + STATEMENT.format(h="%04x" % n, n=n)
    (d / "goal.v").write_text(statement + SLOT)
    (d / "proof.v").write_text(statement + proof)
    return d


class RendererTests(unittest.TestCase):
    def test_proofs_are_copied_byte_for_byte_and_round_trip(self):
        with tempfile.TemporaryDirectory() as root:
            goal_dir(root, 1)
            goal_dir(root, 2)
            text = render_from_goals("1234", root)
        self.assertNotIn("Definition", text)
        self.assertEqual(text.count("#[export] Hint Resolve residual_1234_"), 2)
        for n in (1, 2):
            self.assertIn(STATEMENT.format(h="%04x" % n, n=n) + PROOF.rstrip() + "\n", text)
        block, header, rows = parse_module(text)
        self.assertEqual((block, len(rows)), ("1234", 2))
        self.assertEqual(header[-1], "Local Open Scope Z_scope.")
        self.assertEqual(residual_module_failures("ZesuSsz/Residuals/Block800d1234.v", text), [])

    def test_refuses_unchecked_proofs(self):
        for proof in ["intros. admit.\nQed.\n", "Admitted.\n", "intros. lia.\nQed.\nQed.\n",
                      "timeout 5 lia.\nQed.\n", "intros. lia.\n"]:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as root:
                goal_dir(root, 1, proof=proof)
                with self.assertRaises(RenderError):
                    render_from_goals("1234", root)

    def test_refuses_a_changed_statement(self):
        with tempfile.TemporaryDirectory() as root:
            d = goal_dir(root, 1)
            (d / "proof.v").write_text((d / "proof.v").read_text().replace("0 <= x +", "0 < x +"))
            with self.assertRaises(RenderError):
                render_from_goals("1234", root)

    def test_refuses_differing_imports(self):
        with tempfile.TemporaryDirectory() as root:
            goal_dir(root, 1)
            goal_dir(root, 2, header=HEADER.replace("ZArith.ZArith", "Lists.List"))
            with self.assertRaises(RenderError):
                render_from_goals("1234", root)

    def test_hygiene_rejects_edited_modules(self):
        with tempfile.TemporaryDirectory() as root:
            goal_dir(root, 1)
            text = render_from_goals("1234", root)
        name = "ZesuSsz/Residuals/Block800d1234.v"
        for edited in [text.replace("Hint Resolve residual_1234_0001", "Hint Resolve other"),
                       text + "\nDefinition extra := 5.\n",
                       text.replace("Require Import ZesuSsz.Automation2.All.",
                                    "Require Import ZesuSsz.Automation.All."),
                       text.replace("lia.\nQed.", "admit.\nQed.")]:
            with self.subTest(edited=edited[-80:]):
                self.assertTrue(residual_module_failures(name, edited))
        self.assertTrue(residual_module_failures("ZesuSsz/Residuals/Block800d9999.v", text))
        self.assertEqual(residual_module_failures("ZesuSsz/Proofs/Other.v", "anything"), [])


BRIDGE = "Lemma decodeItem_bridge_{n} :\n  forall (x : Z), 0 <= x -> 0 <= x + 1.\nProof.\n"
BRIDGE_HEADER = "Require Import ZesuSsz.Automation2.All.\nFrom Coq Require Import ZArith.ZArith.\nLocal Open Scope Z_scope.\n\n"


class SharedModuleTests(unittest.TestCase):
    def bridge_dir(self, root, n, proof=PROOF, name=None):
        d = Path(root) / n
        d.mkdir()
        statement = BRIDGE_HEADER + BRIDGE.format(n=name or n)
        (d / "goal.v").write_text(statement + SLOT)
        (d / "proof.v").write_text(statement + proof)

    def test_bridges_are_copied_without_hints(self):
        with tempfile.TemporaryDirectory() as root:
            self.bridge_dir(root, "fold")
            self.bridge_dir(root, "byte_mask")
            text = render_shared_from_goals("DecodeItemBridges", root)
        self.assertNotIn("Hint", text)
        self.assertIn(BRIDGE.format(n="fold") + PROOF.rstrip() + "\n", text)
        self.assertEqual(len(parse_shared_module(text)[1]), 2)
        name = "ZesuSsz/Residuals/DecodeItemBridges.v"
        self.assertEqual(residual_module_failures(name, text), [])
        for edited in [text + "#[export] Hint Resolve decodeItem_bridge_fold : core.\n",
                       text.replace("lia.\nQed.", "admit.\nQed."),
                       text + "\nDefinition extra := 5.\n"]:
            with self.subTest(edited=edited[-60:]):
                self.assertTrue(residual_module_failures(name, edited))

    def test_refuses_a_lemma_named_apart_from_its_dir(self):
        with tempfile.TemporaryDirectory() as root:
            self.bridge_dir(root, "fold", name="other")
            with self.assertRaises(RenderError):
                render_shared_from_goals("DecodeItemBridges", root)
        with tempfile.TemporaryDirectory() as root:
            self.bridge_dir(root, "fold")
            with self.assertRaises(RenderError):
                render_shared_from_goals("OtherBridges", root)


class ResidualPolicyTests(unittest.TestCase):
    def tree(self, files):
        root = Path(tempfile.mkdtemp())
        for name, text in files.items():
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text(text)
        return root

    MODULE = "Require Import ZesuSsz.Automation2.All.\n#[export] Hint Resolve residual_1234_ab : zesu_residual.\n"
    CALLER = "Require Import ZesuSsz.Automation2.All.\nRequire Import ZesuSsz.Residuals.Block800d{b}.\nLemma DesignedBoundary_800d1234 : True.\n"

    def test_own_caller_may_import(self):
        root = self.tree({"ZesuSsz/Residuals/Block800d1234.v": self.MODULE,
                          "tools/block/generated/fp301_callers/Caller1234.v": self.CALLER.format(b="1234")})
        self.assertEqual(residual_errors(root), [])

    def test_other_importers_and_hints_are_rejected(self):
        root = self.tree({
            "ZesuSsz/Residuals/Block800d1234.v": self.MODULE + "#[export] Hint Resolve foo : core.\n",
            "ZesuSsz/Residuals/Block800d5678.v": self.MODULE.replace("1234", "5678"),
            "ZesuSsz/Proofs/P.v": "Require Import ZesuSsz.Residuals.Block800d1234.\n",
            "tools/block/generated/fp301_callers/Caller1234.v": self.CALLER.format(b="5678"),
            "tools/block/generated/fp301_callers/Caller9999.v": self.CALLER.format(b="9999"),
        })
        errors = "\n".join(residual_errors(root))
        self.assertIn("registers a hint other than", errors)
        self.assertIn("ZesuSsz.Proofs.P imports residual module", errors)
        self.assertIn("another block's residual module", errors)
        self.assertIn("missing residual module", errors)

    def test_block_modules_may_import_the_shared_module(self):
        bridges = "Require Import ZesuSsz.Automation2.All.\nLemma decodeItem_bridge_x : True.\n"
        root = self.tree({
            "ZesuSsz/Residuals/DecodeItemBridges.v": bridges,
            "ZesuSsz/Residuals/Block800d1234.v": "Require Import ZesuSsz.Residuals.DecodeItemBridges.\n" + self.MODULE,
            "tools/block/generated/fp301_callers/Caller1234.v": self.CALLER.format(b="1234")})
        self.assertEqual(residual_errors(root), [])
        (root / "ZesuSsz/Proofs").mkdir(parents=True)
        (root / "ZesuSsz/Proofs/P.v").write_text("Require Import ZesuSsz.Residuals.DecodeItemBridges.\n")
        (root / "ZesuSsz/Residuals/DecodeItemBridges.v").write_text(bridges + "#[export] Hint Resolve x : core.\n")
        errors = "\n".join(residual_errors(root))
        self.assertIn("ZesuSsz.Proofs.P imports residual module", errors)
        self.assertIn("shared bridge module and registers a hint", errors)

    def test_current_tree_passes(self):
        self.assertEqual(residual_errors(ROOT), [])


class CallerImportTests(unittest.TestCase):
    SOURCE = ("Require Import ZesuSsz.Automation2.All.\nRequire Import ZesuSsz.Automation2.All.\n"
              "Local Open Scope Z_scope.\nLemma DesignedBoundary_800d1234 : True.\n")

    def test_import_follows_the_core_when_the_module_exists(self):
        with tempfile.TemporaryDirectory() as root:
            self.assertEqual(residual_import(self.SOURCE, root), self.SOURCE)
            (Path(root) / "Block800d1234.v").write_text("")
            self.assertEqual(residual_import(self.SOURCE, root), self.SOURCE.replace(
                "All.\nLocal", "All.\nRequire Import ZesuSsz.Residuals.Block800d1234.\nLocal"))


if __name__ == "__main__":
    unittest.main()


class MergedHeaderTests(unittest.TestCase):
    def test_added_imports_merge_and_the_own_module_is_dropped(self):
        with tempfile.TemporaryDirectory() as root:
            goal_dir(root, 1)
            extra = HEADER.replace("Local Open Scope Z_scope.\n",
                                   "Require Import ZesuSsz.Compliance.X.\n"
                                   "Require Import ZesuSsz.Residuals.Block800d1234.\n"
                                   "Local Open Scope Z_scope.\n")
            goal_dir(root, 2, header=extra)
            text = render_from_goals("1234", root)
        self.assertIn("Require Import ZesuSsz.Compliance.X.\n", text)
        self.assertNotIn("ZesuSsz.Residuals.Block800d1234", text)
