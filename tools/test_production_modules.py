"""Check production emission without executing a proof or reading an object."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
import production_modules


class ProductionModuleTests(unittest.TestCase):
    def fixture(self, kind="native"):
        if kind == "native":
            lemma = "DesignedBoundary_1000"
            local = (
                "Definition DesignedEntry_1000 (args : Args) : iProp Sigma :=\n"
                "  (Entry args ∗ True)%I.\n"
                "Global Instance : LithiumUnfold (@DesignedEntry_1000) := I.\n"
                "Global Typeclasses Opaque DesignedEntry_1000.\n\n"
            )
            declaration = (
                "Lemma DesignedBoundary_1000 (args : Args) :\n"
                "  instr_pre 0x1004 (∃ witness, Next args witness)%I -∗\n"
                "  Code -∗ instr_body 0x1000 (DesignedEntry_1000 args)."
            )
        else:
            lemma, local = "decodeItemJoinFixture_automatic", ""
            declaration = "Lemma decodeItemJoinFixture_automatic (args : Args) :\n  ⊢ Transfer args."
        source = (
            "Require Import ZesuSsz.Automation.All.\n"
            "Require Import ZesuSsz.Automation.Switches.RamFault.\n"
            "Require Import Contracts.Entry.\n"
            "Require Import Contracts.Entry.\n"
            "From Coq Require Import List ZArith.\n"
            "Open Scope Z_scope.\n"
            "Ltac chain_print_goal phase := idtac phase.\n\n" + local +
            declaration + "\nProof.\n  try zesu_block.\nQed.\n\n"
            "Print Assumptions " + lemma + ".\n"
        )
        return dict(source=source, lemma=lemma, entry_pc="0x1000",
                    statement_sha256=hashlib.sha256(declaration.encode()).hexdigest())

    def test_native_declaration_and_entry_wrapper_remain_exact(self):
        fixture = self.fixture()
        source = production_modules.render(fixture, "native")
        self.assertEqual(production_modules.statement(source, fixture["lemma"]),
                         production_modules.statement(fixture["source"], fixture["lemma"]))
        self.assertIn("(∃ witness, Next args witness)", source)
        self.assertIn("(Entry args ∗ True)%I", source)
        self.assertIn("Global Typeclasses Opaque DesignedEntry_1000.", source)
        self.assertIn("\nProof.\n  zesu_block.\nQed.\n", source)
        self.assertNotIn("try zesu_block", source)
        self.assertNotIn("Ltac chain_print_goal", source)

    def test_approved_imports_replace_switches_and_preserve_defining_imports(self):
        source = production_modules.render(self.fixture(), "native")
        self.assertEqual(source.splitlines()[:3],
                         ["Require Import " + name + "."
                          for name in production_modules.REQUIRED_IMPORTS])
        self.assertNotIn("Automation.Switches.", source)
        self.assertEqual(source.count("Require Import Contracts.Entry."), 1)
        self.assertIn("From Coq Require Import List ZArith.", source)
        self.assertIn("Open Scope Z_scope.", source)

    def test_transfer_module_keeps_its_exact_obligation(self):
        fixture = self.fixture("adapter")
        source = production_modules.render(fixture, "adapter")
        self.assertIn("⊢ Transfer args.", source)
        self.assertEqual(production_modules.module_name(fixture, "adapter"),
                         "ZesuSsz.Proofs.DecodeItem.Auto.JoinFixture")
        self.assertNotIn("block_table_pre", source)

    def test_changed_statement_and_manual_body_are_rejected(self):
        fixture = self.fixture()
        fixture["source"] = fixture["source"].replace("Code -∗", "True -∗")
        with self.assertRaisesRegex(ValueError, "statement changed"):
            production_modules.render(fixture, "native")
        fixture = self.fixture()
        fixture["source"] = fixture["source"].replace("try zesu_block.", "iIntros. zesu_block.")
        with self.assertRaisesRegex(ValueError, "unsupported proof step"):
            production_modules.render(fixture, "native")

    def test_frozen_library_imports_are_rejected(self):
        for command in ("Require Import Boundary.",
                        "From Frozen Require Import Boundary.", "Import Boundary."):
            fixture = self.fixture()
            fixture["source"] = command + "\n" + fixture["source"]
            with self.assertRaisesRegex(ValueError, "frozen Boundary"):
                production_modules.render(fixture, "native")

    def test_object_target_has_the_vo_suffix(self):
        module = production_modules.module_name(self.fixture(), "native")
        self.assertEqual(production_modules.object_path(module),
                         Path("ZesuSsz/Proofs/DecodeItem/Auto/Block1000.vo"))

    def test_different_existing_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            emitted = production_modules.emit(self.fixture(), "native", directory)
            path = Path(directory) / emitted["source"]
            path.write_text("keep this source")
            with self.assertRaisesRegex(ValueError, "different source"):
                production_modules.emit(self.fixture(), "native", directory)
            self.assertEqual(path.read_text(), "keep this source")

    def jobs(self, root):
        rows, jobs = [], []
        for kind, outcome in [("native", "native-closure"), ("adapter", "adapter-closure")]:
            fixture = self.fixture(kind)
            path = root / (kind + ".v")
            path.write_text(fixture["source"])
            jobs.append({**fixture, "id": kind, "kind": kind, "source": str(path),
                         "source_sha256": production_modules.digest(path)})
            rows.append(dict(id=kind, kind=kind, outcome=outcome, exit_code=0,
                             limit=None, assumptions_verified=True, inherited_debts={},
                             statement_sha256=fixture["statement_sha256"]))
        return {"rows": rows}, jobs

    def test_pass_emits_both_closure_kinds_and_omits_residuals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report, jobs = self.jobs(root)
            report["rows"].append(dict(id="residual", outcome="residual"))
            rows = production_modules.emit_pass(report, jobs, root)
            self.assertEqual({row["kind"] for row in rows}, {"native", "adapter"})
            self.assertEqual(len(list((root / production_modules.DIRECTORY).glob("*.v"))), 2)

    def test_late_invalid_closure_does_not_emit_earlier_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report, jobs = self.jobs(root)
            report["rows"][1]["inherited_debts"] = {"shelf": ["pending"]}
            with self.assertRaisesRegex(ValueError, "debt-free evidence"):
                production_modules.emit_pass(report, jobs, root)
            self.assertFalse((root / production_modules.DIRECTORY).exists())

    def test_source_hash_and_duplicate_closures_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report, jobs = self.jobs(root)
            Path(jobs[0]["source"]).write_text("changed")
            with self.assertRaisesRegex(ValueError, "source hash differs"):
                production_modules.emit_pass(report, jobs, root)
            report, jobs = self.jobs(root)
            report["rows"].append(deepcopy(report["rows"][0]))
            with self.assertRaisesRegex(ValueError, "repeats an obligation"):
                production_modules.emit_pass(report, jobs, root)

    def test_escaped_target_does_not_emit_earlier_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            workspace, outside = root / "workspace", root / "outside"
            workspace.mkdir()
            outside.mkdir()
            report, jobs = self.jobs(root)
            targets = workspace / production_modules.DIRECTORY
            targets.mkdir(parents=True)
            (targets / "JoinFixture.v").symlink_to(outside / "JoinFixture.v")
            with self.assertRaisesRegex(ValueError, "leaves its workspace"):
                production_modules.emit_pass(report, jobs, workspace)
            self.assertFalse((targets / "Block1000.v").exists())
            self.assertFalse((outside / "JoinFixture.v").exists())


if __name__ == "__main__":
    unittest.main()
