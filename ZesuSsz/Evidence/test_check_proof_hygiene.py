import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch

from check_proof_hygiene import (
    PLACEHOLDER,
    retired_module_failures,
    forbidden_counts,
    proof_size_warnings,
    proof_size_ratchet_failures,
    ratchet_failures,
    generated_hand_line_failures,
)


class ProofHygieneTests(unittest.TestCase):
    def test_retired_hand_modules_cannot_return(self):
        for name in ("From6a38", "From6ad8"):
            path = f"ZesuSsz/Proofs/DecodeItem/Join6ae0/{name}.v"
            self.assertTrue(retired_module_failures(path, ""))

    def test_retired_full_and_relative_imports_fail(self):
        for name in ("From6a38", "From6ad8"):
            for source in (
                f"Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.{name}.",
                f"From ZesuSsz.Proofs.DecodeItem.Join6ae0 Require Export {name}.",
            ):
                self.assertTrue(retired_module_failures("New.v", source))

    def test_retirement_preserves_contract_and_generated_modules(self):
        source = ("Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.\n"
                  "Require Import ZesuSsz.Proofs.DecodeItem.Auto.Join6ae0From6a38.\n"
                  "Check decodeItemJoin6ae0From6a38.\n")
        self.assertEqual(retired_module_failures("New.v", source), [])

    def test_retired_module_comment_is_historical(self):
        self.assertEqual(retired_module_failures(
            "New.v", "(* ZesuSsz.Proofs.DecodeItem.Join6ae0.From6ad8 *)"), [])

    def test_rejects_proof_placeholders(self):
        for source in (
            "Admitted.",
            "admit.",
            "Axiom bad : False.",
            "Abort.",
            "Parameter external_value : nat.",
            "Hypothesis unproved : False.",
            "Variable unspecified : nat.",
        ):
            with self.subTest(source=source):
                self.assertIsNotNone(PLACEHOLDER.search(source))

    def test_accepts_related_words(self):
        self.assertIsNone(PLACEHOLDER.search("Definition abort_reason := 0."))

    def test_forbidden_name_ratchet(self):
        name = "ZesuSsz/Proofs/Test.v"
        counts = forbidden_counts("solve_zesu_ld_array_at solve_zesu_ld_array_at")
        baseline = {name: {"solve_zesu_ld_array_at": 2}}
        self.assertEqual(ratchet_failures(name, counts, baseline), [])
        counts["solve_zesu_ld_array_at"] = 3
        self.assertEqual(len(ratchet_failures(name, counts, baseline)), 1)

    def test_new_forbidden_name_fails(self):
        counts = forbidden_counts("zesu_ld_byte_array_at_spec")
        self.assertEqual(len(ratchet_failures("new.v", counts, {})), 1)

    def test_proof_size_ratchet(self):
        messages = ["instr_body proof has 50 lines: Test.v:1"]
        baseline = {"Test.v": {
            "long_proofs": 1,
            "max_proof_lines": 50,
            "rename_proofs": 0,
            "max_renames": 0,
        }}
        self.assertEqual(
            proof_size_ratchet_failures("Test.v", messages, baseline), []
        )
        messages = ["instr_body proof has 51 lines: Test.v:1"]
        self.assertEqual(
            len(proof_size_ratchet_failures("Test.v", messages, baseline)), 1
        )

    def test_one_line_proof_does_not_extend_into_next_proof(self):
        lines = [
            "Lemma first : instr_body 0x1 spec.",
            "Proof. move => *. zesu_block. Qed.",
            "Lemma second : instr_body 0x2 spec.",
            "Proof.",
            *["  iFrame."] * 42,
            "Qed.",
        ]
        self.assertEqual(
            proof_size_warnings("Test.v", lines),
            ["instr_body proof has 42 lines: Test.v:4"],
        )

    def test_new_long_hand_proof_fails_after_one_line_proof(self):
        lines = [
            "Lemma first : instr_body 0x1 spec.",
            "Proof. move => *. zesu_block. Qed.",
            "Lemma new_hand : instr_body 0x2 spec.",
            "Proof.",
            *["  iFrame."] * 41,
            "Qed.",
        ]
        warnings = proof_size_warnings("New.v", lines)
        self.assertEqual(
            warnings, ["instr_body proof has 41 lines: New.v:4"]
        )
        self.assertTrue(proof_size_ratchet_failures("New.v", warnings, {}))

    def test_generated_instruction_body_rejects_hand_lines(self):
        name = "ZesuSsz/Generated/WriteSuccess/Blocks/Block_1.v"
        for body in ("Proof. iIntros. zesu_block. Qed.",
                     "Proof.\n  iIntros.\n  zesu_block.\nQed.",
                     "Proof using All. iIntros. zesu_block. Qed.",
                     "Proof using Type*.\n  iIntros.\n  zesu_block.\nQed."):
            with self.subTest(body=body), tempfile.TemporaryDirectory() as root:
                path = Path(root) / name
                path.parent.mkdir(parents=True)
                text = "Lemma block_1 : instr_body 0x1 spec.\n" + body + "\n"
                path.write_text(text)
                with patch("check_proof_hygiene.ROOT", Path(root)):
                    failures = generated_hand_line_failures(name, text)
                self.assertEqual(len(failures), 1)
                self.assertIn("block_1: 1 lines", failures[0])

    def test_generated_instruction_body_accepts_block_automation(self):
        name = "ZesuSsz/Generated/WriteSuccess/Blocks/Block_1.v"
        text = ("Lemma block_1 : instr_body 0x1 spec.\n"
                "Proof. zesu_block. Qed.\n"
                "Lemma pure_fact : True.\nProof. exact I. Qed.\n")
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / name
            path.parent.mkdir(parents=True)
            path.write_text(text)
            with patch("check_proof_hygiene.ROOT", Path(root)):
                self.assertEqual(generated_hand_line_failures(name, text), [])

    def test_handwritten_instruction_body_needs_no_residual_record(self):
        self.assertEqual(generated_hand_line_failures(
            "ZesuSsz/Proofs/Test.v",
            "Lemma block_1 : instr_body 0x1 spec.\nProof. iIntros. Qed.\n"), [])

    def test_proof_using_keeps_the_40_line_limit(self):
        lines = ["Lemma block_1 : instr_body 0x1 spec.",
                 "Proof using All.", *["  iFrame."] * 41, "Qed."]
        self.assertEqual(proof_size_warnings("Test.v", lines),
                         ["instr_body proof has 41 lines: Test.v:2"])


if __name__ == "__main__":
    unittest.main()
