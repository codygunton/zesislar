import unittest

from check_proof_hygiene import (
    PLACEHOLDER,
    forbidden_counts,
    proof_size_warnings,
    proof_size_ratchet_failures,
    ratchet_failures,
    record_ratchet_failures,
)


class ProofHygieneTests(unittest.TestCase):
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

    def test_residual_record_ratchet(self):
        entries = [("new_block", "instr_body 0x1 spec", 3)]
        self.assertEqual(
            len(record_ratchet_failures("new.v", entries, set(), [])), 1)
        self.assertEqual(
            record_ratchet_failures("new.v", entries, {"new_block"}, []), [])
        self.assertEqual(
            record_ratchet_failures(
                "new.v", entries, set(), ["new.v:new_block"]), [])

    def test_residual_record_ratchet_ignores_clean_proofs(self):
        entries = [("clean_block", "instr_body 0x1 spec", 0),
                   ("not_a_block", "some other statement", 9)]
        self.assertEqual(
            record_ratchet_failures("new.v", entries, set(), []), [])


if __name__ == "__main__":
    unittest.main()
