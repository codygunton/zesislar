import unittest

from check_proof_hygiene import (
    PLACEHOLDER,
    forbidden_counts,
    proof_size_ratchet_failures,
    ratchet_failures,
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


if __name__ == "__main__":
    unittest.main()
