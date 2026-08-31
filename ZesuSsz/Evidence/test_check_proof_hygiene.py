import unittest

from check_proof_hygiene import PLACEHOLDER


class ProofHygieneTests(unittest.TestCase):
    def test_rejects_proof_placeholders(self):
        for source in ("Admitted.", "admit.", "Axiom bad : False.", "Abort."):
            with self.subTest(source=source):
                self.assertIsNotNone(PLACEHOLDER.search(source))

    def test_accepts_related_words(self):
        self.assertIsNone(PLACEHOLDER.search("Definition abort_reason := 0."))


if __name__ == "__main__":
    unittest.main()
