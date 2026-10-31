import unittest

from render_support import definition_introduction_source


class DefinitionIntroduction(unittest.TestCase):
    def source(self, body):
        return ("Definition sample `{!islaG Sigma} `{!threadG}\n"
                "  (value : Z) (K : iProp Sigma) : iProp Sigma :=\n"
                + body + ".\n")

    def test_body_and_existential_scope_are_exact(self):
        body = "((∃ (word : bv 64), ⌜word = Z_to_bv 64 value⌝ ∗ ⌜0 < value⌝ ∗ True) ∗ K)%I"
        rendered = definition_introduction_source(self.source(body), "sample")
        self.assertIn(body + " := bi.entails_refl _.", rendered)
        self.assertIn("(sample (value) (K))", rendered)
        self.assertNotIn("Proof.", rendered)

    def test_new_clause_replaces_the_cached_body(self):
        old = definition_introduction_source(self.source("(True ∗ K)%I"), "sample")
        new = definition_introduction_source(self.source("(⌜0 < value⌝ ∗ True ∗ K)%I"), "sample")
        self.assertNotIn("⌜0 < value⌝", old)
        self.assertIn("⌜0 < value⌝", new)

    def test_extra_command_refuses(self):
        with self.assertRaises(ValueError):
            definition_introduction_source(self.source("True%I") + "Axiom bad : False.\n", "sample")

    def test_tactic_body_refuses(self):
        with self.assertRaises(ValueError):
            definition_introduction_source(self.source("ltac:(exact I)"), "sample")

    def test_wrong_definition_refuses(self):
        with self.assertRaises(ValueError):
            definition_introduction_source(self.source("True%I"), "other")


if __name__ == "__main__":
    unittest.main()
