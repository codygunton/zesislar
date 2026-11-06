"""Keep literals transparent while preserving reviewed constant identities."""
import unittest

from closed_literal_definitions import closed_literal_definitions, closed_literal_failures


class ClosedLiteralDefinitions(unittest.TestCase):
    def test_numeric_types_and_arithmetic(self):
        for source in ["Definition a : Z := 2 ^ 64.", "Definition a : N := 40%N.",
                       "Definition a : nat := Nat.add 8 8.", "Definition a : positive := xH.",
                       "Definition a : Z := Z.ones 8.", "Definition a : bv 8 := BV 8 255.",
                       "Definition a := 40.", "#[local] Definition a : Z := 40.",
                       "Definition a : Z := (* not a dependency *) 40."]:
            with self.subTest(source=source):
                self.assertEqual([x.name for x in closed_literal_definitions(source)], ["a"])

    def test_numeric_notation_cannot_hide_a_new_literal_definition(self):
        source = ("Notation width := (8 : Z) (only parsing).\n"
                  "Definition bytes : Z := 8 * width.")
        self.assertEqual([x.name for x in closed_literal_definitions(source)], ["bytes"])

    def test_symbolic_and_non_numeric_bodies_are_allowed(self):
        for source in ["Definition a (n : Z) : Z := n + 1.",
                       "Definition a : Z := externalValue + 1.",
                       "Definition a : Prop := True.", "Definition a := [1; 2].",
                       'Definition a := "40".', "(* Definition a : Z := 40. *)",
                       "Notation a := (40 : Z) (only parsing)."]:
            self.assertEqual(closed_literal_definitions(source), [])

    def test_reviewed_exact_exception_and_frozen_core(self):
        source = "Definition a : Z := 40."
        constant = closed_literal_definitions(source)[0]
        exceptions = {("ZesuSsz/Contracts/A.v", "a"):
                      {"sha256": constant.digest, "reason": "Frozen rewrite requires this identity."}}
        self.assertEqual(closed_literal_failures("ZesuSsz/Contracts/A.v", source, exceptions), [])
        self.assertEqual(closed_literal_failures("ZesuSsz/Automation/A.v", source, {}), [])
        self.assertTrue(closed_literal_failures("ZesuSsz/Automation2/A.v", source, {}))
        self.assertTrue(closed_literal_failures("ZesuSsz/Contracts/A.v", source.replace("40", "41"), exceptions))
        self.assertTrue(closed_literal_failures("ZesuSsz/Contracts/B.v", source, exceptions))

    def test_error_names_the_rule_and_instruction(self):
        message = closed_literal_failures("ZesuSsz/Contracts/A.v", "Definition a : Z := 40.", {})[0]
        for expected in ["CONST-NOTATION", "AGENTS.md Constants", "A.v:1", "a must use"]:
            self.assertIn(expected, message)


if __name__ == "__main__":
    unittest.main()
