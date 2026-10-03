"""Each native branch retains its context and recorded memory width."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "block"))
import chain_goals


class ChainGoalsTests(unittest.TestCase):
    def setUp(self):
        # This output came from the adjacent fixture compiled with Rocq 8.19.2.
        self.output = (ROOT / "fixtures/chain_goals_native.log").read_text()

    def test_native_branches_keep_distinct_resources(self):
        goals = chain_goals.parse_goals(self.output, phase="active")
        goals = [goal for goal in goals if goal["environment"] == "iris"]
        self.assertEqual(len(goals), 2)
        self.assertNotEqual(goals[0]["spatial"], goals[1]["spatial"])
        self.assertEqual(list(goals[0]["memory_word_widths"].values()), [64])
        self.assertEqual(list(goals[1]["memory_word_widths"].values()), [8])
        self.assertEqual(list(goals[0]["trace_value_widths"].values()), [64])
        self.assertEqual(list(goals[1]["trace_value_widths"].values()), [8])
        for goal in goals:
            self.assertTrue(goal["persistent"])
            self.assertIn("mmio_range", goal["persistent"][0])
            self.assertEqual(list(goal["address_widths"].values()), [64])
            self.assertIn("Hbound", dict(goal["coq"]))
            self.assertEqual(goal["local_sorts"]["Hbound"], "Prop")
            self.assertEqual(goal["local_sorts"]["sp"], "Type")
            self.assertIn("↦ₘ", goal["context"])
            names = [name for name, _ in goal["coq"]]
            self.assertLess(names.index("sp"), names.index("Hbound"))

    def test_shelved_arithmetic_keeps_its_context(self):
        goals = chain_goals.parse_goals(self.output, phase="shelved")
        arithmetic = [goal for goal in goals if goal["environment"] == "coq"]
        self.assertEqual(len(arithmetic), 2)
        for goal in arithmetic:
            self.assertIn("sp", dict(goal["coq"]))
            self.assertIn("Hbound", dict(goal["coq"]))
            self.assertIn("bv_unsigned sp + 1", goal["conclusion"])

    def test_truncated_record_is_rejected(self):
        with self.assertRaises(ValueError):
            chain_goals.parse_goals(self.output[:self.output.index(chain_goals.END)])

    def test_missing_context_is_rejected(self):
        output = ('CHAIN-GOAL-BEGIN "active"\n'
                  'CHAIN-GOAL-CONCLUSION True CHAIN-FIELD-END\nCHAIN-GOAL-END')
        with self.assertRaises(ValueError):
            chain_goals.parse_goals(output)

    def test_missing_sort_is_rejected(self):
        output = self.output.replace(
            'CHAIN-GOAL-SORT sp : Set CHAIN-FIELD-END', '', 1)
        with self.assertRaises(ValueError):
            chain_goals.parse_goals(output)

    def test_invalid_phase_is_rejected(self):
        with self.assertRaises(ValueError):
            chain_goals.parse_goals('CHAIN-GOAL-BEGIN "unknown" CHAIN-GOAL-END')

    def test_native_dependent_locals_keep_dependency_order(self):
        goals = chain_goals.parse_goals(self.output, phase="active")
        dependent = next(goal for goal in goals if "values" in dict(goal["coq"]))
        self.assertEqual([name for name, _ in dependent["coq"]], ["n", "values"])
        self.assertIn("n", dict(dependent["coq"])["values"])

    def test_native_local_alias_is_rejected(self):
        output = (ROOT / "fixtures/chain_goals_alias.log").read_text()
        with self.assertRaisesRegex(ValueError, "unresolved native local definitions"):
            chain_goals.parse_goals(output)


if __name__ == "__main__":
    unittest.main()
