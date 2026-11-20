import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / "block"))
from return_exit import add_return_facts, return_blocks


class ReturnExitTests(unittest.TestCase):
    def test_exit_kind_comes_from_the_design(self):
        row = {"entry_pc": "0x10", "successor_pcs": [],
               "return_clause": {"return_instruction_pc": "0x14"}}
        self.assertEqual(return_blocks({"blocks": [row]}), {16: row})
        with self.assertRaisesRegex(ValueError, "declared exit kind"):
            return_blocks({"blocks": [{"entry_pc": "0x10", "successor_pcs": []}]})
        row["successor_pcs"] = ["0x20"]
        with self.assertRaisesRegex(ValueError, "inconsistent"):
            return_blocks({"blocks": [row]})

    def test_return_facts_follow_every_resource(self):
        body = "((∃ x, (owner args x ∗ ⌜x = 1⌝ ∗ True)) ∗ K)%I"
        self.assertEqual(add_return_facts(body, ["P args x"]),
                         "((∃ x, (owner args x ∗ ⌜x = 1⌝ ∗ ⌜P args x⌝ ∗ True)) ∗ K)%I")
        self.assertEqual(add_return_facts("(owner ∗ K)%I", []), "(owner ∗ K)%I")
        with self.assertRaisesRegex(ValueError, "pure fact tail"):
            add_return_facts("(owner ∗ K)%I", ["P"])


if __name__ == "__main__":
    unittest.main()
