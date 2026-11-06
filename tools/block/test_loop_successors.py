"""Check the frozen loop-derived declarations and their source bindings."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]


class LoopSuccessors(unittest.TestCase):
    def test_committed_declarations(self):
        fixture = json.loads((ROOT / "tools/block/fixtures/fp301-loop-successors.json").read_text())
        self.assertEqual(len(fixture["declarations"]), 8)
        for row in fixture["declarations"]:
            with self.subTest(output=row["output"]):
                source = row["canonical_source"]
                self.assertEqual(hashlib.sha256(source.encode()).hexdigest(), row["sha256"])
                self.assertEqual((ROOT / row["output"]).read_text(), source)
                self.assertIsNone(re.search(r"\b(?:Proof|Qed|Admitted|Axiom|Ltac)\b", source))
                if row["output"].endswith("Entries.v"):
                    self.assertEqual(source.count(" ∗ K)"), 1)

    def test_source_bindings(self):
        fixture = json.loads((ROOT / "tools/block/fixtures/fp301-loop-successors.json").read_text())
        self.assertEqual(len(fixture["reaching_passes"]), 8)
        self.assertEqual(len(fixture["loop_proofs"]), 2)
        for row in fixture["reaching_passes"]:
            for key in ["report", "seed"]:
                self.assertRegex(row[key]["sha256"], r"^[0-9a-f]{64}$")


if __name__ == "__main__":
    unittest.main()
