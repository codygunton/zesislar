"""Check immutable precommit captures and the compiled regression statements."""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent

class PrecommitmentWitnessFixtures(unittest.TestCase):
    def test_capture_and_statement_bindings(self):
        index = json.loads((ROOT / "precommitment/INDEX.json").read_text())
        self.assertEqual([row["block"] for row in index["captures"]],
                         ["6a08", "6a38", "6aa8", "6ad8"])
        source = (ROOT / index["module"]).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), index["module_sha256"])
        text = source.decode()
        self.assertTrue(text.startswith("Require Import ZesuSsz.Automation.All."))
        for name, expected in index["theorem_sha256"].items():
            body = "Lemma " + text.split("Lemma " + name, 1)[1].split("Qed.", 1)[0] + "Qed."
            self.assertEqual(hashlib.sha256(body.encode()).hexdigest(), expected)
        for row in index["captures"]:
            data = (ROOT / row["capture"]).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), row["capture_sha256"])
            self.assertEqual(len(data), row["capture_export"]["bytes"])
            groups = json.loads(data)
            self.assertEqual(set(groups), {"goals", "stack", "shelf", "given_up"})
            self.assertEqual(len(groups["goals"]), row["capture_export"]["active_goals"])
            self.assertEqual(len(groups["shelf"]), row["capture_export"]["shelved_goals"])
            self.assertGreater(len(groups["goals"]), 0)
            self.assertIn(row["witness_theorem"], index["theorem_sha256"])
            self.assertLessEqual(row["selected_goal_one_based"], len(groups["goals"]))
        self.assertEqual(set(index["conflict_certificates"]), {"697c", "69e8"})
        self.assertEqual(index["pending_precommit_states"], ["6960", "697c", "69e8"])
        self.assertIn("no closure acceptance test", index["repair_ON"])

if __name__ == "__main__":
    unittest.main()
