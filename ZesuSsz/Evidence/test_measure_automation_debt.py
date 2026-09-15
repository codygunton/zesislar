import json
import tempfile
import unittest
from pathlib import Path

from measure_automation_debt import (
    build_log_metrics,
    instr_body_proof_lines,
    measure,
)


class MeasureAutomationDebtTests(unittest.TestCase):
    def test_instr_body_proof_lines(self):
        source = """Lemma sample :
  instr_body 1 True%I.
Proof.
  first.
  second.
Qed.
"""
        self.assertEqual(instr_body_proof_lines(source), [2])

    def test_counts_new_style_debt(self):
        files = {
            "ZesuSsz/Proofs/New.v": """Lemma x : instr_body 1 True%I.
Proof. zesu_block. Unshelve. iApply (instr_pre_wand 1 P Q). Qed.
""",
            "ZesuSsz/Proofs/Old.v": "Proof. Unshelve. Qed.",
        }
        with tempfile.TemporaryDirectory() as directory:
            row = measure(files, Path(directory), 12, 3)
        self.assertEqual(row["new_style_modules"], 1)
        self.assertEqual(row["unshelve_total"], 2)
        self.assertEqual(row["unshelve_new_style"], 1)
        self.assertEqual(row["benchmark_wall_ms"], 12)

    def test_build_log_fraction(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "tx"
            path.mkdir()
            (path / "log.jsonl").write_text(
                json.dumps({"exit": 0}) + "\n" + json.dumps({"exit": 1}) + "\n"
            )
            metrics = build_log_metrics(Path(directory))
        self.assertEqual(metrics["build_log_records"], 2)
        self.assertEqual(metrics["build_log_failures"], 1)
        self.assertEqual(metrics["build_log_failure_fraction"], 0.5)


if __name__ == "__main__":
    unittest.main()
