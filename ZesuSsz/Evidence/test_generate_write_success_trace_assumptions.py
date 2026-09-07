import json
import subprocess
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from generate_write_success_trace_assumptions import collect, event_term, write_coq


ROOT = Path(__file__).resolve().parents[2]


class WriteSuccessTraceAssumptionsTest(unittest.TestCase):
    def test_event_term_keeps_only_the_constructor_argument(self):
        self.assertEqual(
            event_term("  Assume (AExp_Val x a) a :t: tnil", "Assume"),
            "(AExp_Val x a) a",
        )
        self.assertIsNone(event_term("  ReadReg x :t: tnil", "Assume"))

    def test_uses_the_pinned_index_and_region(self):
        inventory = collect(
            ROOT / "generated/isla-traces/write_success_blocks/Index.v",
            ROOT / "generated/isla-traces",
        )
        self.assertEqual(inventory["trace_count"], 950)
        self.assertEqual(len(inventory["assumes"]), 822)
        self.assertEqual(len(inventory["assume_regs"]), 12)
        self.assertEqual(inventory["assume_occurrence_count"], 2095)
        self.assertEqual(inventory["assume_reg_occurrence_count"], 3846)
        x9_lower = [item for item in inventory["assumes"]
                    if 'AVal_Var "x9"' in item["term"]
                    and "Bvuge" in item["term"]]
        self.assertTrue(x9_lower)

    def test_cli_writes_stable_json(self):
        with TemporaryDirectory() as temporary:
            output = Path(temporary) / "inventory.json"
            subprocess.run([
                sys.executable,
                str(ROOT / "ZesuSsz/Evidence/generate_write_success_trace_assumptions.py"),
                "--index",
                str(ROOT / "generated/isla-traces/write_success_blocks/Index.v"),
                "--trace-root",
                str(ROOT / "generated/isla-traces"),
                "--output",
                str(output),
            ], check=True)
            inventory = json.loads(output.read_text())
            self.assertEqual(inventory["trace_count"], 950)

    def test_writes_chunked_coq_predicate(self):
        inventory = collect(
            ROOT / "generated/isla-traces/write_success_blocks/Index.v",
            ROOT / "generated/isla-traces",
        )
        with TemporaryDirectory() as temporary:
            paths = write_coq(inventory, Path(temporary), chunk_size=100)
            self.assertEqual(len(paths), 10)
            source = paths[-1].read_text()
            self.assertIn(
                "Definition writeSuccessTraceAssumptions (state : IslaState) : Prop :=",
                source,
            )
            self.assertIn("writeSuccessTraceAssumptionsChunk08", source)


if __name__ == "__main__":
    unittest.main()
