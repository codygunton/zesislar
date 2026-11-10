"""Reject stale committed FP301 declarations and generated block callers."""
import hashlib
import json
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header, return_header
from render_fp301_statements import render_caller, render_declaration

ROOT = Path(__file__).resolve().parents[2]


class GeneratedFP301(unittest.TestCase):
    def test_committed_outputs_match_renderer(self):
        inputs = json.loads((ROOT / "tools/block/fixtures/fp301-generation.json").read_text())
        self.assertEqual(len(inputs["callers"]), 16)
        profile = load_profile()
        headers = {"pilot": pilot_header(profile), "return": return_header(profile)}
        for group in ["callers", "declarations"]:
            for row in inputs[group]:
                with self.subTest(output=row["output"]):
                    source = row["canonical_source"]
                    self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),
                                     row["canonical_sha256"])
                    expected = (render_caller(source) if group == "callers" else
                                render_declaration(source, headers[row["header_kind"]]))
                    self.assertEqual((ROOT / row["output"]).read_text(), expected)


if __name__ == "__main__":
    unittest.main()
