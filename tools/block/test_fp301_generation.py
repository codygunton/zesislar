"""Reject stale committed FP301 declarations and generated block callers."""
import ast
import hashlib
import json
from pathlib import Path
import unittest

from render_fp301_statements import render_caller, render_declaration

ROOT = Path(__file__).resolve().parents[2]


class GeneratedFP301(unittest.TestCase):
    def test_committed_outputs_match_renderer(self):
        inputs = json.loads((ROOT / "tools/block/fixtures/fp301-generation.json").read_text())
        self.assertEqual(len(inputs["callers"]), 16)
        headers = {}
        for kind, name in [("pilot", "render_fp301_entries.py"),
                           ("return", "render_fp301_statements.py")]:
            tree = ast.parse((ROOT / "tools/block" / name).read_text())
            headers[kind] = next(ast.literal_eval(node.value) for node in ast.walk(tree)
                                 if isinstance(node, ast.Assign) and any(
                                     isinstance(target, ast.Name) and target.id == "header"
                                     for target in node.targets))
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
