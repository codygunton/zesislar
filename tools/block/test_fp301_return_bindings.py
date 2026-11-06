"""Check the source bindings for the shared FP301 return declarations."""

import ast
import hashlib
import json
from pathlib import Path
import unittest

from render_fp301_statements import render_declaration
from return_exit import return_blocks


ROOT = Path(__file__).resolve().parents[2]


class FP301ReturnBindings(unittest.TestCase):
    def test_return_exits_and_declarations_match_their_sources(self):
        packet = json.loads(
            (ROOT / "tools/block/fixtures/fp301-return-bindings.json").read_text()
        )
        design = ROOT / packet["design"]["path"]
        self.assertEqual(hashlib.sha256(design.read_bytes()).hexdigest(),
                         packet["design"]["sha256"])
        exits = return_blocks(json.loads(design.read_text()))
        for row in packet["reusable_return_exits"]:
            source = exits[int(row["entry_pc"], 0)]
            self.assertEqual(source["return_clause"]["return_instruction_pc"],
                             row["return_instruction_pc"])
            self.assertEqual(row["address"], "returnAddress")

        canonical = json.loads((ROOT / packet["canonical_fixture"]).read_text())
        headers = {}
        for kind, filename in [("pilot", "render_fp301_entries.py"),
                               ("return", "render_fp301_statements.py")]:
            tree = ast.parse((ROOT / "tools/block" / filename).read_text())
            headers[kind] = next(
                ast.literal_eval(node.value) for node in ast.walk(tree)
                if isinstance(node, ast.Assign) and any(
                    isinstance(target, ast.Name) and target.id == "header"
                    for target in node.targets
                )
            )
        for row in packet["declarations"]:
            with self.subTest(output=row["output"]):
                source = next(item for item in canonical["declarations"]
                              if item["output"] == row["output"])
                self.assertEqual(source["canonical_sha256"], row["canonical_sha256"])
                rendered = render_declaration(source["canonical_source"],
                                              headers[row["header_kind"]])
                self.assertEqual((ROOT / row["output"]).read_text(), rendered)
                self.assertEqual(hashlib.sha256(rendered.encode()).hexdigest(),
                                 row["sha256"])


if __name__ == "__main__":
    unittest.main()
