"""Check the source bindings for the shared FP301 return declarations."""

import hashlib
import json
from pathlib import Path
import unittest

from function_profiles import load_profile, pilot_header, return_header
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
        profile = load_profile()
        headers = {"pilot": pilot_header(profile), "return": return_header(profile)}
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
