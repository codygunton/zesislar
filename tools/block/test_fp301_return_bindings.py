"""Check the design-table return exits that share the FP301 function-return package."""

import hashlib
import json
from pathlib import Path
import unittest

from return_exit import return_blocks


ROOT = Path(__file__).resolve().parents[2]


class FP301ReturnBindings(unittest.TestCase):
    def test_return_exits_match_the_design_table(self):
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


if __name__ == "__main__":
    unittest.main()
