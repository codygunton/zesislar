"""Test source identity and unavailable-count handling in the status generator."""

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import generate_decode_item_native_status as status


class NativeStatusTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        source = self.root / "ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v"
        source.parent.mkdir(parents=True)
        sites = ["6960", "697c", "698c", "69b0", "69e8", "6a08", "6a24",
                 "6a38", "6a40", "6a78", "6aa8", "6ac4", "6ad8", "6ae0", "6b08"]
        source.write_text("Record DecodeItemOpenNativeHypotheses : Prop := {\n" +
                          ";\n".join("native800d" + site + " : closure" + site for site in sites) +
                          "\n}.\nDefinition decodeItemI67NativeResidualCounts := [" +
                          ";".join("(0x800d" + site + ", None)" for site in sites) + "].\n")
        production = self.root / "ZesuSsz/Proofs/DecodeItem/Auto/Block800d6974.v"
        production.parent.mkdir(parents=True)
        production.write_text("production identity\n")
        measured = self.root / "Measured.v"
        measured.write_text("measured identity\n")
        self.table = self.root / "build/stock-zisk/table.json"
        self.table.parent.mkdir(parents=True)
        self.data = {"root": status.MEASUREMENT_ROOT, "approved_switches": 28,
                     "hint_modules": 25, "rows": [
                         {"block": "0x800d" + site, "goal_count": None,
                          "source": str(measured), "source_sha256": status.binding(measured)["sha256"],
                          "outcome": "limit-stop", "statement_sha256": "statement", "captures": []}
                         for site in sites]}

    def generate(self):
        self.table.write_text(json.dumps(self.data))
        sha = hashlib.sha256(self.table.read_bytes()).hexdigest()
        with patch.object(status, "ROOT", self.root), patch.object(status, "I67_SHA256", sha):
            return status.generate(self.table)

    def test_unavailable_counts_remain_null(self):
        result = self.generate()
        self.assertEqual(result["open_closures"], 15)
        self.assertTrue(all(row["printed_active_count"] is None for row in result["rows"]))
        self.assertTrue(all(row["closure"] == "open" for row in result["rows"]))

    def test_changed_measurement_is_rejected(self):
        self.data["rows"][0]["goal_count"] = 1
        with self.assertRaisesRegex(ValueError, "checked active count differs"):
            self.generate()

    def test_changed_source_is_rejected(self):
        self.data["rows"][0]["source_sha256"] = "wrong"
        with self.assertRaisesRegex(ValueError, "measured source hash differs"):
            self.generate()


if __name__ == "__main__":
    unittest.main()
