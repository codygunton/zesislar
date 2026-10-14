"""Check the decodeItem vector layout and its pinned result images."""

import hashlib
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


class DecodeItemVectorsTest(unittest.TestCase):
    def test_pinned_sources(self):
        report = json.loads((ROOT / "ZesuSsz/Evidence/DECODE_ITEM_VECTORS.json").read_text())
        for key, path in [
            ("oracle_sha256", "ZesuSsz/Evidence/DecodeItemVectorOracle.v"),
            ("contract_sha256", "ZesuSsz/Contracts/RlpDecodeItem.v"),
        ]:
            self.assertEqual(report["hashes"][key],
                             hashlib.sha256((ROOT / path).read_bytes()).hexdigest())

    def test_layout_and_images(self):
        report = json.loads((ROOT / "ZesuSsz/Evidence/DECODE_ITEM_VECTORS.json").read_text())
        fixture = report["fixture"]
        source = fixture["input_pointer"]
        output = fixture["output_pointer"]
        stack = fixture["stack_pointer"]
        self.assertLessEqual(0xA0000000, output)
        self.assertLessEqual(output + 40, 0xC0000000)
        self.assertTrue(output + 40 <= stack - 16 or stack <= output)
        vectors = report["vectors"]
        self.assertEqual(len(vectors), 27)
        wraps = []
        for vector in vectors:
            size = len(vector["input_bytes"])
            self.assertLessEqual(0, fixture["input_end"])
            self.assertLess(fixture["input_end"], 2**64)
            self.assertLessEqual(source + size, fixture["input_end"])
            self.assertTrue(0x40000000 <= source <= source + size <= 0x80000000
                            or 0xA0000000 <= source <= source + size <= 0xC0000000)
            image = bytes.fromhex(vector["c1_b"]["expected_40_byte_image_hex"])
            self.assertEqual(len(image), 40)
            candidate = vector["c1_b"]["candidate"]
            if candidate["kind"] == "Success":
                self.assertEqual(int.from_bytes(image[:8], "little"),
                                 candidate["payload_pointer"])
                self.assertEqual(int.from_bytes(image[24:32], "little"),
                                 candidate["consumed_mod_2_64"])
                before = bytes(fixture["before_output_bytes"])
                self.assertEqual(image[17:24], before[17:24])
                self.assertEqual(image[34:40], before[34:40])
            else:
                self.assertEqual(image, bytes(32) + bytes([4]) + bytes(7))
            if "eight_byte_length_wrap" in vector["classes"]:
                wraps.append(vector["name"])
        self.assertEqual(wraps, ["length_2_64_minus_9_wrap",
                                "length_2_64_minus_8_wrap",
                                "list_length_2_64_minus_9_wrap"])


if __name__ == "__main__":
    unittest.main()
