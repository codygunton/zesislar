"""Check the pinned parent-header vector set and its Rocq oracle binding."""

import hashlib
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "ZesuSsz/Evidence/PARENT_HEADER_VECTORS.json"
ORACLE_PATH = ROOT / "ZesuSsz/Evidence/ParentHeaderDifferential.v"
ELF_PATH = ROOT / "build/stock-zisk/zesu-zisk.elf"
BOUNDARIES = [
    33, 66, 87, 120, 153, 186, 445, 446, 447, 451,
    454, 459, 460, 493, 502, 503, 536, 537, 538, 571,
]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def wrap(payload):
    size = len(payload)
    if size <= 55:
        return bytes([192 + size]) + payload
    if size <= 255:
        return bytes([248, size]) + payload
    return bytes([249, size // 256, size % 256]) + payload


class ParentHeaderVectorsTest(unittest.TestCase):
    def test_pinned_vectors(self):
        report = json.loads(VECTOR_PATH.read_text())
        self.assertEqual(report["hashes"]["oracle_sha256"], digest(ORACLE_PATH.read_bytes()))
        self.assertEqual(report["hashes"]["selected_elf_sha256"], digest(ELF_PATH.read_bytes()))
        self.assertEqual(report["source_fixture"]["revision"],
                         "c67e485ff8b5be9abc8ad15345ec21aa22e290d9")
        self.assertEqual(report["source_fixture"]["sha256"],
                         "d4e5acbc323640e68dae68162243f7946c32276bb17bc6710d6266590d50e69f")

        self.assertEqual(report["fixture"]["input_pointer"], 4096)
        vectors = report["vectors"]
        self.assertEqual(len(vectors), 24)
        raw = [bytes(vector["input_bytes"]) for vector in vectors]
        self.assertEqual(report["hashes"]["vector_inputs_sha256"], digest(b"".join(raw)))
        for vector, data in zip(vectors, raw):
            self.assertEqual(vector["input_hex"], data.hex())
            self.assertTrue(vector["outer_c1_a"]["in_domain"])
            self.assertLess(4096 + len(data), 2**64)

        self.assertEqual([vector["name"] for vector in vectors[:2]],
                         ["cancun_real_header", "prague_real_header"])
        self.assertEqual([vector["sail_outcome"]["kind"] for vector in vectors[:2]],
                         ["Success", "Success"])
        self.assertTrue(all(vector["all_contiguous_headers_fit"]["in_domain"]
                            for vector in vectors[:22]))

        payload = raw[0][3:]
        for field, (vector, data, size) in enumerate(
                zip(vectors[2:22], raw[2:22], BOUNDARIES), start=1):
            self.assertEqual(vector["name"], f"cancun_after_field_{field:02d}")
            self.assertEqual(data, wrap(payload[:size]))
            self.assertEqual(vector["sail_outcome"]["kind"], "Success")
            self.assertIn("selected_elf_static_analysis", vector)

        for vector, data, start, finish in zip(
                vectors[22:], raw[22:], [447, 536], [451, 537]):
            self.assertEqual(data, wrap(payload[:start] + bytes([191] + [255] * 8)
                                        + payload[finish:]))
            self.assertEqual(vector["sail_outcome"]["kind"], "Reject")
            self.assertFalse(vector["all_contiguous_headers_fit"]["in_domain"])


if __name__ == "__main__":
    unittest.main()
