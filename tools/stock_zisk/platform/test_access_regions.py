"""Check source-bound region rendering without generating traces or proofs."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from access_regions import access_constraint, annotate_regions, region_bounds
from riscv import decode


class AccessRegionTests(unittest.TestCase):
    def fixture(self, root, operation="load", immediate=0, regions=None):
        def binding(name):
            path = root / name
            path.write_text(name)
            return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        imm = immediate & 0xfff
        word = ((imm << 20) | (2 << 15) | (3 << 12) | (5 << 7) | 3)
        if operation == "store":
            word = ((imm >> 5) << 25) | (5 << 20) | (2 << 15) | (3 << 12) | ((imm & 31) << 7) | 0x23
        instruction = decode(4, word.to_bytes(4, "little"))
        names = regions or ["RAM"]
        owner = {"shape": "(KindReg zisk_input_end, ExactShape (RVal_Bits inputEnd))"}
        access = {"pc": "0x4", "instruction": instruction, "operation": operation,
                  "address_width": 64, "comparison_width": 128, "access_bytes": 8,
                  "raw_register": {"event": ["read-reg", "|x2|", "nil", "v5"]},
                  "raw_address": {"event": ["define-const", "v6", ["bvadd", "v5", f"#x{immediate % (1 << 64):016x}"]]},
                  "raw_trace": binding("raw.isla"), "unsplit_region_set": names,
                  "production_region": {"set": list(names), "input_end_owner": owner}}
        packet = {"schema": "source-per-load-placement319.v1", "entry": binding("entry.v"),
                  "regions": {"RAM": {"lower": "2684354560", "upper": "3221225472"},
                              "INPUT_BUFFER": {"lower": "1073741824", "upper": "2147483648"},
                              "RODATA": {"lower": "2148597120", "upper": "2148632184"}},
                  "loads": [access]}
        return packet, access, instruction

    def render(self, packet, access, instruction):
        return access_constraint(packet, access, instruction, region_bounds(packet))

    def test_load_union_keeps_order_and_ignores_case_narrowing(self):
        with tempfile.TemporaryDirectory() as directory:
            p, a, i = self.fixture(Path(directory), regions=["INPUT_BUFFER", "RODATA", "RAM"])
            a["case_specific_region_sets"] = [{"set": ["RAM"]}]
            text, record = self.render(p, a, i)
            self.assertEqual(record["region_union"], ["INPUT_BUFFER", "RODATA", "RAM"])
            self.assertTrue(text.startswith("(or "))
            self.assertEqual(text.count("(and "), 3)
            self.assertLess(text.index("0000000040000000"), text.index("000000008010fd80"))
            self.assertLess(text.index("000000008010fd80"), text.index("00000000a0000000"))
            self.assertIn("(bvsub zisk_input_end #x0000000000000008)", text)
            self.assertNotIn("v6", text)
            self.assertNotIn("actualInputEnd", text)

    def test_stores_require_writable_ram(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p, a, i = self.fixture(root, operation="store")
            self.assertEqual(self.render(p, a, i)[1]["operation"], "store")
            for names in [["INPUT_BUFFER"], ["RODATA"], ["RAM", "INPUT_BUFFER"]]:
                with self.subTest(names=names):
                    p, a, i = self.fixture(root, operation="store", regions=names)
                    with self.assertRaisesRegex(ValueError, "not writable RAM"):
                        self.render(p, a, i)

    def test_offsets_are_decoded_and_end_bound_does_not_wrap(self):
        with tempfile.TemporaryDirectory() as directory:
            for immediate in [-8, 0, 24]:
                with self.subTest(immediate=immediate):
                    p, a, i = self.fixture(Path(directory), immediate=immediate)
                    text, record = self.render(p, a, i)
                    address = f"(bvadd x2 #x{immediate % (1 << 64):016x})"
                    self.assertIn(f"(bvule {address} #x{3221225472 - 8:016x})", text)
                    self.assertNotIn("zero_extend", text)
                    self.assertEqual(record["immediate"], immediate)

    def test_each_load_width_uses_its_full_access_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            for width, funct3 in [(1, 4), (2, 5), (4, 6), (8, 3)]:
                with self.subTest(width=width):
                    p, a, _ = self.fixture(Path(directory))
                    word = (2 << 15) | (funct3 << 12) | (5 << 7) | 3
                    instruction = decode(4, word.to_bytes(4, "little"))
                    a.update(instruction=instruction, access_bytes=width)
                    text, record = self.render(p, a, instruction)
                    self.assertEqual(record["access_bytes"], width)
                    self.assertIn(f"(bvule (bvadd x2 #x0000000000000000) #x{3221225472 - width:016x})", text)

    def test_source_input_end_maps_to_the_owned_register(self):
        with tempfile.TemporaryDirectory() as directory:
            p, a, i = self.fixture(Path(directory), regions=["INPUT_BUFFER"])
            region = a["production_region"]
            region.update(source_parameter_bindings={
                "address": "(bvadd pointer #x0000000000000000)", "inputEnd": "endWord",
                "actualInputEnd_owner": '"zisk_input_end" ↦ᵣ RVal_Bits endWord'},
                symbol_types={"pointer": "BitVec64", "endWord": "BitVec64"},
                original_input_end_reads=[{"event": ["read-reg", "|zisk_input_end|", "nil", "v72"]}])
            text, _ = self.render(p, a, i)
            self.assertIn("(bvsub zisk_input_end #x0000000000000008)", text)
            self.assertNotIn("endWord", text)
            self.assertNotIn("v72", text)
            region["original_input_end_reads"][0]["event"][1] = "|v72|"
            with self.assertRaisesRegex(ValueError, "no source read"):
                self.render(p, a, i)

    def test_wrong_operation_instruction_width_or_offset_refuses(self):
        changes = [("operation", "store"), ("access_bytes", 4), ("comparison_width", 64)]
        with tempfile.TemporaryDirectory() as directory:
            p, a, i = self.fixture(Path(directory))
            for name, value in changes:
                with self.subTest(name=name):
                    changed = deepcopy(a)
                    changed[name] = value
                    with self.assertRaises(ValueError):
                        self.render(p, changed, i)
            changed = deepcopy(a)
            changed["instruction"]["word"] ^= 1
            with self.assertRaisesRegex(ValueError, "checked ELF"):
                self.render(p, changed, i)
            a["raw_address"]["event"][2][2] = "#x0000000000000008"
            with self.assertRaisesRegex(ValueError, "decoded immediate"):
                self.render(p, a, i)

    def test_unknown_register_region_and_source_symbol_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            p, a, i = self.fixture(Path(directory))
            changed = deepcopy(a)
            changed["raw_register"]["event"][1] = "|v6|"
            with self.assertRaisesRegex(ValueError, "ISA register"):
                self.render(p, changed, i)
            changed = deepcopy(a)
            changed["unsplit_region_set"] = changed["production_region"]["set"] = ["UNKNOWN"]
            with self.assertRaisesRegex(ValueError, "no resolved platform bounds"):
                self.render(p, changed, i)
            a["production_region"].update(source_parameter_bindings={"address": "(bvadd unknown #x0000000000000000)"}, symbol_types={})
            with self.assertRaisesRegex(ValueError, "source parameter is unresolved"):
                self.render(p, a, i)

    def test_unowned_input_end_refuses(self):
        with tempfile.TemporaryDirectory() as directory:
            p, a, i = self.fixture(Path(directory), regions=["INPUT_BUFFER"])
            a["production_region"]["input_end_owner"]["shape"] = "(KindReg v6, ExactShape (RVal_Bits actualInputEnd))"
            with self.assertRaisesRegex(ValueError, "exact register owner"):
                self.render(p, a, i)

    def test_packet_identity_source_hash_and_exact_coverage_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p, a, i = self.fixture(root)
            path = root / "packet.json"
            path.write_text(json.dumps(p))
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            rows, records, bindings = annotate_regions([i], path, digest)
            self.assertEqual(len(records), 1)
            self.assertEqual(len(rows[0]["annotations"]), 1)
            self.assertEqual(bindings, [p["entry"], a["raw_trace"]])
            with self.assertRaisesRegex(ValueError, "exact selected memory"):
                annotate_regions([], path, digest)
            with self.assertRaisesRegex(ValueError, "region source changed"):
                annotate_regions([i], path, "0" * 64)
            (root / "raw.isla").write_text("changed trace")
            with self.assertRaisesRegex(ValueError, "region source changed"):
                annotate_regions([i], path, digest)


if __name__ == "__main__":
    unittest.main()
