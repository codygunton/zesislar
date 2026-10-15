"""Check function-specific names without changing supplied proof declarations."""
from pathlib import Path
from copy import deepcopy
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent / "block"))
from function_names import FunctionNames, prefix_argument
import complete_promotion
import generate_table
import production_modules
import promote_table
from tools import test_block_table, test_complete_promotion, test_production_modules, test_promote_table


class FunctionNameTests(unittest.TestCase):
    def test_inventory_names_resolve_to_the_final_component(self):
        self.assertEqual(prefix_argument("rlp.decodeItem"), "decodeItem")
        self.assertEqual(prefix_argument("alt_fl_alloc.free"), "free")
        self.assertEqual(FunctionNames("nextUint64").filename, "next_uint64")

    def test_invalid_identifiers_cannot_enter_generated_paths_or_terms(self):
        for name in ("", "0name", "../free", "free; Check nat.", "a/b", None):
            with self.subTest(name=name), self.assertRaises(ValueError):
                FunctionNames(name)

    def test_default_renderer_prefix_is_byte_identical(self):
        self.assertEqual(complete_promotion.render_prefix(), complete_promotion.PREFIX)
        design, report = test_block_table.BlockTableTests().executable_fixture()
        self.assertEqual(generate_table.render_table(design, report),
                         generate_table.render_table(design, report, name_prefix="decodeItem"))

    def test_only_the_exact_producer_sha_comment_is_excluded(self):
        producer = "(* Source: tools/block/generate_table.py; SHA-256: " + "a" * 64 + ". *)\n"
        source = producer + "Definition value := 1.\n(* A retained comment. *)\n"
        changed = source.replace("a" * 64, "b" * 64)
        self.assertTrue(generate_table.rocq_outputs_equal(source, changed))
        for other in [changed.replace("1.", "2."),
                      changed.replace(" := ", "  := "),
                      changed.replace("retained", "changed"),
                      changed.replace("\n", "\r\n"),
                      changed.replace(producer.replace("a" * 64, "b" * 64), "")]:
            with self.subTest(other=other):
                self.assertFalse(generate_table.rocq_outputs_equal(source, other))

    def test_other_source_hashes_and_edge_alternatives_remain_exact(self):
        source = ("(* Source: Contracts/Entry.v; SHA-256: " + "a" * 64 + ". *)\n"
                  "Definition literal := Entries.literal.\n"
                  "Definition shortString := Entries.shortString.\n")
        for old, new in [("a" * 64, "b" * 64), ("Entries.literal", "Entries.shortString"),
                         ("Entries.shortString", "Entries.literal")]:
            with self.subTest(old=old):
                self.assertFalse(generate_table.rocq_outputs_equal(source, source.replace(old, new)))

    def test_duplicate_or_malformed_producer_comments_are_not_ignored(self):
        line = "(* Source: tools/block/generate_table.py; SHA-256: " + "a" * 64 + ". *)\n"
        with self.assertRaisesRegex(ValueError, "duplicate producer-SHA"):
            generate_table.rocq_outputs_equal(line, line + line)
        for changed in [line.replace("a" * 64, "invalid"),
                        line.replace("Source:", "Producer:"),
                        line.replace("tools/block/", "other/"), " " + line]:
            with self.subTest(changed=changed):
                self.assertFalse(generate_table.rocq_outputs_equal(line, changed))

    def test_producer_text_inside_strings_or_nested_comments_is_retained(self):
        line = "(* Source: tools/block/generate_table.py; SHA-256: " + "a" * 64 + ". *)\n"
        for source in ['Definition text := "\n' + line + '".\n',
                       '(* Outer comment.\n' + line + '*)\n']:
            with self.subTest(source=source):
                self.assertFalse(generate_table.rocq_outputs_equal(
                    source, source.replace("a" * 64, "b" * 64)))

    def test_other_function_table_keeps_resource_bindings(self):
        design, report = test_block_table.BlockTableTests().executable_fixture()
        source = generate_table.render_table(design, report, name_prefix="free")
        self.assertIn("Section free_block_table.", source)
        self.assertIn("Definition freeState1000 :", source)
        self.assertIn("Definition freeBlockTable :", source)
        self.assertIn("ZesuSsz.Contracts.Fixture.entry1000 (args) (frameBytes)", source)
        self.assertNotIn("decodeItem", source)

    def test_other_function_promotion_checks_its_own_table_signature(self):
        _, design, _ = test_promote_table.PromotionTests().fixture()
        native, adapter = test_promote_table.PromotionTests().evidence()
        adapter["statement"] = promote_table.table_statement(0x1000, name_prefix="free")
        self.assertEqual(promote_table.validate_promotion(
            design["blocks"][0], native, adapter, design_sha256="bound", name_prefix="free"),
            "Proofs.ExactBody")
        with self.assertRaisesRegex(ValueError, "table-body signature"):
            promote_table.validate_promotion(
                design["blocks"][0], native, adapter, design_sha256="bound")

    def test_other_function_slots_preserve_supplied_qualified_proof(self):
        report = {"proof_slots": [{"pc": "0x1000", "status": "proved",
                  "proof_module": "Proofs.decodeItemKeep", "proof_lemma": "Proofs.decodeItemKeep.body"}]}
        source = promote_table.render_slots(report, name_prefix="free")
        self.assertIn("Require Import ZesuSsz.Compliance.FreeHints.", source)
        self.assertIn("Definition freePromotedBody1000 :", source)
        self.assertIn("Proofs.decodeItemKeep.body.", source)

    def test_other_function_module_keeps_the_exact_declaration(self):
        fixture = test_production_modules.ProductionModuleTests().fixture()
        with tempfile.TemporaryDirectory() as directory:
            emitted = production_modules.emit(fixture, "native", directory, name_prefix="free")
            self.assertEqual(emitted["module"], "ZesuSsz.Proofs.Free.Auto.Block1000")
            source = (Path(directory) / emitted["source"]).read_text()
            self.assertEqual(production_modules.statement(source, fixture["lemma"]),
                             production_modules.statement(fixture["source"], fixture["lemma"]))
            self.assertIn("Require Import ZesuSsz.Compliance.FreeHints.", source)

    def test_other_function_adapter_uses_its_names_without_rewriting_theorem(self):
        source = complete_promotion.render_adapter(
            0x1000, "Proofs.decodeItemKeep", "decodeItemKeep", ["args"], name_prefix="free")
        self.assertIn("Require Import ZesuSsz.Proofs.Free.TableSlots.Adapter1000Conditional.", source)
        self.assertIn("Lemma freeSlotBody1000", source)
        self.assertIn("instr_body 0x1000 freeState1000.", source)
        self.assertIn("exact (decodeItemKeep args).", source)

    def test_other_function_complete_does_not_consume_the_historical_i67_table(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in test_complete_promotion.INPUTS:
                old = test_complete_promotion.HISTORICAL_NAMES.get(name, name)
                text = test_complete_promotion.historical("cp-p1-i60", old)
                text = text.replace("DecodeItem", "Free").replace("decodeItem", "free")
                path = root / name.replace("DecodeItem", "Free")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            module = test_complete_promotion.MODULE.replace("DecodeItem", "Free")
            lemma = test_complete_promotion.LEMMA.replace("DecodeItem", "Free")
            with patch.object(test_complete_promotion.native_status, "generate",
                              side_effect=AssertionError("The historical refresh must not run.")), \
                 patch.object(complete_promotion.subprocess, "check_output", return_value="fixture-root\n"), \
                 patch("promotion_verification.verify_generated", return_value={"success": True}):
                report = complete_promotion.complete(
                    root, 0x800d6974, module, lemma, root / "report.json", None,
                    name_prefix="free")
            self.assertTrue(report["success"])
            self.assertIsNone(report["native_status"])
            self.assertTrue((root / "ZesuSsz/Evidence/FreeOpenNativeHypotheses.v").is_file())
            self.assertFalse((root / "ZesuSsz/Evidence/DecodeItemOpenNativeHypotheses.v").exists())

    def test_table_check_compares_bytes_without_rewriting_stale_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design, report = test_block_table.BlockTableTests().executable_fixture()
            design_path, output, coverage = (root / name for name in ("design.json", "Table.v", "table.json"))
            design_path.write_text(json.dumps(design))
            command = ["generate_table.py", "--function", "free", "--design", str(design_path),
                       "--output", str(output), "--coverage", str(coverage)]
            with patch.object(sys, "argv", command), \
                 patch.object(generate_table, "bound_inputs", side_effect=lambda *args: deepcopy(report)):
                generate_table.main()
            expected = output.read_bytes()
            with patch.object(sys, "argv", [*command, "--check"]), \
                 patch.object(generate_table, "bound_inputs", side_effect=lambda *args: deepcopy(report)):
                generate_table.main()
                output.write_text("preserve stale source")
                with self.assertRaisesRegex(ValueError, "Rocq table is stale"):
                    generate_table.main()
            self.assertEqual(output.read_text(), "preserve stale source")
            self.assertIn(b"Definition freeBlockTable", expected)


if __name__ == "__main__":
    unittest.main()
