import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from tools.block import check_data_only_lemmas, check_generic_automation


class GenericAutomationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.automation = self.root / "ZesuSsz/Automation"
        self.automation.mkdir(parents=True)

    def write(self, name, text):
        path = self.automation / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_generic_modules_pass(self):
        self.write("Hooks.v", "Ltac generic_step := idtac.\n")
        self.assertEqual(check_generic_automation.violations(self.root), [])

    def test_each_forbidden_form_fails(self):
        for value in ("0x800d697c", "2148362620", "decodeItem", "DecodeItem",
                      "parentHeader", "nextUint64", "alt_fl_alloc", "memcpy"):
            with self.subTest(value=value):
                self.write("Hooks.v", value)
                errors = check_generic_automation.violations(self.root)
                self.assertEqual(len(errors), 1)
                self.assertIn(value, errors[0])

    def test_nested_modules_and_comments_are_scanned(self):
        self.write("Switches/Private.v", "(* decodeItem *)\n(* 0x800d697c *)\n")
        errors = check_generic_automation.violations(self.root)
        self.assertEqual(len(errors), 2)
        self.assertIn("Switches/Private.v:2:4", errors[1])

    def test_embedded_function_names_are_rejected(self):
        self.write("Hooks.v", "RlpDecodeItemContract decodeItemDerivedFacts")
        self.assertEqual(len(check_generic_automation.violations(self.root)), 2)

    def test_all_occurrences_are_reported(self):
        self.write("Hooks.v", "decodeItem decodeItem\nmemcpy")
        self.assertEqual(len(check_generic_automation.violations(self.root)), 3)

    def test_only_automation_rocq_sources_are_scanned(self):
        self.write("notes.txt", "decodeItem")
        outside = self.root / "ZesuSsz/Compliance"
        outside.mkdir()
        (outside / "Facts.v").write_text("decodeItem")
        self.assertEqual(check_generic_automation.violations(self.root), [])

    def test_address_patterns_keep_the_requested_range(self):
        self.write("Hooks.v", "0x700d697c 0x8001234 2147000000 214800000")
        self.assertEqual(check_generic_automation.violations(self.root), [])


class DataOnlyLemmaTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.evidence = self.root / "ZesuSsz/Evidence"
        self.evidence.mkdir(parents=True)
        self.manifest = {category: [] for category in check_data_only_lemmas.CATEGORIES}
        self.manifest["function"] = "example"

    def write_manifest(self, name="example"):
        (self.evidence / f"{name}_function_text.json").write_text(json.dumps(self.manifest))

    def add_file(self, category, text):
        relative = f"ZesuSsz/Evidence/{category}.v"
        (self.root / relative).write_text(text)
        self.manifest[category] = [relative]

    def test_data_facts_pass(self):
        self.add_file("introductions", "Lemma length_fact : length [] = 0. Proof. reflexivity. Qed.")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_every_semantic_category_rejects_each_machine_reference(self):
        for category in check_data_only_lemmas.DATA_CATEGORIES:
            for value in ("instr_body", "instr_pre", "WPasm", "liAStep", "zesu_block", "zesu_liAStep"):
                with self.subTest(category=category, value=value):
                    self.add_file(category, value)
                    self.write_manifest()
                    self.assertTrue(any(value in error for error in
                                        check_data_only_lemmas.violations(self.root)))

    def test_comments_are_scanned(self):
        self.add_file("exit_meanings", "(* WPasm must not appear here. *)")
        self.write_manifest()
        self.assertIn("WPasm", check_data_only_lemmas.violations(self.root)[0])

    def test_contract_and_registration_categories_can_describe_machine_code(self):
        for category in ("contracts", "registrations", "generator_json"):
            self.add_file(category, "instr_body WPasm zesu_block")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_missing_listed_files_fail_in_every_category(self):
        for category in check_data_only_lemmas.CATEGORIES:
            with self.subTest(category=category):
                self.manifest[category] = ["ZesuSsz/Evidence/Missing.v"]
                self.write_manifest()
                self.assertIn("listed file is missing", check_data_only_lemmas.violations(self.root)[0])
                self.manifest[category] = []

    def test_missing_or_invalid_file_lists_fail(self):
        for value in (None, "Facts.v", [1], [""]):
            with self.subTest(value=value):
                self.manifest["introductions"] = value
                self.write_manifest()
                self.assertIn("file list", check_data_only_lemmas.violations(self.root)[0])

    def test_missing_or_empty_function_name_fails(self):
        for value in (None, "", " "):
            with self.subTest(value=value):
                self.manifest["function"] = value
                self.write_manifest()
                self.assertIn("function name", check_data_only_lemmas.violations(self.root)[0])

    def test_invalid_json_fails(self):
        (self.evidence / "example_function_text.json").write_text("{")
        self.assertTrue(check_data_only_lemmas.violations(self.root))

    def test_paths_outside_the_repository_fail(self):
        for value in ("../Outside.v", "/tmp/Outside.v"):
            with self.subTest(value=value):
                self.manifest["introductions"] = [value]
                self.write_manifest()
                self.assertIn("leaves the repository", check_data_only_lemmas.violations(self.root)[0])

    def test_all_manifests_are_checked(self):
        self.add_file("loop_steps", "instr_pre")
        self.write_manifest("first")
        self.write_manifest("second")
        self.assertEqual(len(check_data_only_lemmas.violations(self.root)), 2)

    def test_unlisted_files_are_outside_the_manifest_check(self):
        (self.evidence / "Unlisted.v").write_text("WPasm")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])


class BlockTableMetadataTests(unittest.TestCase):
    def test_metadata_matches_current_sources_and_existential_convention(self):
        root = Path(__file__).resolve().parents[2]
        metadata = json.loads((root / "ZesuSsz/Generated/DecodeItem/block_table_metadata.json").read_text())
        self.assertIn("existential_binders", metadata["table_convention"])
        self.assertNotIn("universal_binders", metadata["table_convention"])
        for category in ("source_hashes", "generated_hashes"):
            for relative, expected in metadata[category].items():
                with self.subTest(path=relative):
                    self.assertEqual(hashlib.sha256((root / relative).read_bytes()).hexdigest(), expected)


if __name__ == "__main__":
    unittest.main()
