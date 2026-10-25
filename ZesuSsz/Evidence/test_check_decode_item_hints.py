import json
from pathlib import Path
import tempfile
import unittest

from check_decode_item_hints import (
    ROOT, SCOPED_HINT_IMPORTS, exported_modules, imported_modules,
    has_hint_registration, missing_hint_modules,
    manifest_errors, manifest_umbrellas,
)


class DecodeItemHintCoverageTests(unittest.TestCase):
    def test_current_inventory_is_exported(self):
        self.assertEqual(manifest_errors(ROOT)[0], [])

    def test_new_hint_module_requires_an_export(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "DecodeItemHints.v").write_text("")
            (directory / "NewFact.v").write_text(
                "#[export] Hint Extern 1 (SimplAnd P True) => exact I : typeclass_instances.\n"
            )
            self.assertEqual(missing_hint_modules(directory), ["ZesuSsz.Compliance.NewFact"])
            (directory / "DecodeItemHints.v").write_text(
                "Require Export ZesuSsz.Compliance.NewFact.\n"
            )
            self.assertEqual(missing_hint_modules(directory), [])

    def test_import_does_not_replace_export(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "Fact.v").write_text("Global Instance fact : SimplAnd P True := proof.\n")
            (directory / "DecodeItemHints.v").write_text("Require Import ZesuSsz.Compliance.Fact.\n")
            self.assertEqual(missing_hint_modules(directory), ["ZesuSsz.Compliance.Fact"])

    def test_nested_module_requires_its_full_name(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "Nested").mkdir()
            (directory / "Nested" / "Fact.v").write_text("Instance fact : SimplAnd P True := proof.\n")
            (directory / "DecodeItemHints.v").write_text("Require Export ZesuSsz.Compliance.Fact.\n")
            self.assertEqual(missing_hint_modules(directory), ["ZesuSsz.Compliance.Nested.Fact"])

    def test_comments_strings_and_local_commands_are_not_exports(self):
        self.assertFalse(has_hint_registration(
            '(* Hint Extern (* nested Instance *) *) Definition text := "Hint Extern".\n'
            'Local Instance local_fact : True := I. #[local] Hint Resolve local_fact.\n'
        ))
        self.assertEqual(exported_modules(
            '(* Require Export ZesuSsz.Compliance.Fact. *)\n'
            'Definition text := "Require Export ZesuSsz.Compliance.Fact.".\n'
        ), set())

    def test_multiline_and_from_exports(self):
        self.assertTrue(has_hint_registration("#[export]\nInstance fact :\nSimplAnd P True := proof.\n"))
        self.assertTrue(has_hint_registration("Global Hint Resolve fact : typeclass_instances.\n"))
        self.assertTrue(has_hint_registration("#[export] Existing Instances fact other.\n"))
        self.assertEqual(exported_modules(
            "From ZesuSsz.Compliance Require Export\nFact Other.\n"
        ), {"ZesuSsz.Compliance.Fact", "ZesuSsz.Compliance.Other"})

    def test_direct_import_parser_rejects_exports_comments_and_strings(self):
        self.assertEqual(imported_modules(
            '(* Require Import ZesuSsz.Compliance.Comment. *)\n'
            'Definition text := "Require Import ZesuSsz.Compliance.String.".\n'
            'Require Export ZesuSsz.Compliance.Exported.\n'
            'From ZesuSsz.Compliance Require Import\nFact Other.\n'
        ), {"ZesuSsz.Compliance.Fact", "ZesuSsz.Compliance.Other"})


class FunctionHintCoverageTests(unittest.TestCase):
    def fixture(self, root):
        evidence = root / "ZesuSsz/Evidence"
        compliance = root / "ZesuSsz/Compliance"
        evidence.mkdir(parents=True)
        compliance.mkdir(parents=True)
        for prefix in ("DecodeItem", "Free"):
            registrations = [f"ZesuSsz/Compliance/{prefix}{name}.v"
                             for name in ("Hints", "DataRegistrations")]
            (evidence / f"{prefix}_function_text.json").write_text(json.dumps({
                "function": prefix, "registrations": registrations}))
            (compliance / f"{prefix}Hints.v").write_text(
                f"Require Export ZesuSsz.Compliance.{prefix}DataRegistrations.\n"
                f"Global Instance {prefix}_unfold : True := I.\n")
            (compliance / f"{prefix}DataRegistrations.v").write_text(
                f"Global Instance {prefix}_fact : True := I.\n")
        return evidence, compliance

    def scoped_fixture(self, root):
        _, compliance = self.fixture(root)
        for module, importers in SCOPED_HINT_IMPORTS.items():
            (compliance / (module.rsplit(".", 1)[1] + ".v")).write_text(
                "Global Instance scoped_fact : True := I.\n")
            for importer in importers:
                path = root / (importer.replace(".", "/") + ".v")
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("a") as stream:
                    stream.write(f"Require Import {module}.\n")
        return compliance

    def test_inventory_only_skips_only_missing_umbrella(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            evidence, compliance = self.fixture(root)
            manifest = evidence / 'Parent_function_text.json'
            data = dict(function='parent', inventory_only=True,
                        registrations=['ZesuSsz/Compliance/ParentFacts.v'])
            (compliance / 'ParentFacts.v').write_text('Global Instance parent_fact : True := I.\n')
            manifest.write_text(json.dumps(data))
            self.assertEqual(manifest_errors(root)[0], [])
            data['introductions'] = 'invalid'
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'Invalid introductions'):
                manifest_umbrellas(root)
            data['introductions'] = ['ZesuSsz/Compliance/Missing.v']
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'missing'):
                manifest_umbrellas(root)
            data['introductions'] = []
            data['inventory_only'] = 'true'
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'inventory_only'):
                manifest_umbrellas(root)

    def test_inventory_only_does_not_skip_existing_umbrella_coverage(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            evidence, compliance = self.fixture(root)
            manifest = evidence / 'Free_function_text.json'
            data = json.loads(manifest.read_text())
            data['inventory_only'] = True
            manifest.write_text(json.dumps(data))
            (compliance / 'FreeHints.v').write_text('(* Missing exports. *)\n')
            errors, _ = manifest_errors(root)
            self.assertIn('Free_function_text.json: FreeHints.v does not export ZesuSsz.Compliance.FreeDataRegistrations.', errors)

    def test_c1b_meaning_requires_the_scoped_error_image_registration(self):
        module = "ZesuSsz.Compliance.DecodeItemExitDataFacts"
        importer = "Scaffolding.DecodeItemC1BMeaning"
        self.assertIn(importer, SCOPED_HINT_IMPORTS[module])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.scoped_fixture(root)
            path = root / (importer.replace(".", "/") + ".v")
            self.assertEqual(manifest_errors(root)[0], [])
            path.write_text("Require Import ZesuSsz.Compliance.DecodeItemHints.\n")
            self.assertEqual(manifest_errors(root)[0], [
                f"{importer} does not directly import {module}."])

    def test_scoped_hints_use_all_declared_direct_importers(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.scoped_fixture(root)
            self.assertEqual(manifest_errors(root), ([], 5))

    def test_each_scoped_import_is_required(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.scoped_fixture(root)
            for module, importers in SCOPED_HINT_IMPORTS.items():
                for importer in importers:
                    with self.subTest(module=module, importer=importer):
                        path = root / (importer.replace(".", "/") + ".v")
                        original = path.read_text()
                        path.write_text(original.replace(f"Require Import {module}.\n", ""))
                        self.assertEqual(manifest_errors(root)[0], [
                            f"{importer} does not directly import {module}."])
                        path.write_text(original)

    def test_scoped_importer_must_exist(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.scoped_fixture(root)
            importer = SCOPED_HINT_IMPORTS["ZesuSsz.Compliance.DecodeItemExitDataFacts"][0]
            (root / (importer.replace(".", "/") + ".v")).unlink()
            self.assertEqual(manifest_errors(root)[0], [
                f"Scoped hint importer is missing: {importer}."])

    def test_transitive_import_does_not_cover_a_scoped_hint(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            compliance = self.scoped_fixture(root)
            module = "ZesuSsz.Compliance.DecodeItemExitDataFacts"
            importer = SCOPED_HINT_IMPORTS[module][0]
            (compliance / "Bridge.v").write_text(f"Require Export {module}.\n")
            path = root / (importer.replace(".", "/") + ".v")
            path.write_text("Require Import ZesuSsz.Compliance.Bridge.\n")
            self.assertEqual(manifest_errors(root)[0], [
                f"{importer} does not directly import {module}."])

    def test_scoped_policy_keeps_ordinary_export_checks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            compliance = self.scoped_fixture(root)
            (compliance / "FreeHints.v").write_text("")
            self.assertEqual(manifest_errors(root)[0], [
                "Free_function_text.json: FreeHints.v does not export "
                "ZesuSsz.Compliance.FreeDataRegistrations.",
                "No function hint umbrella exports ZesuSsz.Compliance.FreeDataRegistrations."])

    def test_separate_umbrellas_cover_their_own_function(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root)
            self.assertEqual(manifest_errors(root), ([], 2))

    def test_another_umbrella_cannot_hide_a_missing_function_export(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _, compliance = self.fixture(root)
            (compliance / "FreeHints.v").write_text("")
            with (compliance / "DecodeItemHints.v").open("a") as stream:
                stream.write("Require Export ZesuSsz.Compliance.FreeDataRegistrations.\n")
            errors, _ = manifest_errors(root)
            self.assertEqual(len(errors), 1)
            self.assertIn("FreeHints.v does not export ZesuSsz.Compliance.FreeDataRegistrations", errors[0])

    def test_unlisted_new_hint_module_cannot_escape_every_umbrella(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _, compliance = self.fixture(root)
            (compliance / "Unclaimed.v").write_text("Global Hint Resolve fact.\n")
            errors, _ = manifest_errors(root)
            self.assertEqual(errors, ["No function hint umbrella exports ZesuSsz.Compliance.Unclaimed."])

    def test_missing_listed_registration_is_an_error(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _, compliance = self.fixture(root)
            (compliance / "FreeDataRegistrations.v").unlink()
            with self.assertRaisesRegex(ValueError, "listed Compliance source is missing"):
                manifest_umbrellas(root)

    def test_the_manifest_must_declare_exactly_one_umbrella(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            evidence, _ = self.fixture(root)
            manifest = evidence / "Free_function_text.json"
            data = json.loads(manifest.read_text())
            data["registrations"] = []
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "one hint umbrella"):
                manifest_umbrellas(root)


if __name__ == "__main__":
    unittest.main()
