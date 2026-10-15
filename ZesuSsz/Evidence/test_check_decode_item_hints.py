import json
from pathlib import Path
import tempfile
import unittest

from check_decode_item_hints import (
    ROOT, exported_modules, has_hint_registration, missing_hint_modules,
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
