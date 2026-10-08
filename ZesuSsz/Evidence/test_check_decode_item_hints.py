from pathlib import Path
import tempfile
import unittest

from check_decode_item_hints import (
    ROOT, exported_modules, has_hint_registration, missing_hint_modules,
)


class DecodeItemHintCoverageTests(unittest.TestCase):
    def test_current_inventory_is_exported(self):
        self.assertEqual(missing_hint_modules(ROOT / "ZesuSsz" / "Compliance"), [])

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


if __name__ == "__main__":
    unittest.main()
