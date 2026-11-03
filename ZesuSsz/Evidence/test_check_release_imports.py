import unittest

from check_release_imports import import_errors, imports


class ReleaseImportTests(unittest.TestCase):
    def test_final_all_restores_the_rules(self):
        self.assertEqual(import_errors(
            "Require Import ZesuSsz.Automation.All.\n"
            "Require Import isla.riscv64.riscv64.\n"
            "Require Import ZesuSsz.Automation.All.\n"), [])

    def test_later_isa_or_stdpp_import_fails(self):
        for command in ("Require Import isla.riscv64.riscv64.",
                        "From stdpp Require Import list."):
            with self.subTest(command=command):
                self.assertTrue(import_errors(
                    "Require Import ZesuSsz.Automation.All.\n" + command))

    def test_comments_and_strings_do_not_restore_rules(self):
        self.assertTrue(import_errors(
            "Require Import isla.riscv64.riscv64.\n"
            "(* outer (* Require Import ZesuSsz.Automation.All. *) *)\n"
            'Definition text := "Require Import ZesuSsz.Automation.All.".\n'))

    def test_multiline_from_import(self):
        self.assertEqual(import_errors(
            "From ZesuSsz.Automation Require Import\n All.\n"), [])

    def test_plain_import_after_all_fails(self):
        self.assertTrue(import_errors(
            "Require Import ZesuSsz.Automation.All.\nImport Other.\n"))

    def test_plain_require_after_all_fails(self):
        self.assertTrue(import_errors(
            "Require Import ZesuSsz.Automation.All.\nRequire Other.\n"))

    def test_mixed_last_command_fails(self):
        self.assertTrue(import_errors(
            "Require Import ZesuSsz.Automation.All isla.riscv64.riscv64.\n"))

    def test_explicit_release_umbrella(self):
        self.assertEqual(import_errors("Require Import Release.Rules.\n",
                                       ("Release.Rules",)), [])

    def test_missing_import_fails(self):
        self.assertTrue(import_errors("Lemma control : True. Proof. exact I. Qed."))

    def test_command_offsets_preserve_source_positions(self):
        source = "(* heading *)\nRequire Import isla.riscv64.riscv64.\n"
        commands = list(imports(source))
        self.assertEqual(commands[0][2], ["isla.riscv64.riscv64"])
        self.assertEqual(source[commands[0][1] - 1], ".")


if __name__ == "__main__":
    unittest.main()
