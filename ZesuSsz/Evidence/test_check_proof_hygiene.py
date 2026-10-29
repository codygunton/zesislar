import unittest
import tempfile
import subprocess
from pathlib import Path
from unittest.mock import patch

from check_proof_hygiene import (
    PLACEHOLDER,
    executable_form_failures,
    executable_text,
    main,
    normalized_declaration,
    trusted_declaration_failures,
    trusted_declarations,
    retired_module_failures,
    forbidden_counts,
    proof_size_warnings,
    proof_size_ratchet_failures,
    ratchet_failures,
    generated_hand_line_failures,
)


class ProofHygieneTests(unittest.TestCase):
    def test_scanner_rejects_each_planted_executable_form(self):
        cases = (
            ("timeout 1 done.", "timeout identifier"),
            ("timeoutf 1 done.", "timeout identifier"),
            ("Timeout 10 Check nat.", "Timeout command"),
            ("Set Default Timeout 10.", "default timeout"),
            ("Unset Guard Checking.", "disabled checking"),
            ("Unset Positivity Checking.", "disabled checking"),
            ("Unset Universe Checking.", "disabled checking"),
            ("bypass_check.", "bypass_check identifier"),
        )
        for command, label in cases:
            with self.subTest(command=command), tempfile.TemporaryDirectory() as root:
                name = "ZesuSsz/Automation/Planted.v"
                path = Path(root) / name
                path.parent.mkdir(parents=True)
                path.write_text("(* The planted command is on line 2. *)\n" + command + "\n")
                with patch("check_proof_hygiene.ROOT", Path(root)), \
                        patch("check_proof_hygiene.tracked_files", return_value=[name]):
                    with self.assertRaises(SystemExit) as raised:
                        main()
                self.assertEqual(str(raised.exception), f"forbidden {label}: {name}:2")

    def test_scanner_rejects_plants_across_its_existing_scope(self):
        for name in ("ZesuSsz/Proofs/Planted.v", "ZesuSsz/Generated/Planted.v",
                     "tools/Planted.v"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as root:
                path = Path(root) / name
                path.parent.mkdir(parents=True)
                path.write_text("Require Import ZesuSsz.Automation.All.\nbypass_check.\n")
                with patch("check_proof_hygiene.ROOT", Path(root)), \
                        patch("check_proof_hygiene.tracked_files", return_value=[name]):
                    with self.assertRaises(SystemExit) as raised:
                        main()
                self.assertEqual(str(raised.exception),
                                 f"forbidden bypass_check identifier: {name}:2")

    def test_comments_and_strings_do_not_trigger_executable_bans(self):
        source = ('(* timeout 1 (* timeoutf 2 *) Timeout 3 Check nat.\n'
                  'Set Default Timeout 4. Unset Guard Checking. bypass_check. *)\n'
                  'Definition message := "timeout timeoutf Timeout 1 Set Default Timeout '
                  'Unset Guard Checking bypass_check ""timeout""".\n')
        self.assertEqual(executable_form_failures("Test.v", source), [])
        self.assertEqual(executable_text(source).count("\n"), source.count("\n"))

    def test_identifier_boundaries_and_enabled_checks_remain_valid(self):
        source = ("Ltac my_timeout := idtac.\n"
                  "Ltac timeout_helper := idtac.\n"
                  "Ltac timeout' := idtac.\n"
                  "Ltac bypass_check_helper := idtac.\n"
                  "Set Guard Checking.\n")
        self.assertEqual(executable_form_failures("Test.v", source), [])

    def test_scanner_accepts_a_file_with_only_noncode_matches(self):
        with tempfile.TemporaryDirectory() as root:
            name = "ZesuSsz/Automation/Planted.v"
            path = Path(root) / name
            path.parent.mkdir(parents=True)
            path.write_text('(* timeout timeoutf Timeout 1 Set Default Timeout 1.\n'
                            'Unset Guard Checking. bypass_check. *)\n'
                            'Definition message := "timeout bypass_check".\n')
            with patch("check_proof_hygiene.ROOT", Path(root)), \
                    patch("check_proof_hygiene.tracked_files", return_value=[name]):
                main()

    def test_comments_can_separate_command_tokens(self):
        for source, label in (("Timeout (* note *) 3 Check nat.", "Timeout command"),
                              ("Set (* note *) Default\nTimeout 3.", "default timeout"),
                              ("Unset (* note *) Guard\nChecking.", "disabled checking")):
            with self.subTest(source=source):
                self.assertEqual(executable_form_failures("Test.v", source),
                                 [f"forbidden {label}: Test.v:1"])

    def test_retired_hand_modules_cannot_return(self):
        for name in ("From6a38", "From6ad8"):
            path = f"ZesuSsz/Proofs/DecodeItem/Join6ae0/{name}.v"
            self.assertTrue(retired_module_failures(path, ""))

    def test_retired_full_and_relative_imports_fail(self):
        for name in ("From6a38", "From6ad8"):
            for source in (
                f"Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.{name}.",
                f"From ZesuSsz.Proofs.DecodeItem.Join6ae0 Require Export {name}.",
            ):
                self.assertTrue(retired_module_failures("New.v", source))

    def test_retirement_preserves_contract_and_generated_modules(self):
        source = ("Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.\n"
                  "Require Import ZesuSsz.Proofs.DecodeItem.Auto.Join6ae0From6a38.\n"
                  "Check decodeItemJoin6ae0From6a38.\n")
        self.assertEqual(retired_module_failures("New.v", source), [])

    def test_retired_module_comment_is_historical(self):
        self.assertEqual(retired_module_failures(
            "New.v", "(* ZesuSsz.Proofs.DecodeItem.Join6ae0.From6ad8 *)"), [])

    def test_rejects_proof_placeholders(self):
        for source in (
            "Admitted.",
            "admit.",
            "Axiom bad : False.",
            "Abort.",
            "Parameter external_value : nat.",
            "Hypothesis unproved : False.",
            "Variable unspecified : nat.",
        ):
            with self.subTest(source=source):
                self.assertIsNotNone(PLACEHOLDER.search(source))

    def test_accepts_related_words(self):
        self.assertIsNone(PLACEHOLDER.search("Definition abort_reason := 0."))

    def test_forbidden_name_ratchet(self):
        name = "ZesuSsz/Proofs/Test.v"
        counts = forbidden_counts("solve_zesu_ld_array_at solve_zesu_ld_array_at")
        baseline = {name: {"solve_zesu_ld_array_at": 2}}
        self.assertEqual(ratchet_failures(name, counts, baseline), [])
        counts["solve_zesu_ld_array_at"] = 3
        self.assertEqual(len(ratchet_failures(name, counts, baseline)), 1)

    def test_new_forbidden_name_fails(self):
        counts = forbidden_counts("zesu_ld_byte_array_at_spec")
        self.assertEqual(len(ratchet_failures("new.v", counts, {})), 1)

    def test_proof_size_ratchet(self):
        messages = ["instr_body proof has 50 lines: Test.v:1"]
        baseline = {"Test.v": {
            "long_proofs": 1,
            "max_proof_lines": 50,
            "rename_proofs": 0,
            "max_renames": 0,
        }}
        self.assertEqual(
            proof_size_ratchet_failures("Test.v", messages, baseline), []
        )
        messages = ["instr_body proof has 51 lines: Test.v:1"]
        self.assertEqual(
            len(proof_size_ratchet_failures("Test.v", messages, baseline)), 1
        )

    def test_one_line_proof_does_not_extend_into_next_proof(self):
        lines = [
            "Lemma first : instr_body 0x1 spec.",
            "Proof. move => *. zesu_block. Qed.",
            "Lemma second : instr_body 0x2 spec.",
            "Proof.",
            *["  iFrame."] * 42,
            "Qed.",
        ]
        self.assertEqual(
            proof_size_warnings("Test.v", lines),
            ["instr_body proof has 42 lines: Test.v:4"],
        )

    def test_new_long_hand_proof_fails_after_one_line_proof(self):
        lines = [
            "Lemma first : instr_body 0x1 spec.",
            "Proof. move => *. zesu_block. Qed.",
            "Lemma new_hand : instr_body 0x2 spec.",
            "Proof.",
            *["  iFrame."] * 41,
            "Qed.",
        ]
        warnings = proof_size_warnings("New.v", lines)
        self.assertEqual(
            warnings, ["instr_body proof has 41 lines: New.v:4"]
        )
        self.assertTrue(proof_size_ratchet_failures("New.v", warnings, {}))

    def test_generated_instruction_body_rejects_hand_lines(self):
        name = "ZesuSsz/Generated/WriteSuccess/Blocks/Block_1.v"
        for body in ("Proof. iIntros. zesu_block. Qed.",
                     "Proof.\n  iIntros.\n  zesu_block.\nQed.",
                     "Proof using All. iIntros. zesu_block. Qed.",
                     "Proof using Type*.\n  iIntros.\n  zesu_block.\nQed."):
            with self.subTest(body=body), tempfile.TemporaryDirectory() as root:
                path = Path(root) / name
                path.parent.mkdir(parents=True)
                text = "Lemma block_1 : instr_body 0x1 spec.\n" + body + "\n"
                path.write_text(text)
                with patch("check_proof_hygiene.ROOT", Path(root)):
                    failures = generated_hand_line_failures(name, text)
                self.assertEqual(len(failures), 1)
                self.assertIn("block_1: 1 lines", failures[0])

    def test_generated_instruction_body_accepts_block_automation(self):
        name = "ZesuSsz/Generated/WriteSuccess/Blocks/Block_1.v"
        text = ("Lemma block_1 : instr_body 0x1 spec.\n"
                "Proof. zesu_block. Qed.\n"
                "Lemma pure_fact : True.\nProof. exact I. Qed.\n")
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / name
            path.parent.mkdir(parents=True)
            path.write_text(text)
            with patch("check_proof_hygiene.ROOT", Path(root)):
                self.assertEqual(generated_hand_line_failures(name, text), [])

    def test_handwritten_instruction_body_needs_no_residual_record(self):
        self.assertEqual(generated_hand_line_failures(
            "ZesuSsz/Proofs/Test.v",
            "Lemma block_1 : instr_body 0x1 spec.\nProof. iIntros. Qed.\n"), [])

    def test_proof_using_keeps_the_40_line_limit(self):
        lines = ["Lemma block_1 : instr_body 0x1 spec.",
                 "Proof using All.", *["  iFrame."] * 41, "Qed."]
        self.assertEqual(proof_size_warnings("Test.v", lines),
                         ["instr_body proof has 41 lines: Test.v:2"])


class TrustedDeclarationTests(unittest.TestCase):
    name = "ZesuSsz/Automation/EntryIntro.v"
    ml = 'Declare ML Module "zesu-signature-gates.plugin".'
    external = ('Ltac2 @ external zesu_unique_entry_registration : unit -> unit :=\n'
                '  "zesu-signature-gates.plugin" "unique_entry_registration".')

    def scan(self, name, source):
        """Exercise main and its actual git file inventory with a planted file."""
        with tempfile.TemporaryDirectory() as root:
            subprocess.run(["git", "init", "--quiet", root], check=True)
            path = Path(root) / name
            path.parent.mkdir(parents=True)
            path.write_text(source)
            with patch("check_proof_hygiene.ROOT", Path(root)):
                main()

    def test_exact_allowlist_has_nineteen_declarations(self):
        self.assertEqual(len(trusted_declarations()), 19)

    def test_approved_statements_accept_whitespace_and_comments(self):
        source = ('Declare (* note *) ML\nModule "zesu-signature-gates.plugin".\n'
                  'Ltac2 @external zesu_unique_entry_registration\n'
                  ' : (* note *) unit -> unit := "zesu-signature-gates.plugin"\n'
                  ' "unique_entry_registration".\n')
        self.scan(self.name, source)

    def test_changed_plugin_symbol_signature_and_path_fail(self):
        cases = (
            (self.name, self.ml.replace(".plugin", ".other"), "ML"),
            (self.name, self.external.replace('"unique_entry_registration"', '"other"'), "external"),
            (self.name, self.external.replace("unit -> unit", "unit -> bool"), "external"),
            (self.name, "Local " + self.ml, "ML"),
            (self.name, "#[local] " + self.external, "external"),
            ("ZesuSsz/Automation/Moved.v", self.ml, "ML"),
            ("ZesuSsz/Automation/Moved.v", self.external, "external"),
        )
        for name, source, kind in cases:
            with self.subTest(name=name, source=source):
                with self.assertRaises(SystemExit) as raised:
                    self.scan(name, source)
                self.assertEqual(str(raised.exception), f"unapproved {kind} declaration: {name}:1")

    def test_new_declarations_fail_in_an_approved_file(self):
        for source, kind in (
            (self.ml + '\nDeclare ML Module "other.plugin".', "ML"),
            (self.external + '\nLtac2 @external other : unit -> unit := "other.plugin" "other".', "external"),
        ):
            with self.subTest(kind=kind):
                with self.assertRaises(SystemExit) as raised:
                    self.scan(self.name, source)
                line = source.count("\n") + 1
                self.assertEqual(str(raised.exception),
                                 f"unapproved {kind} declaration: {self.name}:{line}")

    def test_repeated_trusted_declaration_is_not_a_new_allowance(self):
        with self.assertRaises(SystemExit) as raised:
            self.scan(self.name, self.ml + "\n" + self.ml)
        self.assertEqual(str(raised.exception), f"unapproved ML declaration: {self.name}:2")

    def test_declaration_text_in_comments_or_strings_is_not_executable(self):
        source = ('(* Declare ML Module "other.plugin". (* nested *)\n'
                  'Ltac2 @external other : unit -> unit := "other" "other". *)\n'
                  'Definition message := "Declare ML Module ""other"". Ltac2 @external other".\n')
        self.scan("tools/Planted.v", source)

    def test_normalization_preserves_literal_string_contents(self):
        changed = self.ml.replace("zesu-signature-gates.plugin", "zesu-signature-gates. plugin")
        self.assertNotEqual(normalized_declaration(self.ml), normalized_declaration(changed))
        self.assertTrue(trusted_declaration_failures(self.name, changed, trusted_declarations()))


if __name__ == "__main__":
    unittest.main()
