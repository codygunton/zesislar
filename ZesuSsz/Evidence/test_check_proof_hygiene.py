import unittest
import tempfile
import subprocess
from pathlib import Path
from unittest.mock import patch

from check_proof_hygiene import (
    PLACEHOLDER,
    assert_fails_match_failures,
    automation_lia_call_failures,
    automation_entry_failures,
    FROZEN_AUTOMATION_TREE,
    frozen_automation_failures,
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
    def setUp(self):
        self.freeze = patch("check_proof_hygiene.frozen_automation_failures", return_value=[])
        self.freeze.start()
        self.addCleanup(self.freeze.stop)

    def test_core_umbrella_policy(self):
        name = "ZesuSsz/Proofs/Tests/EntryFixture.v"
        old = "Require Import ZesuSsz.Automation.All.\n"
        new = "Require Import ZesuSsz.Automation2.All.\n"
        legacy = "Require Import ZesuSsz.Automation.AllLegacy.\n"
        for source, approved in ((old, set()), (new, set()), (legacy, {name})):
            with self.subTest(source=source):
                self.assertEqual(automation_entry_failures(name, source, approved), [])
        rejected = (
            ("", set()),
            ("Require Import ZesuSsz.Automation2.MemoryAddress.\n", set()),
            (old + new, set()),
            (old + legacy, {name}),
            (new + legacy, {name}),
            (legacy, set()),
            ("(* " + new + " *)", set()),
            ('Definition text := "' + new.strip() + '".\n', set()),
        )
        for source, approved in rejected:
            with self.subTest(source=source):
                self.assertTrue(automation_entry_failures(name, source, approved))
        self.assertEqual(automation_entry_failures(name, new + "(* " + old + " *)", set()), [])

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

    def test_assert_fails_match_requires_idtac_delay(self):
        name = "ZesuSsz/Automation2/Planted.v"
        bad = ("Ltac a := assert_fails (match goal with _ => idtac end).\n"
               "Ltac b := assert_fails(lazymatch goal with _ => idtac end).\n"
               "Ltac c := assert_fails ltac:(\n  multimatch goal with _ => idtac end).\n")
        self.assertEqual(assert_fails_match_failures(name, bad), [
            f"assert_fails with an undelayed match (use `idtac; match`): {name}:{n}"
            for n in (1, 2, 3)])
        self.assertEqual(len(assert_fails_match_failures("ZesuSsz/Proofs/P.v", bad)), 3)
        self.assertEqual(assert_fails_match_failures("ZesuSsz/Automation/P.v", bad), [])
        good = ("Ltac a := assert_fails (idtac; match goal with _ => idtac end).\n"
                "Ltac b := assert_fails ltac:(idtac; multimatch goal with _ => idtac end).\n"
                "Ltac c := assert_fails (has_evar x).\n"
                "(* assert_fails (match goal with _ => idtac end) *)\n")
        self.assertEqual(assert_fails_match_failures(name, good), [])

    def test_automation_tactics_call_the_project_lia(self):
        name = "ZesuSsz/Automation2/Planted.v"
        bad = ("Ltac a := first [zesu_lia | lia].\n"
               "Ltac b x :=\n  assert (x = x) by Lia.lia.\n"
               "#[export] Hint Extern 1 (_ < _) => Coq.micromega.Lia.lia : core.\n"
               "Ltac2 c () := ltac1:(lia).\n")
        self.assertEqual(automation_lia_call_failures(name, bad), [
            f"Automation2 tactic calls lia (call zesu_lia): {name}:{n}" for n in (1, 3, 4, 5)])
        self.assertEqual(automation_lia_call_failures("ZesuSsz/Contracts/P.v", bad), [])
        good = ("Ltac zesu_lia := lia.\n"
                "Ltac Lia.lia ::= zesu_lia.\n"
                "Ltac a := first [zesu_lia | xlia Lia.zchecker | zesu_finish_lia].\n"
                "(* Ltac b := lia. *)\n"
                "Lemma l : 1 = 1.\nProof. lia. Qed.\n")
        self.assertEqual(automation_lia_call_failures(name, good), [])

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
    def setUp(self):
        self.freeze = patch("check_proof_hygiene.frozen_automation_failures", return_value=[])
        self.freeze.start()
        self.addCleanup(self.freeze.stop)

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
        self.assertEqual(len(trusted_declarations()), 38)

    def test_automation2_keeps_the_same_hook_owner_boundary(self):
        self.scan("ZesuSsz/Automation2/Hooks.v", "Ltac liAStep ::= idtac.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Automation2/Other.v", "Ltac liAStep ::= idtac.")

    def test_qualified_hook_redefinition_is_refused_outside_hooks(self):
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Automation2/Other.v",
                      "Ltac ZesuSsz.Automation2.Finish.zesu_block_tail_one ::= idtac.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Automation2/Other.v", "Ltac isla.base.unLET ::= idtac.")

    def test_project_hook_allowlist_permits_one_owner_redefinition(self):
        self.scan("ZesuSsz/Automation2/BlockTail.v",
                  "Ltac ZesuSsz.Automation2.Finish.zesu_block_tail_one ::= idtac.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Automation2/BlockTail.v",
                      "Ltac ZesuSsz.Automation2.Finish.zesu_block_tail_one ::= idtac.\n"
                      "Ltac ZesuSsz.Automation2.Finish.zesu_block_tail_one ::= fail.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Automation2/BlockTail.v", "Ltac liAStep ::= idtac.")

    def test_tests_may_redefine_project_tactics_locally_only(self):
        umbrella = "Require Import ZesuSsz.Automation2.All.\n"
        self.scan("ZesuSsz/Proofs/Tests/Local.v",
                  umbrella + "#[local] Ltac ZesuSsz.Automation2.Hooks.zesu_open_folded_facts ::= idtac.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Proofs/Tests/Local.v",
                      umbrella + "Ltac ZesuSsz.Automation2.Hooks.zesu_open_folded_facts ::= idtac.")
        with self.assertRaisesRegex(SystemExit, "Lithium hook redefinition"):
            self.scan("ZesuSsz/Proofs/Tests/Local.v", umbrella + "#[local] Ltac liAStep ::= idtac.")

    def test_automation2_has_the_same_forbidden_name_scope(self):
        self.scan("ZesuSsz/Automation2/Rule.v", "Definition zesu_lbu_byte_array_at_spec (value : nat) := value.")
        with self.assertRaisesRegex(SystemExit, "forbidden-name increase"):
            self.scan("tools/Rule.v", "Definition zesu_lbu_byte_array_at_spec (value : nat) := value.")

    def test_automation2_trust_mirrors_only_existing_automation_declarations(self):
        # Telemetry.v (solver telemetry: switch, clock, RSS and print only),
        # FailureMemo.v (per-proof solver failure memo: hash and table only) and
        # SwitchDispatch.v's switch memo (a per-run table only) have no
        # Automation counterpart.
        approved = trusted_declarations()
        old = {(name, body) for name, body in approved if name.startswith("ZesuSsz/Automation/")}
        new = {(name.replace("/Automation2/", "/Automation/"), body)
               for name, body in approved if name.startswith("ZesuSsz/Automation2/")
               and name not in ("ZesuSsz/Automation2/Telemetry.v", "ZesuSsz/Automation2/FailureMemo.v",
                                "ZesuSsz/Automation2/SwitchDispatch.v")}
        self.assertEqual(new, old)
        self.assertTrue(trusted_declaration_failures("ZesuSsz/Automation2/Other.v", self.ml, approved))
        self.assertTrue(trusted_declaration_failures("ZesuSsz/Automation2/EntryIntro.v",
            self.ml.replace("zesu-signature-gates.plugin", "other.plugin"), approved))

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



class FrozenAutomationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "--quiet")
        self.source = self.root / "ZesuSsz/Automation/Rule.v"
        self.source.parent.mkdir(parents=True)
        self.source.write_text("Definition frozen := 1.\n")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "Freeze")
        self.revision = self.git("rev-parse", "HEAD:ZesuSsz/Automation").strip()
        environment = patch.dict("os.environ", {"ZESU_AUTOMATION_EMERGENCY_OVERRIDE": ""})
        environment.start()
        self.addCleanup(environment.stop)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True)

    def check(self):
        return frozen_automation_failures(self.root, self.revision)

    def test_pin_matches_the_current_legacy_tree(self):
        root = Path(__file__).resolve().parents[2]
        recorded = subprocess.check_output([
            "git", "-C", str(root), "rev-parse",
            "HEAD:ZesuSsz/Automation"], text=True).strip()
        self.assertEqual(recorded, FROZEN_AUTOMATION_TREE)

    def test_shallow_clone_needs_only_the_current_tree(self):
        original = self.git("rev-parse", "HEAD").strip()
        (self.root/"README").write_text("A later commit retains the frozen tree.")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "Later")
        with tempfile.TemporaryDirectory() as destination:
            clone = Path(destination)/"shallow"
            subprocess.run(["git", "clone", "--quiet", "--depth", "1",
                self.root.as_uri(), str(clone)], check=True)
            absent = subprocess.run(["git", "-C", str(clone), "cat-file", "-e", original],
                capture_output=True)
            self.assertNotEqual(absent.returncode, 0)
            current = subprocess.check_output(["git", "-C", str(clone), "rev-parse",
                "HEAD:ZesuSsz/Automation"], text=True).strip()
            self.assertEqual(current, self.revision)
            self.assertEqual(frozen_automation_failures(clone, self.revision), [])
            source = clone/"ZesuSsz/Automation/Rule.v"
            source.write_text("Definition changed := 2.\n")
            self.assertTrue(frozen_automation_failures(clone, self.revision))

    def test_unchanged_tree_and_automation2_changes_pass(self):
        other = self.root / "ZesuSsz/Automation2/Rule.v"
        other.parent.mkdir()
        other.write_text("Definition new := 2.\n")
        self.assertEqual(self.check(), [])

    def test_dirty_staged_and_committed_changes_remain_refused(self):
        self.source.write_text("Definition frozen := 2.\n")
        self.assertEqual(len(self.check()), 1)
        self.git("add", ".")
        self.assertEqual(len(self.check()), 1)
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "Change")
        self.assertEqual(len(self.check()), 1)

    def test_deletions_and_new_files_are_refused(self):
        self.source.unlink()
        added = self.source.with_name("Added.v")
        added.write_text("Definition new := 2.\n")
        self.assertEqual(len(self.check()), 2)

    def test_explicit_emergency_reason_is_visible(self):
        self.source.write_text("Definition frozen := 2.\n")
        with patch.dict("os.environ", {"ZESU_AUTOMATION_EMERGENCY_OVERRIDE": "Issue17 emergency approval"}), \
                patch("sys.stderr") as output:
            self.assertEqual(self.check(), [])
            self.assertIn("Issue17 emergency approval", str(output.write.call_args_list))

if __name__ == "__main__":
    unittest.main()


class ShortCoreNameTests(unittest.TestCase):
    """Short names of modules in both cores can resolve to the frozen core."""

    HEADER = "Require Import ZesuSsz.Automation2.All.\n"

    def failures(self, name, text):
        from check_proof_hygiene import short_core_name_failures
        return short_core_name_failures(name, text, {"ContextCollection", "Hooks"})

    def test_short_shared_name_in_an_automation2_test_fails(self):
        text = self.HEADER + "Goal True.\nProof. ContextCollection.zesu_context_prune_goal. Qed.\n"
        failures = self.failures("ZesuSsz/Proofs/Tests/X.v", text)
        self.assertEqual(len(failures), 1)
        self.assertIn("X.v:3: ContextCollection.", failures[0])

    def test_full_names_imports_comments_and_other_trees_pass(self):
        text = (self.HEADER + "Require Import ZesuSsz.Automation2.ContextCollection.\n"
                "(* ContextCollection.zesu_context_prune_goal *)\n"
                "Goal True. Proof. ZesuSsz.Automation2.ContextCollection.zesu_context_prune_goal. Qed.\n")
        self.assertEqual(self.failures("ZesuSsz/Proofs/Tests/X.v", text), [])
        short = self.HEADER + "Ltac t := Hooks.zesu_run.\n"
        self.assertEqual(self.failures("ZesuSsz/Residuals/Block800d1234.v", short), [])
        self.assertEqual(self.failures("ZesuSsz/Proofs/Tests/Y.v",
                                       "Require Import ZesuSsz.Automation.All.\n" + short[len(self.HEADER):]), [])

    def test_shared_modules_include_context_collection(self):
        from check_proof_hygiene import shared_core_modules
        self.assertIn("ContextCollection", shared_core_modules())


class DuplicateRewriteTests(unittest.TestCase):
    """One lemma is registered once per rewrite database and direction."""

    def failures(self, sources):
        from check_proof_hygiene import duplicate_rewrite_failures
        return duplicate_rewrite_failures(sources)

    def test_second_registration_in_one_database_fails(self):
        sources = {
            "ZesuSsz/Automation2/A.v": "#[export] Hint Rewrite lemma_a (@lemma_b 64) : db_one db_two.\n",
            "ZesuSsz/Automation2/B.v": ("(* lemma_a *)\n#[export] Hint Rewrite (@lemma_b 64)\n"
                                        "  lemma_c using (first [idtac | bv_solve]) : db_two.\n"),
        }
        failures = self.failures(sources)
        self.assertEqual(len(failures), 1)
        self.assertIn("(@lemma_b 64) (->) in db_two", failures[0])
        self.assertIn("A.v:1", failures[0])
        self.assertIn("B.v:2", failures[0])

    def test_local_other_database_and_other_direction_pass(self):
        sources = {
            "ZesuSsz/Automation2/A.v": "#[export] Hint Rewrite lemma_a : db_one.\n",
            "ZesuSsz/Automation2/B.v": ("#[local] Hint Rewrite lemma_a : db_one.\n"
                                        "#[export] Hint Rewrite lemma_a : db_two.\n"
                                        "#[export] Hint Rewrite <- lemma_a : db_one.\n"),
        }
        self.assertEqual(self.failures(sources), [])


class FrozenGlobalTests(unittest.TestCase):
    """A frozen Global instance loaded by the Automation2 umbrella is removed."""

    def write(self, root, module, text):
        path = Path(root) / (module.replace(".", "/") + ".v")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_loaded_frozen_instance_needs_a_removal(self):
        from check_proof_hygiene import frozen_global_failures
        with tempfile.TemporaryDirectory() as root:
            self.write(root, "ZesuSsz.Automation.Frozen",
                       "Definition frozen_inst := 0.\nGlobal Existing Instance frozen_inst | 5.\n"
                       "Global Instance frozen_other : C.\nGlobal Existing Instance library_inst | 20.\n")
            self.write(root, "ZesuSsz.Automation.Unloaded", "Global Existing Instance unloaded_inst.\n")
            self.write(root, "ZesuSsz.Automation2.All",
                       "Require ZesuSsz.Automation.Frozen.\n(* Require ZesuSsz.Automation.Unloaded. *)\n")
            failures = frozen_global_failures(root)
            self.assertEqual(sorted(failures), [
                "frozen Global instance active beside Automation2: ZesuSsz.Automation.Frozen.frozen_inst",
                "frozen Global instance active beside Automation2: ZesuSsz.Automation.Frozen.frozen_other"])
            self.write(root, "ZesuSsz.Automation2.All",
                       "Require ZesuSsz.Automation.Frozen.\nRequire Export ZesuSsz.Automation2.Removal.\n")
            self.write(root, "ZesuSsz.Automation2.Removal",
                       "Global Remove Hints ZesuSsz.Automation.Frozen.frozen_inst : typeclass_instances.\n")
            self.assertEqual(frozen_global_failures(
                root, allowlist={"ZesuSsz.Automation.Frozen.frozen_other": "reason"}), [])


class SealedCalleeTests(unittest.TestCase):
    """A caller treats a proved callee as a black box."""

    CALLEES = [{
        "interfaces": ["ZesuSsz/Interfaces/Callee.v", "ZesuSsz/Interfaces/CalleeCorrect.v"],
        "sealed": ["calleeCallMeaning"],
        "restricted": ["calleeCallSpec2CorrectFrom", "calleeCallMeaningLink"],
        "unsealed": ["CalleeMeaning"],
        "owned_prefixes": ["ZesuSsz/Generated/Callee/"],
    }]

    def failures(self, name, text):
        from check_proof_hygiene import sealed_callee_failures
        return sealed_callee_failures(name, text, self.CALLEES)

    def test_interface_modules_may_use_the_bridge(self):
        text = "Definition c := calleeCallSpec2CorrectFrom code entry template_correct.\n"
        self.assertEqual(self.failures("ZesuSsz/Interfaces/CalleeCorrect.v", text), [])

    def test_bridge_or_link_outside_the_interface_fails(self):
        self.assertEqual(self.failures("ZesuSsz/Proofs/Block.v", "Proof. apply calleeCallMeaningLink. Qed.\n"),
                         ["sealed callee interface used outside it: ZesuSsz/Proofs/Block.v:1: calleeCallMeaningLink"])

    def test_unfolding_a_sealed_name_fails(self):
        for text in ("Proof. unfold foo, calleeCallMeaning in H. Qed.\n",
                     "Transparent calleeCallMeaning.\n"):
            with self.subTest(text=text):
                self.assertEqual(self.failures("ZesuSsz/Automation2/Rule.v", text),
                                 ["sealed callee predicate unfolded: ZesuSsz/Automation2/Rule.v:1: calleeCallMeaning"])

    def test_unsealed_predicate_in_another_functions_entry_fails(self):
        text = "Definition e := ⌜CalleeMeaning args after⌝.\n"
        self.assertEqual(self.failures("ZesuSsz/Generated/Caller/Pilot0040Entries.v", text),
                         ["unsealed callee predicate in a caller entry: "
                          "ZesuSsz/Generated/Caller/Pilot0040Entries.v:1: CalleeMeaning"])
        self.assertEqual(self.failures("ZesuSsz/Generated/Callee/Pilot0040Entries.v", text), [])

    def test_sealed_use_comments_and_longer_names_pass(self):
        text = ("(* apply calleeCallMeaningLink; unfold calleeCallMeaning *)\n"
                "Definition e := ⌜calleeCallMeaning args after⌝.\n"
                "Lemma calleeCallMeaningLink2 : True. Proof. unfold calleeCallMeaningX. Qed.\n")
        self.assertEqual(self.failures("ZesuSsz/Generated/Caller/Pilot0040Entries.v", text), [])

    def test_parameter_and_axiom_only_inside_an_interface_signature(self):
        from check_proof_hygiene import interface_signature_lines
        text = ("Module Type SealedSignature.\n  Parameter p : Prop.\n  Axiom a : p.\nEnd SealedSignature.\n"
                "Module Sealed : SealedSignature.\nEnd Sealed.\nAxiom outside : False.\n")
        self.assertEqual(interface_signature_lines(text), {2, 3})


class EdgeProofTests(unittest.TestCase):
    """EDGE-PROOF: generated history edge modules may hold proofs from EDGE_SENTENCES only."""
    name = "ZesuSsz/Generated/NextUint64/FP301/Edges0070.v"
    edge = ("Global Instance zesu_hist_edge_8 (args : A) (x : bv 64) :\n"
            "  ZesuHistEdge (PROP := iProp Sigma) (e_Hist args x) (f_Hist args x) (True)%I.\n"
            "Proof.\n"
            "  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold e_Hist in Hh.\n"
            "  destruct Hh as (g & HF0 & HF1).\n"
            "  iIntros \"HN\".\n"
            "  iPureIntro. apply zesu_hist_intro. unfold f_Hist.\n"
            "  exists g.\n"
            "  split; [exact HF0|].\n"
            "  by vm_compute.\n"
            "Qed.\n")

    def failures(self, name, text):
        from check_proof_hygiene import edge_proof_failures
        return edge_proof_failures(name, text)

    def test_a_conforming_edge_module_passes(self):
        self.assertEqual(self.failures(self.name, self.edge), [])

    def test_admitted_is_refused(self):
        text = self.edge.replace("  by vm_compute.\nQed.\n", "Admitted.\n")
        self.assertTrue(any("Admitted" in failure for failure in self.failures(self.name, text)))

    def test_a_sentence_outside_the_list_is_refused(self):
        text = self.edge.replace("  by vm_compute.\n", "  lia.\n")
        self.assertEqual(self.failures(self.name, text),
                         ["EDGE-PROOF: " + self.name + ": sentence outside EDGE_SENTENCES: lia"])

    def test_ltac_and_axiom_are_refused(self):
        for line in ("Ltac t := idtac.\n", "Axiom bad : False.\n"):
            with self.subTest(line=line):
                self.assertTrue(self.failures(self.name, line + self.edge))

    def test_the_rule_applies_to_edge_modules_only(self):
        self.assertEqual(self.failures("ZesuSsz/Generated/NextUint64/FP301/Pilot0070Entries.v",
                                       self.edge.replace("by vm_compute", "lia")), [])

    def test_the_list_is_the_renderers(self):
        import check_proof_hygiene
        import render_edges
        self.assertIs(check_proof_hygiene.edge_proof_problems, render_edges.edge_proof_problems)
