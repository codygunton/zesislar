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


class ManifestFixture:
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


class DataOnlyLemmaTests(ManifestFixture, unittest.TestCase):
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


class RegistrationParserTests(unittest.TestCase):
    def test_named_classes_and_source_heads(self):
        records = check_data_only_lemmas.registrations("""
#[global] Instance first {Sigma} (args : Args) :
  ZesuEntryIntro (Contracts.entry args) (fact args).
Proof. exact certified. Qed.
Local Instance second (args : Args) :
  ZesuLoopStep (Contracts.header args) (step args) := certified_step.
""", "Registrations")
        self.assertEqual([(r.name, r.class_name, r.predicate) for r in records],
                         [("Registrations.first", "ZesuEntryIntro", "Contracts.entry"),
                          ("Registrations.second", "ZesuLoopStep", "Contracts.header")])

    def test_explicit_and_named_implicit_class_arguments(self):
        records = check_data_only_lemmas.registrations("""
Global Instance first : @Rules.ZesuEntryIntro Sigma (@Contracts.entry Sigma args) fact.
Global Instance second : Rules.ZesuLoopStep (Sigma := Sigma) (Contracts.header args) fact.
""")
        self.assertEqual([r.predicate for r in records], ["Contracts.entry", "Contracts.header"])

    def test_premises_quantifiers_and_parentheses(self):
        records = check_data_only_lemmas.registrations("""
Instance first : forall (x : nat), (Ready x) ->
  (ZesuEntryIntro ((Contracts.entry (pair x x)) : Resource) (facts x)).
Instance second : forall x, ZesuEntryIntro (Contracts.premise x) True ->
  ZesuLoopStep (Contracts.header x) True.
""")
        self.assertEqual([(r.class_name, r.predicate) for r in records],
                         [("ZesuEntryIntro", "Contracts.entry"),
                          ("ZesuLoopStep", "Contracts.header")])

    def test_comments_strings_and_unrelated_instances_are_not_registrations(self):
        records = check_data_only_lemmas.registrations('''
(* Instance fake : ZesuEntryIntro Entry True. (* nested *) "*)" *)
Definition note := "Instance fake : ZesuLoopStep Header True. ""quoted""".
Instance unrelated : Other (ZesuEntryIntro Entry True) := evidence.
Instance real : ZesuEntryIntro Entry True := evidence.
''')
        self.assertEqual([r.name for r in records], ["real"])

    def test_priority_does_not_distinguish_registrations(self):
        records = check_data_only_lemmas.registrations("""
Instance first : ZesuEntryIntro Entry True | 10 := certificate.
Instance second : ZesuEntryIntro Entry Other | 20 := certificate.
""")
        self.assertEqual([r.predicate for r in records], ["Entry", "Entry"])

    def test_local_definitions_keep_module_namespaces_distinct(self):
        records = check_data_only_lemmas.registrations("""
Module Left.
Section Left.
Definition entry := resource.
Instance first : ZesuEntryIntro entry True := certificate.
End Left.
Instance second : ZesuLoopStep entry True := certificate.
End Left.
Module Right.
Definition entry := other_resource.
Instance third : ZesuEntryIntro entry True := certificate.
End Right.
""", "Registrations")
        self.assertEqual([r.predicate for r in records],
                         ["Registrations.Left.entry", "Registrations.Left.entry",
                          "Registrations.Right.entry"])

    def test_anonymous_targeted_instance_fails(self):
        with self.assertRaisesRegex(ValueError, "explicit instance name"):
            check_data_only_lemmas.registrations("Instance : ZesuEntryIntro Entry True.")

    def test_qualified_local_heads_and_module_export_match(self):
        records = check_data_only_lemmas.registrations("""
Module Export Inner.
Local Definition entry := resource.
Instance first : ZesuEntryIntro entry True := certificate.
End Inner.
Instance second : ZesuEntryIntro Inner.entry True := certificate.
""", "Registrations")
        self.assertEqual([r.predicate for r in records],
                         ["Registrations.Inner.entry", "Registrations.Inner.entry"])

    def test_malformed_delimiters_fail(self):
        for source in ["Instance first : ZesuEntryIntro (Entry args] True.",
                       "Instance first : ZesuEntryIntro (Entry args True."]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                check_data_only_lemmas.registrations(source)

    def test_unsupported_source_expression_fails(self):
        with self.assertRaisesRegex(ValueError, "named predicate head"):
            check_data_only_lemmas.registrations(
                "Instance first : ZesuEntryIntro (fun x => Entry x) True.")

    def test_incomplete_arguments_comments_and_strings_fail(self):
        for source in ["Instance first : ZesuEntryIntro.", "(* unterminated",
                       'Definition note := "unterminated']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                check_data_only_lemmas.registrations(source)


class RegistrationManifestTests(ManifestFixture, unittest.TestCase):
    def setUp(self):
        super().setUp()
        (self.root / "Contracts.v").write_text("""
Definition entry := resource.
Definition Entry := resource.
Module Left. Definition entry := resource. End Left.
Module Right. Definition entry := other_resource. End Right.
""")
        self.manifest["contracts"] = ["Contracts.v"]

    def add_file(self, category, text):
        if category == "registrations":
            text = "Require Import Contracts.\n" + text
        super().add_file(category, text)

    def test_duplicate_intro_reports_both_names(self):
        self.add_file("registrations", """
Instance first : ZesuEntryIntro (Contracts.entry left) LeftFacts := left_certificate.
Instance second : ZesuEntryIntro (Contracts.entry right) RightFacts := right_certificate.
""")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Duplicate ZesuEntryIntro", errors[0])
        self.assertIn("registrations.first", errors[0])
        self.assertIn("registrations.second", errors[0])

    def test_duplicates_across_modules_and_classes_are_checked(self):
        for cls in check_data_only_lemmas.REGISTRATION_CLASSES:
            with self.subTest(cls=cls):
                self.add_file("registrations", f"Instance first : {cls} Contracts.entry Left := proof.")
                other = self.evidence / "Other.v"
                other.write_text(f"Instance second : {cls} Contracts.entry Right := proof.")
                self.manifest["registrations"].append(str(other.relative_to(self.root)))
                self.write_manifest()
                errors = check_data_only_lemmas.violations(self.root)
                self.assertEqual(len(errors), 1)
                self.assertIn("registrations.first", errors[0])
                self.assertIn("Other.second", errors[0])

    def test_intro_instances_in_different_manifest_categories_share_a_key(self):
        self.add_file("introductions", """
Require Import Contracts.
Instance base : ZesuEntryIntro entry Left := first_certificate.
""")
        self.add_file("registrations", """
Instance additional : ZesuEntryIntro Contracts.entry Right := second_certificate.
""")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Duplicate ZesuEntryIntro registration for Contracts.entry", errors[0])
        self.assertIn("introductions.base", errors[0])
        self.assertIn("registrations.additional", errors[0])

    def test_loop_instances_in_different_manifest_categories_share_a_key(self):
        self.add_file("loop_steps", """
Require Import Contracts.
Instance base : ZesuLoopStep entry Left := first_certificate.
""")
        self.add_file("registrations", """
Instance additional : ZesuLoopStep Contracts.entry Right := second_certificate.
""")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("loop_steps.base", errors[0])
        self.assertIn("registrations.additional", errors[0])

    def test_aliases_resolve_across_declared_module_categories(self):
        self.add_file("introductions", """
Definition alias := Contracts.entry.
Instance base : ZesuEntryIntro alias Left := first_certificate.
""")
        self.add_file("registrations", """
Instance additional : ZesuEntryIntro Contracts.entry Right := second_certificate.
""")
        self.manifest["aliases"] = {"ZesuSsz.Evidence.introductions.alias": "Contracts.entry"}
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Contracts.entry", errors[0])
        self.assertIn("introductions.base", errors[0])
        self.assertIn("registrations.additional", errors[0])

    def test_exported_unlisted_registration_module_fails(self):
        self.add_file("registrations", """
Require Export ZesuSsz.Evidence.Unlisted.
Instance first : ZesuEntryIntro Contracts.entry Left := first_certificate.
""")
        (self.evidence / "Unlisted.v").write_text("""
Instance second : ZesuEntryIntro Contracts.entry Right := second_certificate.
""")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Unlisted registration module: ZesuSsz/Evidence/Unlisted.v", errors[0])
        self.assertIn("exported by ZesuSsz/Evidence/registrations.v", errors[0])

    def test_exported_listed_registration_module_is_checked(self):
        self.add_file("registrations", "Require Export ZesuSsz.Evidence.Listed.")
        path = self.evidence / "Listed.v"
        path.write_text("Instance unique : ZesuEntryIntro Contracts.entry True := proof.")
        self.manifest["registrations"].append(str(path.relative_to(self.root)))
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_unlisted_registration_through_export_chain_fails(self):
        self.add_file("registrations", "From ZesuSsz.Evidence Require Export Bridge.")
        (self.evidence / "Bridge.v").write_text(
            "Require Export ZesuSsz.Evidence.Hidden.")
        (self.evidence / "Hidden.v").write_text(
            "Instance hidden : ZesuLoopStep Contracts.entry True := proof.")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Hidden.v", errors[0])
        self.assertIn("Bridge.v", errors[0])

    def test_export_cycle_terminates_without_registration(self):
        self.add_file("registrations", "Require Export ZesuSsz.Evidence.Bridge.")
        (self.evidence / "Bridge.v").write_text(
            "Require Export ZesuSsz.Evidence.registrations.")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_import_does_not_trigger_export_policy(self):
        self.add_file("registrations", "Require Import ZesuSsz.Evidence.Hidden.")
        (self.evidence / "Hidden.v").write_text(
            "Instance hidden : ZesuEntryIntro Contracts.entry True := proof.")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_export_comment_and_string_do_not_trigger_policy(self):
        self.add_file("registrations", '''
(* Require Export ZesuSsz.Evidence.Hidden. *)
Definition label := "Require Export ZesuSsz.Evidence.Hidden.".
''')
        (self.evidence / "Hidden.v").write_text(
            "Instance hidden : ZesuEntryIntro Contracts.entry True := proof.")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_another_manifest_cannot_cover_an_unlisted_export(self):
        self.add_file("registrations", "Require Export ZesuSsz.Evidence.Hidden.")
        hidden = self.evidence / "Hidden.v"
        hidden.write_text("Instance hidden : ZesuEntryIntro Contracts.entry True := proof.")
        self.write_manifest("first")
        self.manifest["registrations"] = [str(hidden.relative_to(self.root))]
        self.write_manifest("second")
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("first_function_text.json", errors[0])

    def test_different_classes_and_qualified_predicates_pass(self):
        self.add_file("registrations", """
Instance intro : ZesuEntryIntro Contracts.Left.entry True := proof.
Instance step : ZesuLoopStep Contracts.Left.entry True := proof.
Instance other : ZesuEntryIntro Contracts.Right.entry True := proof.
""")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_repeated_manifest_paths_do_not_duplicate_an_instance(self):
        self.add_file("registrations", "Instance first : ZesuEntryIntro Entry True := proof.")
        self.manifest["registrations"] *= 2
        self.write_manifest("first")
        self.write_manifest("second")
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_unlisted_registration_modules_are_not_scanned(self):
        (self.evidence / "Unlisted.v").write_text("""
Instance first : ZesuEntryIntro Entry True := proof.
Instance second : ZesuEntryIntro Entry Other := proof.
""")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_unsupported_registration_is_reported_with_its_file(self):
        self.add_file("registrations", "Instance : ZesuLoopStep Entry True.")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("ZesuSsz/Evidence/registrations.v", errors[0])
        self.assertIn("explicit instance name", errors[0])

    def test_imported_and_qualified_predicates_share_a_key(self):
        self.add_file("registrations", """
Instance first : ZesuEntryIntro entry True := proof.
Instance second : ZesuEntryIntro Contracts.entry Other := proof.
""")
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Contracts.entry", errors[0])
        self.assertIn("registrations.first", errors[0])
        self.assertIn("registrations.second", errors[0])

    def test_from_imports_and_reexports_resolve_predicates(self):
        package = self.root / "Package"
        package.mkdir()
        (package / "Source.v").write_text("Definition entry := resource.")
        (package / "Umbrella.v").write_text("From Package Require Export Source.")
        self.manifest["contracts"].extend(["Package/Source.v", "Package/Umbrella.v"])
        self.add_file("registrations", """
From Package Require Import Umbrella.
Instance first : ZesuLoopStep entry True := proof.
Instance second : ZesuLoopStep Package.Source.entry Other := proof.
""")
        self.write_manifest()
        # Contracts.entry and Package.Source.entry are both visible. Require a
        # qualified source instead of silently choosing one imported declaration.
        self.assertIn("ambiguous", check_data_only_lemmas.violations(self.root)[0])
        (self.evidence / "registrations.v").write_text("""
From Package Require Import Umbrella.
Instance first : ZesuLoopStep entry True := proof.
Instance second : ZesuLoopStep Package.Source.entry Other := proof.
""")
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Duplicate ZesuLoopStep", errors[0])
        self.assertIn("Package.Source.entry", errors[0])

    def test_unresolved_predicate_is_rejected(self):
        self.add_file("registrations", "Instance first : ZesuEntryIntro Missing.entry True := proof.")
        self.write_manifest()
        self.assertIn("unresolved registration key: Missing.entry",
                      check_data_only_lemmas.violations(self.root)[0])

    def test_definition_alias_duplicate_reports_both_names(self):
        self.add_file("registrations", """
Definition alias := Contracts.entry.
Instance original : ZesuEntryIntro Contracts.entry True := proof.
Instance duplicate : ZesuEntryIntro alias Other := proof.
""")
        self.manifest["aliases"] = {"ZesuSsz.Evidence.registrations.alias": "Contracts.entry"}
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("registrations.original", errors[0])
        self.assertIn("registrations.duplicate", errors[0])
        self.assertIn("Contracts.entry", errors[0])

    def test_named_notation_alias_and_short_alias_key(self):
        self.add_file("registrations", """
Notation \"alias\" := Contracts.entry.
Instance original : ZesuLoopStep entry True := proof.
Instance duplicate : ZesuLoopStep alias Other := proof.
""")
        self.manifest["aliases"] = {"alias": "Contracts.entry"}
        self.write_manifest()
        errors = check_data_only_lemmas.violations(self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("Duplicate ZesuLoopStep", errors[0])
        self.assertIn("registrations.original", errors[0])
        self.assertIn("registrations.duplicate", errors[0])

    def test_aliases_are_not_inferred_without_manifest_metadata(self):
        self.add_file("registrations", """
Definition alias := Contracts.entry.
Instance original : ZesuEntryIntro Contracts.entry True := proof.
Instance distinct_key : ZesuEntryIntro alias Other := proof.
""")
        self.write_manifest()
        self.assertEqual(check_data_only_lemmas.violations(self.root), [])

    def test_alias_chains_resolve_to_one_canonical_key(self):
        self.add_file("registrations", """
Definition alias := Contracts.entry.
Definition alias2 := alias.
Instance original : ZesuEntryIntro Contracts.entry True := proof.
Instance duplicate : ZesuEntryIntro alias2 Other := proof.
""")
        self.manifest["aliases"] = {
            "alias2": "ZesuSsz.Evidence.registrations.alias",
            "alias": "Contracts.entry"}
        self.write_manifest()
        self.assertIn("Duplicate ZesuEntryIntro", check_data_only_lemmas.violations(self.root)[0])

    def test_alias_cycles_and_unresolved_targets_fail(self):
        self.add_file("registrations", """
Definition alias := Contracts.entry.
Instance first : ZesuEntryIntro alias True := proof.
""")
        for target, expected in [
                ("ZesuSsz.Evidence.registrations.alias", "cycle"),
                ("Contracts.missing", "unresolved registration key: Contracts.missing")]:
            with self.subTest(target=target):
                self.manifest["aliases"] = {"alias": target}
                self.write_manifest()
                self.assertIn(expected, check_data_only_lemmas.violations(self.root)[0])

    def test_invalid_alias_metadata_fails(self):
        for aliases in [[], {"alias": "entry"}, {"alias": None}, {"": "Contracts.entry"}]:
            with self.subTest(aliases=aliases):
                self.manifest["aliases"] = aliases
                self.write_manifest()
                self.assertTrue(check_data_only_lemmas.violations(self.root))

    def test_conflicting_manifest_aliases_fail(self):
        self.manifest["aliases"] = {"alias": "Contracts.entry"}
        self.write_manifest("first")
        self.manifest["aliases"] = {"alias": "Contracts.Entry"}
        self.write_manifest("second")
        self.assertIn("disagree", check_data_only_lemmas.violations(self.root)[0])

    def test_unlisted_import_cannot_resolve_a_registration_key(self):
        (self.root / "Unlisted.v").write_text("Definition other := resource.")
        self.add_file("registrations", """
Require Import Unlisted.
Instance first : ZesuEntryIntro other True := proof.
""")
        self.write_manifest()
        self.assertIn("unresolved registration key: other",
                      check_data_only_lemmas.violations(self.root)[0])

    def test_unused_alias_still_requires_a_declared_source_and_target(self):
        for aliases, expected in [
                ({"missing": "Contracts.entry"}, "missing"),
                ({"Contracts.Entry": "Contracts.missing"}, "Contracts.missing")]:
            with self.subTest(aliases=aliases):
                self.manifest["aliases"] = aliases
                self.write_manifest()
                self.assertIn("unresolved registration key: " + expected,
                              check_data_only_lemmas.violations(self.root)[0])

    def test_ambiguous_short_alias_name_requires_qualification(self):
        self.manifest["aliases"] = {"entry": "Contracts.Entry"}
        self.write_manifest()
        self.assertIn("unresolved registration key: entry",
                      check_data_only_lemmas.violations(self.root)[0])


if __name__ == "__main__":
    unittest.main()
