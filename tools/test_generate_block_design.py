"""Check word-derived edges and source-bound per-function profiles."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import test_block_table

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generic_block_design", ROOT / "ZesuSsz/Evidence/generate_block_design.py")
generator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(generator)


class FunctionDesignTests(unittest.TestCase):
    def test_check_ignores_only_the_top_level_producer_hash(self):
        baseline = json.dumps({"hashes": {"generator_sha256": "a" * 64,
                                        "source_sha256": "c" * 64},
                               "blocks": [{"binders": ["args"],
                                           "resource_alternative": "Entries.literal"}]}, indent=2) + "\n"
        changed = baseline.replace("a" * 64, "b" * 64)
        self.assertEqual(generator.checked_design_text(baseline), generator.checked_design_text(changed))
        for old, new in [("c" * 64, "d" * 64), ("args", "other"),
                         ("Entries.literal", "Entries.shortString"), ('  "blocks"', '    "blocks"')]:
            with self.subTest(change=old):
                self.assertNotEqual(generator.checked_design_text(baseline),
                                    generator.checked_design_text(changed.replace(old, new)))

    def test_check_rejects_invalid_or_duplicate_producer_hashes(self):
        for text in ['{"hashes":{"generator_sha256":"short"}}',
                     '{"hashes":{"generator_sha256":"' + "a" * 64 +
                     '","generator_sha256":"' + "b" * 64 + '"}}']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                generator.checked_design_text(text)

    def test_cli_check_preserves_newline_bytes_and_accepts_only_the_hash_change(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile, output = (root / name for name in ("inventory.json", "profile.json", "design.json"))
            inventory.write_text("{}")
            profile.write_text("{}")
            expected = {"hashes": {"generator_sha256": "a" * 64}, "blocks": []}
            rendered = json.dumps(expected, indent=2) + "\n"
            command = ["generate_block_design.py", "--function", "fixture", "--inventory", str(inventory),
                       "--profile", str(profile), "--output", str(output), "--check"]
            output.write_bytes(rendered.replace("a" * 64, "b" * 64).encode())
            with patch.object(generator.sys, "argv", command), patch.object(generator, "build", return_value=expected):
                generator.main()
                output.write_bytes(rendered.replace("\n", "\r\n").encode())
                with self.assertRaisesRegex(SystemExit, "stale"):
                    generator.main()

    def fixture(self, root):
        design, _ = test_block_table.BlockTableTests().executable_fixture()
        inventory, _ = test_block_table.BlockTableTests().fixture()
        function = inventory["functions"][0]
        function.update(instruction_count=3, block_count=3, branch_count=1,
                        loops=[], loop_count=0)
        for row in function["rows"]:
            row.update(rs1=(row["word"] >> 15) & 31, rs2=(row["word"] >> 20) & 31,
                       rd=(row["word"] >> 7) & 31)
            row["mnemonic"] = "beq" if row["kind"] == "branch" else "jalr"
        elf = root / "build/stock-zisk/zesu-zisk.elf"
        elf.parent.mkdir(parents=True)
        elf.write_bytes(b"selected synthetic ELF")
        inventory["elf_sha256"] = hashlib.sha256(elf.read_bytes()).hexdigest()
        source = root / "Contracts/Fixture.v"
        source.parent.mkdir()
        source.write_text("\n".join(
            f"Definition entry{pc:x} (args : FixtureArgs) (frameBytes : list byte) : iProp Sigma := True%I."
            for pc in (0x1000, 0x1004, 0x1008)))
        code = root / "Contracts/Code.v"
        code.write_text("Definition fixtureCode : iProp Sigma := True%I.\n")
        for row in design["blocks"]:
            pc = int(row["entry_pc"], 0)
            row.update(entry_definition=f"Contracts.Fixture.entry{pc:x}",
                       resource_predicate=f"Contracts.Fixture.entry{pc:x}",
                       source_hashes={"Contracts/Fixture.v": "refresh"})
        return inventory, {"function": "fixture", "design": design,
                           "hash_sources": {"selected_elf_sha256": "build/stock-zisk/zesu-zisk.elf"}}

    def test_words_override_stale_displacement_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            inventory["functions"][0]["rows"][0]["imm"] = 99
            design = generator.build(inventory, "fixture", profile, root=root)
            edges = design["blocks"][1]["incoming_edges"]
            self.assertEqual(edges[0]["from_instruction"], "0x00001000")
            self.assertEqual(edges[0]["path_condition"], {"op": "ne", "left": "0", "right": "0"})
            self.assertEqual(design["blocks"][0]["successor_pcs"], ["0x00001008", "0x00001004"])

    def support_fixture(self, root):
        inventory, profile = self.fixture(root)
        source = root / "Contracts/Fixture.v"
        source.write_text(source.read_text() +
                          "\nDefinition base (args : FixtureArgs) (frameBytes : list byte) : iProp Sigma := True%I.\n" +
                          "Definition continuationAt (args : FixtureArgs) : iProp Sigma := True%I.\n")
        row = profile["design"]["blocks"][0]
        row["support"] = {
            "version": 1, "existentials": [],
            "components": [{"kind": "base", "predicate": "Contracts.Fixture.base",
                            "arguments": ["args", "frameBytes"], "memory_deltas": []}],
            "loop": None, "additional_definitions": [],
            "continuation": {"mode": "included_in_base", "component_index": 0,
                             "predicate": "Contracts.Fixture.continuationAt",
                             "arguments": ["args"], "order": "resources_first"}}
        profile["design"]["support"] = {
            "version": 1, "entries_imports": [], "entries_scopes": [],
            "registrations_imports": [], "unfold_entries": ["entry1000"],
            "introductions": [], "hint_umbrella": [], "scoped_imports": [], "facts": []}
        return inventory, profile

    def test_mixed_design_keeps_legacy_binding_validation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            design = generator.build(inventory, "fixture", profile, root=root)
            self.assertEqual(len(design["blocks"]), 3)
            source = root / "Contracts/Fixture.v"
            source.write_text(source.read_text().replace("Definition entry1004", "Definition missing1004"))
            with self.assertRaisesRegex(ValueError, "source bindings"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_generation_without_old_entry_or_outputs_then_binds_fresh_output(self):
        import render_support
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            source = root / "Contracts/Fixture.v"
            source.write_text("\n".join(line for line in source.read_text().splitlines()
                                      if not line.startswith("Definition entry1000")))
            original = deepcopy(profile)
            design = generator.build(inventory, "fixture", profile, root=root)
            outputs = render_support.render_support(design, root, name_prefix="fixture")
            for path, text in outputs.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(text)
            bindings = generator.verify_rendered_entries(design, root, name_prefix="fixture")
            self.assertEqual(len(bindings), 1)
            self.assertEqual(bindings[0]["entry_definition"],
                             "ZesuSsz.Generated.Fixture.Entries.entry1000")
            self.assertEqual(profile, original)
            self.assertNotIn("ZesuSsz/Generated/Fixture/Entries.v", design["blocks"][0]["source_hashes"])
            generated = root / "ZesuSsz/Generated/Fixture/Entries.v"
            generated.write_text(generated.read_text().replace(" (frameBytes : list byte)", ""))
            with self.assertRaisesRegex(ValueError, "argument count"):
                generator.verify_rendered_entries(design, root, name_prefix="fixture")

    def test_supported_input_hash_tampering_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            design = generator.build(inventory, "fixture", profile, root=root)
            design["blocks"][0]["source_hashes"]["Contracts/Fixture.v"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "source hash changed"):
                generator.validate_resources(design, root, "fixture")

    def test_post_render_binding_includes_body_aliases(self):
        import render_support
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            design = generator.build(inventory, "fixture", profile, root=root)
            body = deepcopy(design["blocks"][0])
            body.update(entry_definition="Contracts.Fixture.body1000",
                        resource_predicate="Contracts.Fixture.body1000")
            design["blocks"].append(body)
            design["support"]["unfold_entries"].append("body1000")
            for path, text in render_support.render_support(design, root, name_prefix="fixture").items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(text)
            bindings = generator.verify_rendered_entries(design, root, name_prefix="fixture")
            self.assertEqual([row["entry_definition"] for row in bindings], [
                "ZesuSsz.Generated.Fixture.Entries.entry1000",
                "ZesuSsz.Generated.Fixture.Entries.body1000"])

    def test_nested_body_binding_preserves_cfg_and_checks_parameters(self):
        import render_support
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            primary = profile["design"]["blocks"][0]
            body = deepcopy(primary)
            body.update(entry_definition="Contracts.Fixture.body1000",
                        resource_predicate="Contracts.Fixture.body1000")
            primary["support"]["additional_definitions"] = [
                {"position": "after", "declaration": body}]
            profile["design"]["support"]["unfold_entries"].append("body1000")
            design = generator.build(inventory, "fixture", profile, root=root)
            self.assertEqual(len(design["blocks"]), 3)
            for path, text in render_support.render_support(design, root, name_prefix="fixture").items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_text(text)
            bindings = generator.verify_rendered_entries(design, root, name_prefix="fixture")
            self.assertEqual(len(bindings), 2)
            self.assertTrue(bindings[1]["entry_definition"].endswith(".body1000"))
            output = root / "ZesuSsz/Generated/Fixture/Entries.v"
            prefix, body_text = output.read_text().split("Definition body1000", 1)
            output.write_text(prefix + "Definition body1000" +
                              body_text.replace(" (frameBytes : list byte)", "", 1))
            with self.assertRaisesRegex(ValueError, "argument count"):
                generator.verify_rendered_entries(design, root, name_prefix="fixture")
            body["binders"][1]["name"] = "args"
            with self.assertRaisesRegex(ValueError, "binder"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_shared_source_hashes_refresh_without_output_prerequisites(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            profile["design"]["support"]["source_hashes"] = {"Contracts/Fixture.v": "refresh"}
            design = generator.build(inventory, "fixture", profile, root=root)
            self.assertEqual(design["support"]["source_hashes"], {
                "Contracts/Fixture.v": generator.digest(root / "Contracts/Fixture.v")})
            profile["design"]["support"]["source_hashes"] = {
                "ZesuSsz/Generated/Fixture/Registrations.v": "refresh"}
            with self.assertRaisesRegex(ValueError, "generated output"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_malformed_support_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            profile["design"]["blocks"][0]["support"]["version"] = 2
            with self.assertRaisesRegex(ValueError, "version"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_generated_output_cannot_be_an_input_prerequisite(self):
        cases = [(location, filename)
                 for location in ("row", "global", "shared", "bootstrap")
                 for filename in ("Entries.v", "Registrations.v", "BootstrapRegistrations.v")]
        for location, filename in cases:
            with self.subTest(location=location, output=filename), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inventory, profile = self.support_fixture(root)
                output = "ZesuSsz/Generated/Fixture/" + filename
                if location == "row":
                    profile["design"]["blocks"][0]["source_hashes"][output] = "0" * 64
                elif location == "global":
                    profile["hash_sources"]["output"] = output
                elif location == "shared":
                    profile["design"]["support"]["source_hashes"] = {output: "refresh"}
                else:
                    profile["design"]["support"]["bootstrap"] = {"source_hashes": {output: "refresh"}}
                with self.assertRaisesRegex(ValueError, "generated output"):
                    generator.build(inventory, "fixture", profile, root=root)

    def test_bootstrap_sources_refresh_independently_without_outputs(self):
        import render_support
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.support_fixture(root)
            source = root / "Contracts/Retained.v"
            source.write_text("Definition retained : Prop := True.\n")
            profile["design"]["support"]["bootstrap"] = {
                "imports": [{"mode": "import", "module": "isla.automation"},
                            {"mode": "import", "module": "Contracts.Retained"}],
                "source_hashes": {"Contracts/Retained.v": "refresh"},
                "unfold_sources": ["Contracts.Retained.retained"],
                "regcol_unfold_sources": []}
            design = generator.build(inventory, "fixture", profile, root=root)
            self.assertEqual(design["support"]["bootstrap"]["source_hashes"], {
                "Contracts/Retained.v": generator.digest(source)})
            outputs = render_support.render_support(design, root, name_prefix="fixture")
            self.assertIn(Path("ZesuSsz/Generated/Fixture/BootstrapRegistrations.v"), outputs)
            self.assertFalse((root / "ZesuSsz/Generated").exists())

    def test_profile_binders_and_alternatives_remain_exact(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            edge = profile["design"]["blocks"][1]["incoming_edges"][0]
            edge["from_block"] = "0x00001000"
            edge["from_instruction"] = "0x00001000"
            edge["resource_alternative"] = "Contracts.Fixture.entry1004"
            design = generator.build(inventory, "fixture", profile, root=root)
            self.assertEqual(design["blocks"][1]["binders"], profile["design"]["blocks"][1]["binders"])
            self.assertEqual(design["blocks"][1]["incoming_edges"][0]["resource_alternative"],
                             "Contracts.Fixture.entry1004")

    def test_profile_needs_no_copy_of_derived_edges_or_hashes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            expected = generator.build(inventory, "fixture", profile, root=root)
            profile["design"]["hashes"] = {}
            profile["design"]["table_convention"]["code_source_hashes"] = list(
                profile["design"]["table_convention"]["code_source_hashes"])
            for row in profile["design"]["blocks"]:
                row.update(end_pc_exclusive=None, incoming_edges=[], successor_pcs=[])
                row["source_hashes"] = list(row["source_hashes"])
            self.assertEqual(generator.build(inventory, "fixture", profile, root=root), expected)

    def test_missing_edge_and_duplicate_profile_block_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            duplicate = deepcopy(profile)
            duplicate["design"]["blocks"].append(deepcopy(duplicate["design"]["blocks"][0]))
            with self.assertRaisesRegex(ValueError, "exactly once"):
                generator.build(inventory, "fixture", duplicate, root=root)
            profile["design"]["blocks"][1]["incoming_edges"][0].update(
                from_instruction="0x2000", resource_alternative="Contracts.Fixture.entry1004")
            with self.assertRaisesRegex(ValueError, "absent incoming edge"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_profile_cannot_change_the_selected_function(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            profile["function"] = "other"
            with self.assertRaisesRegex(ValueError, "different functions"):
                generator.build(inventory, "fixture", profile, root=root)

    def test_instruction_whitelist_covers_the_released_extensions(self):
        no_reads = ("lui", "auipc")
        one_read = ("xori", "sltiu", "lhu", "csrrs")
        two_reads = ("sltu", "sub", "sll", "and")
        for mnemonic in no_reads + one_read + two_reads:
            with self.subTest(mnemonic=mnemonic):
                expected = set() if mnemonic in no_reads else {1} if mnemonic in one_read else {1, 2}
                self.assertEqual(generator.register_reads({"mnemonic": mnemonic, "rs1": 1, "rs2": 2}), expected)
        with self.assertRaisesRegex(ValueError, "Unsupported selected instruction"):
            generator.register_reads({"mnemonic": "unknown"})

    def test_source_paths_and_argument_counts_remain_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = self.fixture(root)
            profile["design"]["blocks"][0]["arguments"].pop()
            with self.assertRaisesRegex(ValueError, "argument count"):
                generator.build(inventory, "fixture", profile, root=root)
            with self.assertRaisesRegex(ValueError, "inside the workspace"):
                generator.source_hashes(["../outside.v"], root)


class CompactInputTests(unittest.TestCase):
    def test_shared_metadata_preserves_nested_bodies_and_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            expected = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            body = author["bodies"][0]
            fields = {key: body.pop(key) for key in ("lets", "existentials", "loop", "continuation") if key in body}
            author["shared"]["metadata_profiles"] = {"selected": fields}
            body["metadata_profile"] = "selected"
            original = deepcopy(author)
            self.assertEqual(generator.construct_profile(inventory, "fixture", author,
                root=root, source_closure=closure), expected)
            self.assertEqual(author, original)
            nested = {"components": [], "metadata_profile": "selected"}
            body["additional_definitions"] = [{"body": nested}]
            expanded = generator._compact_metadata_bodies(author)
            self.assertEqual(expanded[0]["additional_definitions"][0]["body"], {"components": [], **fields})

    def test_shared_metadata_preserves_missing_and_empty_values(self):
        author = {"shared": {"metadata_profiles": {
            "missing": {}, "empty": {"lets": [], "continuation": None}}},
            "bodies": [{"metadata_profile": "missing"}, {"metadata_profile": "empty"}]}
        self.assertEqual(generator._compact_metadata_bodies(author), [{}, {"lets": [], "continuation": None}])

    def test_shared_metadata_rejects_unknown_recursive_conflicting_and_resource_fields(self):
        for change in ("unknown", "recursive", "conflict", "resource", "record_type"):
            with self.subTest(change=change):
                author = {"shared": {"metadata_profiles": {"selected": {"lets": []}}},
                          "bodies": [{"metadata_profile": "selected"}]}
                if change == "unknown":
                    author["bodies"][0]["metadata_profile"] = "absent"
                elif change == "recursive":
                    author["shared"]["metadata_profiles"]["selected"]["metadata_profile"] = "selected"
                elif change == "conflict":
                    author["bodies"][0]["lets"] = []
                elif change == "resource":
                    author["shared"]["metadata_profiles"]["selected"]["components"] = []
                else:
                    author["shared"]["metadata_profiles"] = []
                with self.assertRaises(ValueError):
                    generator._compact_metadata_bodies(author)

    def test_annotations_keep_choices_explicit_and_derive_the_entry_reference(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            author["shared"]["annotation_defaults"] = {
                "needed_resources": {"input": "owned input", "stack": "saved stack"},
                "rocq_entry": {"kind": "constructed_declaration_ref", "role": "entry", "namespace": "generated"}}
            author["bodies"][0]["annotations"] = {
                "entry_class": "function_entry", "needed_resources": {"stack": "initial stack"},
                "branch_constant_facts": {"x4": 17}}
            author["bodies"][1]["annotations"] = {
                "return_clause": {"contract": "public result", "cases": [{"result": "accepted"}]}}
            original = deepcopy(author)
            result = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            first, second, third = result["design"]["blocks"]
            self.assertEqual(first["entry_class"], "function_entry")
            self.assertEqual(first["needed_resources"]["input"], "owned input")
            self.assertEqual(first["needed_resources"]["stack"], "initial stack")
            self.assertEqual(first["needed_resources"]["rocq_entry"],
                             "ZesuSsz.Generated.Fixture.Entries.fixtureEntryAt00001000")
            self.assertEqual(first["branch_constant_facts"], {"x4": 17})
            self.assertEqual(second["return_clause"], {"return_instruction_pc": "0x00001004",
                             "contract": "public result", "cases": [{"result": "accepted"}]})
            self.assertNotIn("branch_constant_facts", third)
            self.assertEqual(author, original)
            author["bodies"][0]["annotations"]["needed_resources"]["rocq_entry"] = "copied.reference"
            with self.assertRaisesRegex(ValueError, "resource descriptions"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_incoming_variant_selection_requires_one_real_edge_and_role(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            body = author["bodies"][1]
            body["additional_definitions"] = [{"position": "before", "role": "entry_variant", "suffix": "Small",
                "handwritten_owner": "Contracts.Fixture", "body": {"source_policy": "resource", "components": [
                    {"kind": "pure", "predicate": "predicate params payload"}]}}]
            author["shared"]["source_policies"] = {"resource": ["Contracts/Fixture.v"]}
            selection = {"from_block": author["bodies"][0]["at"], "declaration": {
                "kind": "local_declaration_ref", "role": "entry_variant", "suffix": "Small", "namespace": "handwritten"}}
            body["annotations"] = {"incoming_edge_variants": [selection]}
            result = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            self.assertEqual(result["design"]["blocks"][1]["incoming_edges"][0]["resource_alternative"],
                             "Contracts.Fixture.fixtureEntryAt00001004Small")
            for change in [{"from_block": "caller"}, {"declaration": dict(selection["declaration"], suffix="Absent")}]:
                body["annotations"]["incoming_edge_variants"] = [{**selection, **change}]
                with self.subTest(change=change), self.assertRaisesRegex(ValueError, "incoming edge"):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            body["annotations"]["incoming_edge_variants"] = [selection, deepcopy(selection)]
            with self.assertRaisesRegex(ValueError, "duplicate"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_resource_component_derives_the_loop_application_and_refuses_copies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            body = author["bodies"][0]
            body["components"] = [{"kind": "base", "predicate": "predicate", "arguments": ["params", "payload"],
                                   "memory_deltas": []}]
            body["loop"] = {"invariant": {"resource_component": 0}}
            result = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            self.assertEqual(result["design"]["blocks"][0]["support"]["loop"]["invariant"],
                             {"component_index": 0, "predicate": "predicate", "arguments": ["params", "payload"]})
            for invariant in [{"resource_component": True}, {"resource_component": 1},
                              {"resource_component": 0, "predicate": "copied"}]:
                body["loop"]["invariant"] = invariant
                with self.subTest(invariant=invariant), self.assertRaisesRegex(ValueError, "loop invariant"):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_introduction_order_rejects_unknown_duplicate_or_incomplete_selections(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            for selectors in [[author["bodies"][0]["at"]], ["unknown"], ["unknown", "unknown"]]:
                author["shared"]["selection_order"] = {"introductions": selectors}
                with self.subTest(selectors=selectors), self.assertRaisesRegex(ValueError, "introduction order"):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def compact_fixture(self, root):
        inventory, _ = FunctionDesignTests().fixture(root)
        source = root / "Contracts/Fixture.v"
        source.write_text("Definition predicate := True.\n")
        (root / "inventory.json").write_text(json.dumps(inventory))
        author = {
            "schema": "p1b.compact-profile.v1",
            "function": {"inventory_name": "fixture", "prefix": "fixture",
                         "root": {"name": "params", "type": "FixtureArgs"},
                         "handwritten_owner": "Contracts.Fixture",
                         "register_policy": "decoded_function_accessed_gprs",
                         "profile_layout": "expanded_cfg"},
            "symbols": [{"name": "payload", "type": "list byte"},
                        {"name": "unused", "type": "nat"}],
            "shared": {"design_metadata": {}, "support_metadata": {"entries_imports": [
                       {"mode": "import", "module": "Contracts.Fixture"}]},
                       "row_source_paths": ["Contracts/Fixture.v"],
                       "input_digest_sources": {"inventory_sha256": "inventory.json"}, "lets": [],
                       "continuation": {"mode": "none"},
                       "loop_annotations": [], "historical_design_metadata": {}},
            "bodies": [{"at": generator.address(block["start"]), "components": [
                {"kind": "pure", "predicate": "predicate params payload"}]}
                for block in inventory["functions"][0]["blocks"]]}
        closure = {"sources": {"Contracts.Fixture": {
            "path": str(source), "sha256": generator.digest(source)}}}
        return inventory, author, closure

    def test_compact_schema_derives_support_version_and_rejects_copies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            original = deepcopy(author)
            profile = generator.construct_profile(inventory, "fixture", author, root=root,
                                                  source_closure=closure)
            self.assertEqual(profile["design"]["support"]["version"], 1)
            self.assertEqual(author, original)
            for version in [1, 2, None]:
                author["shared"]["support_metadata"]["version"] = version
                with self.subTest(version=version), self.assertRaisesRegex(ValueError, "copied version"):
                    generator.construct_profile(inventory, "fixture", author, root=root,
                                                source_closure=closure)
            author = deepcopy(original)
            author["schema"] = "p1b.compact-profile.unknown"
            with self.assertRaisesRegex(ValueError, "schema is unsupported"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_constructor_builds_ordered_imports_and_bootstrap_from_bound_choices(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            shared = author["shared"]
            shared["support_metadata"].pop("entries_imports")
            shared["import_choices"] = {"entries_imports": ["Contracts.Fixture"],
                                        "registrations_imports": [{"module": "Contracts.Fixture", "mode": "export"}]}
            shared["bootstrap_choices"] = [{"unfold": "Contracts.Fixture.predicate"},
                                           {"regcol": "Contracts.Fixture.predicate"}]
            closure["sources"]["isla.automation"] = deepcopy(closure["sources"]["Contracts.Fixture"])
            original = deepcopy(author)
            profile = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            self.assertEqual(author, original)
            support = profile["design"]["support"]
            self.assertEqual(support["entries_imports"], [{"module": "Contracts.Fixture", "mode": "import"}])
            self.assertEqual(support["registrations_imports"][0]["mode"], "export")
            self.assertEqual(support["bootstrap"], {
                "imports": [{"module": "isla.automation", "mode": "import"},
                            {"module": "Contracts.Fixture", "mode": "import"}],
                "source_hashes": {"Contracts/Fixture.v": generator.digest(root / "Contracts/Fixture.v")},
                "unfold_sources": ["Contracts.Fixture.predicate"],
                "regcol_unfold_sources": ["Contracts.Fixture.predicate"]})

    def test_bootstrap_imports_follow_first_source_use_across_roles(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            second = root / "Contracts/Second.v"
            second.write_text("Definition another := True.\nDefinition third := True.\n")
            closure["sources"]["Contracts.Second"] = {
                "path": str(second), "sha256": generator.digest(second)}
            closure["sources"]["isla.automation"] = deepcopy(closure["sources"]["Contracts.Fixture"])
            author["shared"]["bootstrap_choices"] = [
                {"regcol": "Contracts.Second.another"},
                {"unfold": "Contracts.Fixture.predicate"},
                {"unfold": "Contracts.Second.third"}]
            profile = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            self.assertEqual(profile["design"]["support"]["bootstrap"]["imports"], [
                {"module": "isla.automation", "mode": "import"},
                {"module": "Contracts.Second", "mode": "import"},
                {"module": "Contracts.Fixture", "mode": "import"}])

    def test_bootstrap_refuses_copied_imports_or_missing_automation_binding(self):
        for copied in (False, True):
            with self.subTest(copied=copied), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inventory, author, closure = self.compact_fixture(root)
                author["shared"]["bootstrap_choices"] = [{"unfold": "Contracts.Fixture.predicate"}]
                if copied:
                    closure["sources"]["isla.automation"] = deepcopy(closure["sources"]["Contracts.Fixture"])
                    author["shared"]["support_metadata"]["bootstrap"] = {"imports": []}
                with self.assertRaises(ValueError):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_constructor_refuses_conflicting_or_unbound_registry_choices(self):
        cases = [
            {"import_choices": {"entries_imports": ["Contracts.Fixture"]}},
            {"import_choices": {"registrations_imports": ["Contracts.Unknown"]}},
            {"import_choices": {"registrations_imports": ["Contracts.Fixture", "Contracts.Fixture"]}},
            {"import_choices": {"registrations_imports": [{"module": "Contracts.Fixture", "mode": "guess"}]}},
            {"bootstrap_choices": [{}]},
            {"bootstrap_choices": [{"unfold": "Contracts.Fixture.unknown"}]},
            {"bootstrap_choices": [{"unfold": "Contracts.Fixture.predicate"}] * 2},
            {"bootstrap_choices": [{"unfold": "Contracts.Fixture.predicate", "regcol": "Contracts.Fixture.predicate"}]},
        ]
        for choices in cases:
            with self.subTest(choices=choices), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inventory, author, closure = self.compact_fixture(root)
                author["shared"].update(choices)
                closure["sources"]["isla.automation"] = deepcopy(closure["sources"]["Contracts.Fixture"])
                with self.assertRaises(ValueError):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_constructor_refuses_copied_bootstrap_fields_and_changed_source_bindings(self):
        for changed_source in (False, True):
            with self.subTest(changed_source=changed_source), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inventory, author, closure = self.compact_fixture(root)
                author["shared"]["bootstrap_choices"] = [{"unfold": "Contracts.Fixture.predicate"}]
                closure["sources"]["isla.automation"] = deepcopy(closure["sources"]["Contracts.Fixture"])
                if changed_source:
                    (root / "Contracts/Fixture.v").write_text("Definition predicate := False.\n")
                else:
                    author["shared"]["support_metadata"]["bootstrap"] = {"source_hashes": {}}
                with self.assertRaises(ValueError):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_constructor_derives_interfaces_without_entry_declarations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            original = deepcopy(author)
            profile = generator.construct_profile(inventory, "fixture", author,
                                                  root=root, source_closure=closure)
            self.assertEqual(author, original)
            self.assertEqual(profile["design"]["block_count"], 3)
            for row in profile["design"]["blocks"]:
                pc = int(row["entry_pc"], 0)
                expected = f"Contracts.Fixture.fixtureEntryAt{pc:08x}"
                self.assertEqual(row["entry_definition"], expected)
                self.assertEqual(row["resource_predicate"], expected)
                self.assertEqual(row["arguments"], ["params", "x1", "payload"])
                self.assertEqual(row["binders"], [
                    {"name": "params", "type": "FixtureArgs"},
                    {"name": "x1", "type": "bv 64"},
                    {"name": "payload", "type": "list byte"}])
            self.assertEqual(profile["design"]["blocks"][0]["incoming_edges"][0]["from_block"], "caller")
            self.assertFalse((root / "ZesuSsz/Generated").exists())

    def test_constructor_accepts_a_new_function_and_relocated_cfg(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            function = inventory["functions"][0]
            function["name"] = "new_package.unseen"
            function["entry"] += 0x2000
            function["end"] += 0x2000
            function["returns"] = [pc + 0x2000 for pc in function["returns"]]
            for row in function["rows"]:
                row["pc"] += 0x2000
                row["successors"] = [pc + 0x2000 for pc in row["successors"]]
            for block in function["blocks"]:
                block["start"] += 0x2000
                block["end"] += 0x2000
                block["successors"] = [pc + 0x2000 for pc in block["successors"]]
            author["function"].update(inventory_name=function["name"], prefix="unseen")
            for body, block in zip(author["bodies"], function["blocks"]):
                body["at"] = generator.address(block["start"])
            result = generator.construct_profile(inventory, "unseen", author,
                                                 root=root, source_closure=closure)["design"]
            self.assertEqual(result["entry_pc"], "0x00003000")
            self.assertEqual(result["blocks"][0]["entry_definition"],
                             "Contracts.Fixture.unseenEntryAt00003000")
            self.assertEqual(result["blocks"][0]["successor_pcs"], ["0x00003008", "0x00003004"])
            self.assertEqual(result["blocks"][1]["incoming_edges"][0]["from_instruction"], "0x00003000")
            self.assertEqual(result["blocks"][1]["return_clause"],
                             {"return_instruction_pc": "0x00003004"})

    def test_constructor_refuses_missing_duplicate_or_non_cfg_bodies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            invalid = []
            missing = deepcopy(author)
            missing["bodies"].pop()
            invalid.append(missing)
            duplicate = deepcopy(author)
            duplicate["bodies"].append(deepcopy(duplicate["bodies"][0]))
            invalid.append(duplicate)
            foreign = deepcopy(author)
            foreign["bodies"][0]["at"] = "0x00002000"
            invalid.append(foreign)
            for candidate in invalid:
                with self.subTest(bodies=candidate["bodies"]), self.assertRaisesRegex(ValueError, "exactly once"):
                    generator.construct_profile(inventory, "fixture", candidate,
                                                root=root, source_closure=closure)

    def test_constructor_derives_base_index_and_inventory_loop_header(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            function = inventory["functions"][0]
            header = function["blocks"][1]["start"]
            function["loops"] = [{"minimum_pc": generator.address(header), "backward_edges": []}]
            function["loop_count"] = 1
            author["shared"]["loop_annotations"] = [{"loop_index": 0, "annotation": {"kind": "text", "value": "loop"}}]
            source = root / "Contracts/Fixture.v"
            source.write_text(source.read_text() + "Definition caller := True.\n")
            closure["sources"]["Contracts.Fixture"]["sha256"] = generator.digest(source)
            author["shared"]["continuation"] = {"mode": "included_in_base", "predicate": "caller",
                                                   "arguments": ["params"], "order": "resources_first"}
            for body in author["bodies"]:
                body["components"].insert(0, {"kind": "true"})
                body["components"].append({"kind": "base", "predicate": "predicate", "arguments": ["params"], "memory_deltas": []})
            profile = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            for row in profile["design"]["blocks"]:
                self.assertEqual(row["support"]["continuation"]["component_index"], 2)
                if row["entry_pc"] == generator.address(header):
                    self.assertEqual(row["invariant_hint"], "loop")
                else:
                    self.assertNotIn("invariant_hint", row)
            author["bodies"][0]["components"].append({"kind": "base", "predicate": "predicate", "arguments": ["params"], "memory_deltas": []})
            with self.assertRaisesRegex(ValueError, "one matching resource component"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_register_policy_retains_exit_ownership(self):
        registers = generator.compact_registers({}, "rv64_integer_abi_owned_full")
        self.assertEqual(registers, [f"x{i}" for i in [1, 2, *range(5, 32)]])
        self.assertEqual(len(registers), 29)
        with self.assertRaisesRegex(ValueError, "register policy"):
            generator.compact_registers({}, "copied_per_pc")

    def test_accessed_register_policy_ignores_unused_encoding_fields(self):
        function = {"calls": [], "rows": [
            {"pc": 0x1000, "size": 4, "word": 0x00150513, "mnemonic": "addi",
             "rs1": 10, "rs2": 31, "rd": 10},
            {"pc": 0x1004, "size": 4, "word": 0x00008067, "mnemonic": "jalr",
             "rs1": 1, "rs2": 30, "rd": 0}]}
        self.assertEqual(generator.compact_registers(function, "decoded_function_accessed_gprs"),
                         ["x1", "x10"])

    def test_lexical_scope_preserves_outer_symbols(self):
        free = generator.compact_free_identifiers(
            "(exists result : NextUint64Return, nextResultBytes result = resultBytes) /\\ P params")
        self.assertEqual(free, {"NextUint64Return", "nextResultBytes", "resultBytes", "P", "params"})
        self.assertEqual(generator.compact_free_identifiers(
            "let args : NextUint64Call := nextUint64Base params in nextInputPointer args"),
            {"NextUint64Call", "nextUint64Base", "params", "nextInputPointer"})

    def test_comments_strings_and_scope_names_are_not_variables(self):
        self.assertEqual(generator.compact_free_identifiers(
            'P value (* nested (* hidden *) comment *) /\\ Q "not a variable"%string'),
            {"P", "Q", "value"})

    def test_binder_types_keep_their_own_scope(self):
        self.assertEqual(generator.compact_free_identifiers(
            "forall (value : T) (proof : Relation value), P proof outside"),
            {"T", "Relation", "P", "outside"})
        self.assertEqual(generator.compact_free_identifiers("fun (value : T) => F value"),
                         {"T", "F"})

    def test_unsupported_binders_and_shadowing_are_refused(self):
        for text in ["exists value, P value", "let '(a, b) := pair in a",
                     "match value with | C => True end", "fun value => P value"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                generator.compact_free_identifiers(text)
        for name in ["params", "resultBytes", "x1"]:
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "shadows"):
                generator.compact_free_identifiers(f"exists {name} : T, P {name}",
                                                   reserved={"params", "resultBytes", "x1"})

    def test_typed_references_keep_roles_and_reject_extra_keys(self):
        context = {"symbols": {"decoded": "list byte"}, "registers": ["x1", "x2"],
                   "globals": {"helper": {"Contracts.Resources.helper"}}}
        block = {"start": 0x1234}
        cases = [({"kind": "symbol_ref", "name": "decoded"}, "decoded"),
                 ({"kind": "gpr_group_ref", "policy": "function"}, ["x1", "x2"]),
                 ({"kind": "block_pc_ref", "format": "hex8"}, "0x00001234"),
                 ({"kind": "global_ref", "name": "helper", "owner": "Contracts.Resources",
                   "role": "handwritten_helper"}, "Contracts.Resources.helper")]
        for node, expected in cases:
            self.assertEqual(generator.compact_reference(node, context, block), expected)
            with self.assertRaises(ValueError):
                generator.compact_reference(dict(node, proof="exact I"), context, block)
        for node in [{"kind": "entry_ref", "role": "generated_entry"},
                     {"kind": "global_ref", "name": "helper", "owner": "Contracts.Resources",
                      "role": "legacy_entry"},
                     {"kind": "global_ref", "name": "helper", "owner": "Foreign.Resources",
                      "role": "handwritten_helper"}]:
            with self.assertRaises(ValueError):
                generator.compact_reference(node, context, block)

    def test_global_index_checks_source_and_glob_bindings(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Resources.v"
            path.write_text("Definition helper (value : nat) := value.\n"
                            'Notation Bits value := (helper value).\n'
                            'Infix "mod" := Nat.modulo : nat_scope.\n')
            closure = {"sources": {"Contracts.Resources": {
                "path": str(path), "sha256": generator.digest(path)}}}
            notations = {}
            index = generator.compact_global_index(closure, notation_owners=notations)
            self.assertEqual(index, {"helper": {"Contracts.Resources.helper"}})
            self.assertEqual(notations, {"Bits": {"Contracts.Resources.Bits"}, "mod": {"Contracts.Resources.mod"}})
            self.assertNotIn("value", index)
            path.write_text("Definition other := 0.\n")
            with self.assertRaisesRegex(ValueError, "binding changed"):
                generator.compact_global_index(closure)

    def test_notation_does_not_become_a_qualified_global(self):
        context = {"registers": ["x1"], "globals": {}, "notations": {"Bits": {"ISA.Bits"}}}
        group = {"kind": "register_resources", "registers": {"kind": "gpr_group_ref", "policy": "function"},
                 "value_constructor": "Bits"}
        self.assertEqual(generator._compact_expand(group, context, {}),
                         [{"kind": "register", "name": "x1", "value": "Bits x1"}])
        with self.assertRaisesRegex(ValueError, "bound declaration owner"):
            generator.compact_reference({"kind": "global_ref", "name": "Bits", "owner": "ISA",
                                         "role": "handwritten_helper"}, context, {})

    def test_ordered_free_references_keep_lexical_scope(self):
        self.assertEqual(generator.compact_free_identifiers(
            "pair (exists (n : T), P n) (Q y n)", ordered=True),
            ["pair", "T", "P", "Q", "y", "n"])
        self.assertEqual(generator.compact_free_identifiers(
            "(exists (n : T), P n) /\\ Q n", ordered=True), ["T", "P", "Q", "n"])

    def test_semantic_anchor_uses_effective_arguments_and_rejects_bad_deltas(self):
        base = {"kind": "base", "predicate": "Library.resource", "arguments": ["left", "right"],
                "memory_deltas": [{"argument_index": 0, "value": "right"},
                                  {"argument_index": 1, "value": "left"}]}
        support = {"components": [base], "existentials": []}
        context = {"selection": {"parameter_order": "semantic_anchor"},
                   "registers": ["x1", "x2"], "symbols": {"left": "T", "right": "T", "other": "U"}}
        binders = generator._compact_entry_binders({}, support, {"left", "right", "x2", "other"}, context)
        self.assertEqual([item["name"] for item in binders], ["right", "left", "x2", "other"])
        for deltas in [[{"argument_index": 2, "value": "left"}],
                       [{"argument_index": 0, "value": "left"}, {"argument_index": 0, "value": "right"}]]:
            with self.subTest(deltas=deltas), self.assertRaises(ValueError):
                generator._compact_anchor([dict(base, memory_deltas=deltas)])
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            generator._compact_anchor([base, deepcopy(base)])
        with self.assertRaisesRegex(ValueError, "supported unambiguous"):
            generator._compact_anchor([{"kind": "pure", "term": "P"}])

    def test_auxiliary_roles_derive_names_and_preserve_local_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            source = root / "Contracts/Fixture.v"
            source.write_text(source.read_text() + "Parameter LocalType : Type.\n")
            closure["sources"]["Contracts.Fixture"]["sha256"] = generator.digest(source)
            author["function"].update(parameter_order="semantic_anchor", register_policy="resource_free_gprs")
            author["shared"]["source_policies"] = {"body": ["Contracts/Fixture.v"]}
            for body in author["bodies"]:
                body["source_policy"] = "body"
                resource = {"components": [{"kind": "base", "predicate": "Contracts.Fixture.predicate",
                            "arguments": ["params", "payload"], "memory_deltas": []}],
                            "source_policy": "body", "existentials": [{"name": "unused", "type": "LocalType"}]}
                body["additional_definitions"] = [{"position": "before", "role": "entry_variant", "suffix": "Small",
                        "handwritten_owner": "Contracts.Fixture", "body": resource}]
                body["components"] = [{"kind": "disjunction", "alternatives": [{"kind": "application",
                    "predicate": {"kind": "local_declaration_ref", "role": "entry_variant", "suffix": "Small"},
                    "arguments": ["params", "payload"]}]}]
            profile = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            for row in profile["design"]["blocks"]:
                attached = row["support"]["additional_definitions"][0]["declaration"]
                self.assertEqual(attached["entry_definition"], row["entry_definition"] + "Small")
                self.assertNotIn("entry_pc", attached)
                self.assertEqual([item["name"] for item in attached["binders"]], ["params", "payload"])
                self.assertEqual(row["support"]["components"][0]["alternatives"][0]["predicate"],
                                 "ZesuSsz.Generated.Fixture.Entries." + attached["entry_definition"].rsplit(".", 1)[-1])
            author["bodies"][0]["additional_definitions"].append(deepcopy(author["bodies"][0]["additional_definitions"][0]))
            with self.assertRaisesRegex(ValueError, "repeats an auxiliary"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_implicit_prelude_and_scoped_infix_ownership(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {"Coq.Init.Prelude": "Require Export Coq.Init.Datatypes.\n",
                       "Coq.Init.Datatypes": "Inductive bool := true | false.\n",
                       "Library.Z": 'Infix "mod" := Z.modulo : Z_scope.\n',
                       "Library.Nat": 'Infix "mod" := Nat.modulo : nat_scope.\n'}
            closure = {"sources": {}}
            for module, text in sources.items():
                path = root / (module + ".v")
                path.write_text(text)
                closure["sources"][module] = {"path": str(path), "sha256": generator.digest(path)}
            visible = generator.compact_import_visibility(closure, {"entries_imports": [
                {"mode": "import", "module": "Library.Z"}, {"mode": "import", "module": "Library.Nat"}]})
            self.assertIn("Coq.Init.Datatypes", visible)
            notations, scopes = {}, {}
            index = generator.compact_global_index(closure, notation_owners=notations, notation_scopes=scopes)
            context = {"globals": index, "notations": notations, "notation_scopes": scopes,
                       "active_scopes": ["Z_scope"], "visible_modules": visible}
            self.assertEqual(generator._compact_global_candidates("false", context), {"Coq.Init.Datatypes.false"})
            self.assertEqual(generator._compact_global_candidates("mod", context), {"Library.Z.mod"})
            context["active_scopes"] = ["nat_scope"]
            self.assertEqual(generator._compact_global_candidates("mod", context), {"Library.Nat.mod"})
            self.assertEqual(generator.compact_free_identifiers(
                "({| payload := data; frame := bytes |} : RecordType)", ordered=True),
                ["data", "bytes", "RecordType"])
            with self.assertRaisesRegex(ValueError, "unsupported binder"):
                generator.compact_free_identifiers("∃ n : T, P n")

    def test_helper_summaries_bind_resources_and_exclude_continuations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Contracts/Resources.v"
            path.parent.mkdir()
            declaration = ('Definition resources := (∃ (a b : bv 64),\n'
                           '  "x3" ↦ᵣ RVal_Bits a ∗ "x4" ↦ᵣ RVal_Bits b)%I.')
            path.write_text(declaration + "\n")
            summary = {"schema": "p1b.resource-helper-summary.v1", "helper": {
                "kind": "global_ref", "owner": "Contracts.Resources", "name": "resources", "role": "handwritten_helper"},
                "source": {"path": "Contracts/Resources.v", "sha256": generator.digest(path),
                           "definition_sha256": hashlib.sha256(declaration.encode()).hexdigest(), "line_start": 1, "line_end": 2},
                "exposure": "top_level_spatial_existentials", "resource_existentials": [
                    {"name": name, "type": "bv 64", "register_resource": {
                        "kind": "register", "name": register, "value": "RVal_Bits " + name}}
                    for name, register in [("a", "x3"), ("b", "x4")]]}
            context = {"root": root, "globals": {"resources": {"Contracts.Resources.resources"}}, "shared": {
                "helper_summaries": {"schema": summary["schema"], "summaries": [summary]},
                "derived_table_metadata": {
                    "register_existentials": "primary_top_level_register_resources_and_helper_summaries",
                    "internal_existentials": "primary_loop_bodies_with_equal_ordered_existentials"}}}
            rows = [{"entry_pc": "0x00001000", "support": {"existentials": [], "loop": None,
                    "components": [{"kind": "application", "predicate": "Contracts.Resources.resources"},
                                   {"kind": "continuation", "predicate": "Contracts.Resources.resources"}]}},
                    {"entry_pc": "0x00001004", "support": {"existentials": [{"name": "loaded", "type": "bv 64"}],
                    "loop": {"count": "loaded"}, "components": [{"kind": "register", "value": "RVal_Bits loaded"}]}}]
            self.assertEqual(generator._compact_table_metadata(rows, context), {
                "register_existentials": {"0x00001000": ["a", "b"], "0x00001004": ["loaded"]},
                "internal_existentials": {"entry_pcs": ["0x00001004"], "binders": ["loaded"]}})
            summary["resource_existentials"][0]["register_resource"]["value"] = "RVal_Bits b"
            with self.assertRaisesRegex(ValueError, "changes its register resource"):
                generator._compact_table_metadata(rows, context)
            summary["resource_existentials"][0]["register_resource"]["value"] = "RVal_Bits a"
            summary["source"]["definition_sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "definition binding changed"):
                generator._compact_table_metadata(rows, context)

    def test_helper_source_role_preserves_bound_definition_and_refuses_invalid_bindings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Contracts/Resources.v"
            path.parent.mkdir()
            declaration = ('Definition resources : iProp Sigma := (∃ (a : bv 64),\n'
                           '  "x3" ↦ᵣ RVal_Bits a)%I.')
            path.write_text("(* retained header *)\n" + declaration + "\n")
            source = {"path": "Contracts/Resources.v", "sha256": generator.digest(path),
                      "definition_sha256": hashlib.sha256(declaration.encode()).hexdigest(),
                      "line_start": 2, "line_end": 3}
            summary = {"schema": "p1b.resource-helper-summary.v1", "helper": {
                "kind": "global_ref", "owner": "Contracts.Resources", "name": "resources",
                "role": "handwritten_helper"}, "source": source,
                "exposure": "top_level_spatial_existentials", "resource_existentials": [
                    {"name": "a", "type": "bv 64", "register_resource": {
                        "kind": "register", "name": "x3", "value": "RVal_Bits a"}}]}
            context = {"root": root, "globals": {"resources": {"Contracts.Resources.resources"}},
                       "shared": {"helper_summaries": {"schema": summary["schema"], "summaries": [summary]}},
                       "source_closure": {"sources": {"Contracts.Resources": {
                           "path": str(path), "sha256": generator.digest(path)}}}}
            expected = generator._compact_helper_summaries(context)
            summary.pop("source")
            summary["source_binding_role"] = "from_bound_definition"
            original = deepcopy(context)
            self.assertEqual(generator._compact_helper_summaries(context), expected)
            self.assertEqual(context, original)
            for change in ["copied", "unknown", "missing", "changed", "ambiguous", "no_closure"]:
                altered = deepcopy(original)
                item = altered["shared"]["helper_summaries"]["summaries"][0]
                if change == "copied":
                    item["source"] = source
                elif change == "unknown":
                    item["source_binding_role"] = "unknown"
                elif change == "missing":
                    altered["source_closure"]["sources"] = {}
                elif change == "changed":
                    path.write_text(declaration + "\n")
                elif change == "ambiguous":
                    path.write_text(declaration + "\n" + declaration + "\n")
                    altered["source_closure"]["sources"]["Contracts.Resources"]["sha256"] = generator.digest(path)
                else:
                    altered.pop("source_closure")
                with self.subTest(change=change), self.assertRaises(ValueError):
                    generator._compact_helper_summaries(altered)
                path.write_text("(* retained header *)\n" + declaration + "\n")

    def test_import_visibility_and_notation_choices_use_actual_entry_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = self.compact_fixture(root)
            sources = {
                "Library.Entry": "Require Export Library.Notations.\n",
                "Library.Notations": "Notation length := Datatypes.length.\n",
                "Hidden.Constants": "Definition length := 0.\nDefinition unavailable := 0.\n",
                "Other.Notations": "Notation length := Other.length.\n"}
            for module, text in sources.items():
                path = root / (module + ".v")
                path.write_text(text)
                closure["sources"][module] = {"path": str(path), "sha256": generator.digest(path)}
            imports = author["shared"]["support_metadata"]["entries_imports"]
            imports.append({"mode": "import", "module": "Library.Entry"})
            author["bodies"][0]["components"][0]["predicate"] += " (length payload)"
            context = generator.validate_author_data(author, inventory, "fixture", root=root,
                                                      source_closure=closure)
            self.assertIn("Library.Notations", context["visible_modules"])
            self.assertNotIn("Hidden.Constants", context["visible_modules"])
            self.assertEqual(generator._compact_global_candidates("length", context),
                             {"Library.Notations.length"})
            generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            author["bodies"][0]["components"][0]["predicate"] += " unavailable"
            with self.assertRaisesRegex(ValueError, "unresolved or ambiguous global: unavailable"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            author["bodies"][0]["components"][0]["predicate"] = "predicate params payload"
            choices = {"entries_imports": deepcopy(imports), "notations": {"length": {
                "owner": "Library.Notations",
                "source_sha256": closure["sources"]["Library.Notations"]["sha256"],
                "visible_candidates": ["Library.Notations.length"]}}}
            generator.validate_author_data(author, inventory, "fixture", root=root,
                                            source_closure=closure, notation_choices=choices)
            changed = deepcopy(choices)
            changed["notations"]["length"]["source_sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "source binding changed"):
                generator.validate_author_data(author, inventory, "fixture", root=root,
                                                source_closure=closure, notation_choices=changed)
            imports.append({"mode": "import", "module": "Other.Notations"})
            with self.assertRaisesRegex(ValueError, "import boundary changed"):
                generator.validate_author_data(author, inventory, "fixture", root=root,
                                                source_closure=closure, notation_choices=choices)
            choices["entries_imports"] = deepcopy(imports)
            with self.assertRaisesRegex(ValueError, "visible notation candidates changed"):
                generator.validate_author_data(author, inventory, "fixture", root=root,
                                                source_closure=closure, notation_choices=choices)
            choices["notations"]["length"]["visible_candidates"].append("Other.Notations.length")
            context = generator.validate_author_data(author, inventory, "fixture", root=root,
                                                      source_closure=closure, notation_choices=choices)
            self.assertEqual(generator._compact_global_candidates("length", context),
                             {"Library.Notations.length"})
            self.assertEqual(generator._compact_global_candidates("Library.Notations.length", context), set())

    def test_global_index_retains_nested_module_ownership(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Numbers.v"
            path.write_text("Module Pos.\nDefinition length := 0.\nEnd Pos.\nDefinition outer := 0.\n")
            closure = {"sources": {"Library.Numbers": {
                "path": str(path), "sha256": generator.digest(path)}}}
            self.assertEqual(generator.compact_global_index(closure), {
                "length": {"Library.Numbers.Pos.length"}, "outer": {"Library.Numbers.outer"}})

    def test_concat_preserves_text_and_rejects_vector_parts(self):
        context = {"symbols": {}, "registers": ["x1"]}
        block = {"start": 0x1234}
        node = {"kind": "concat", "parts": [
            {"kind": "text", "value": "(at "},
            {"kind": "block_pc_ref", "format": "hex8"},
            {"kind": "text", "value": ")"}]}
        self.assertEqual(generator.compact_reference(node, context, block), "(at 0x00001234)")
        for invalid in [dict(node, proof="exact I"), {"kind": "concat", "parts": []},
                        {"kind": "concat", "parts": [{"kind": "gpr_group_ref", "policy": "function"}]}]:
            with self.subTest(node=invalid), self.assertRaises(ValueError):
                generator.compact_reference(invalid, context, block)

    def test_register_resource_expansion_keeps_surrounding_components(self):
        context = {"registers": ["x1", "x8"], "globals": {"Bits": {"ISA.Bits"}}}
        group = {"kind": "register_resources", "registers": {"kind": "gpr_group_ref", "policy": "function"},
                 "value_constructor": "Bits"}
        components = [{"kind": "true"}, group, {"kind": "continuation", "predicate": "caller"}]
        self.assertEqual(generator._compact_expand(components, context, {}), [
            {"kind": "true"}, {"kind": "register", "name": "x1", "value": "Bits x1"},
            {"kind": "register", "name": "x8", "value": "Bits x8"},
            {"kind": "continuation", "predicate": "caller"}])
        for invalid in [dict(group, entry_binders=[]), dict(group, registers=["x1"]),
                        dict(group, value_constructor="Unknown")]:
            with self.subTest(node=invalid), self.assertRaises(ValueError):
                generator._compact_expand(invalid, context, {})

    def test_fact_statement_preserves_source_clauses_without_type_inference(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Facts.v"
            path.write_text("Lemma helper args (x y : Z) {items : list byte} :\n"
                            "  (P x -> Q y) -> R args items ->\n"
                            "  result args x y items.\nProof. exact I. Qed.\n")
            closure = {"sources": {"Library.Facts": {
                "path": str(path), "sha256": generator.digest(path)}}}
            result = generator.compact_helper_statement("Library.Facts.helper", closure)
            self.assertEqual(result["parameters"], [
                {"name": "args", "type": None, "implicit": False},
                {"name": "x", "type": "Z", "implicit": False},
                {"name": "y", "type": "Z", "implicit": False},
                {"name": "items", "type": "list byte", "implicit": True}])
            self.assertEqual(result["premises"], ["(P x -> Q y)", "R args items"])
            self.assertEqual(result["conclusion"], "result args x y items")

    def test_fact_statement_resolves_nested_declarations_exactly(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Facts.v"
            path.write_text("Module First.\nLemma helper (x : Z) : x = x.\n"
                            "End First.\nModule Second.\nLemma helper : True.\nEnd Second.\n")
            closure = {"sources": {"Library.Facts": {
                "path": str(path), "sha256": generator.digest(path)}}}
            result = generator.compact_helper_statement("Library.Facts.First.helper", closure)
            self.assertEqual(result["conclusion"], "x = x")
            self.assertEqual(generator.compact_helper_statement(
                "Library.Facts.Second.helper", closure)["conclusion"], "True")
            with self.assertRaisesRegex(ValueError, "one source lemma"):
                generator.compact_helper_statement("Library.Facts.helper", closure)
            path.write_text(path.read_text() + "(* changed *)")
            with self.assertRaisesRegex(ValueError, "differs from its binding"):
                generator.compact_helper_statement("Library.Facts.First.helper", closure)

    def test_fact_statement_rejects_generated_and_unsupported_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Facts.v"
            for statement in ["Lemma helper : forall x : Z, x = x.",
                              "Lemma helper (x : Z) x : True.",
                              "Lemma helper ( : Z) : True.",
                              "Definition helper := True."]:
                path.write_text(statement)
                closure = {"sources": {"Library.Facts": {
                    "path": str(path), "sha256": generator.digest(path)}}}
                with self.subTest(statement=statement), self.assertRaises(ValueError):
                    generator.compact_helper_statement("Library.Facts.helper", closure)
            path.write_text("Lemma helper : True.")
            closure = {"sources": {"Library.Generated.Facts": {
                "path": str(path), "sha256": generator.digest(path)}}}
            with self.assertRaisesRegex(ValueError, "generated"):
                generator.compact_helper_statement("Library.Generated.Facts.helper", closure)


class TypedAuthorTests(unittest.TestCase):
    def author(self, component):
        return {"schema": "p1b.compact-profile.v2", "bodies": [{"components": [component]}]}

    def fields(self):
        return [
            ({"predicate": {"owner": "Contracts.Resources", "name": "helper"}}, "predicate"),
            ({"predicate": {"suffix": "Loop"}}, "predicate"),
            ({"registers": {"policy": "function"}}, "registers"),
            ({"terms": [{"provenance": {"source": "selected"}, "term": {"value": " x  "}}]}, "provenance"),
            ({"terms": [{"provenance": {"from_block": "0x00001234", "from_instruction": "0x00001238"},
                         "term": {"value": "x"}}]}, "provenance"),
            ({"terms": [{"provenance": {"source": "selected"}, "term": {"value": "x"}}]}, "term"),
            ({"terms": [{"provenance": {"source": "selected"}, "term": {"parts": [
                {"kind": "text", "value": "(x "}, {"kind": "text", "value": ")"}]}}]}, "term")]

    def selected_field(self, author, selection):
        component = author["bodies"][0]["components"][0]
        return component[selection] if selection in {"predicate", "registers"} else component["terms"][0][selection]

    def test_each_shape_rejects_copied_mixed_missing_and_unknown_fields(self):
        for component, selection in self.fields():
            for mutation in ("copied_kind", "copied_role", "missing", "unknown", "mixed"):
                author = self.author(deepcopy(component))
                field = self.selected_field(author, selection)
                if mutation == "missing":
                    field.pop(next(iter(field)))
                elif mutation == "mixed":
                    if selection == "predicate":
                        field.update(owner="Contracts.Mixed", name="helper", suffix="Mixed")
                    elif selection == "provenance":
                        field.update(source="selected", from_block="0x00001234", from_instruction="0x00001238")
                    elif selection == "term":
                        field.update(value="x", parts=[{"kind": "text", "value": "x"}])
                    else:
                        field["name"] = "x1"
                else:
                    field[{"copied_kind": "kind", "copied_role": "role", "unknown": "unknown"}[mutation]] = "copied"
                with self.subTest(selection=selection, mutation=mutation), self.assertRaises(ValueError):
                    generator._compact_typed_author(author)

    def test_nested_resources_preserve_order_expression_bytes_and_unrelated_metadata(self):
        components = [deepcopy(component) for component, _ in self.fields()]
        author = self.author({"alternatives": components})
        author["shared"] = {"predicate": {"kind": "unchanged"}, "history": None}
        author["bodies"][0]["additional_definitions"] = [{"body": {"components": [
            {"predicate": {"suffix": "Auxiliary"}}]}}]
        original = deepcopy(author)
        expanded = generator._compact_typed_author(author)
        self.assertEqual(author, original)
        self.assertEqual(expanded["shared"], original["shared"])
        alternatives = expanded["bodies"][0]["components"][0]["alternatives"]
        self.assertEqual(alternatives[3]["terms"][0]["term"]["value"], " x  ")
        self.assertEqual(alternatives[6]["terms"][0]["term"]["parts"],
                         components[6]["terms"][0]["term"]["parts"])
        auxiliary = expanded["bodies"][0]["additional_definitions"][0]["body"]["components"][0]
        self.assertEqual(auxiliary["predicate"], {"kind": "local_declaration_ref", "role": "entry_variant", "suffix": "Auxiliary"})

    def test_v2_uses_existing_source_validation_and_preserves_v1_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = CompactInputTests().compact_fixture(root)
            for body in author["bodies"]:
                body["components"] = [{"kind": "pure", "predicate": {
                    "kind": "global_ref", "role": "handwritten_helper", "owner": "Contracts.Fixture", "name": "predicate"}}]
            expected = generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            author["schema"] = "p1b.compact-profile.v2"
            for body in author["bodies"]:
                del body["components"][0]["predicate"]["kind"]
                del body["components"][0]["predicate"]["role"]
            original = deepcopy(author)
            self.assertEqual(generator.construct_profile(inventory, "fixture", author,
                root=root, source_closure=closure), expected)
            self.assertEqual(author, original)
            author["bodies"][0]["components"][0]["predicate"]["owner"] = "Foreign.Resources"
            with self.assertRaisesRegex(ValueError, "bound declaration owner"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)
            author = deepcopy(original)
            (root / "Contracts/Fixture.v").write_text("Definition changed := True.\n")
            with self.assertRaisesRegex(ValueError, "binding changed"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_v2_rejects_unattached_local_variant(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = CompactInputTests().compact_fixture(root)
            author["schema"] = "p1b.compact-profile.v2"
            for body in author["bodies"]:
                body["components"] = [{"kind": "pure", "predicate": {"suffix": "Missing"}}]
            with self.assertRaisesRegex(ValueError, "no attached declaration role"):
                generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)

    def test_v2_rejects_unordered_or_malformed_resource_containers(self):
        for component in [None, {"terms": {}}, {"alternatives": {}}, {"terms": [{}]}, {"predicate": "copied"}]:
            with self.subTest(component=component), self.assertRaises(ValueError):
                generator._compact_typed_author(self.author(component))
        for auxiliary in [None, {}, [None], [{}]]:
            author = self.author({"kind": "true"})
            author["bodies"][0]["additional_definitions"] = auxiliary
            with self.subTest(auxiliary=auxiliary), self.assertRaises(ValueError):
                generator._compact_typed_author(author)

    def test_invalid_schema_containers_fail_without_a_type_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, author, closure = CompactInputTests().compact_fixture(root)
            for schema in [None, {}, []]:
                author["schema"] = schema
                with self.subTest(schema=schema), self.assertRaisesRegex(ValueError, "schema is unsupported"):
                    generator.construct_profile(inventory, "fixture", author, root=root, source_closure=closure)


class ContinuationProjectionTests(unittest.TestCase):
    def fixture(self, directory):
        source = Path(directory) / "Resources.v"
        definition = "Definition base (a b : Z) : Prop := (⌜ True ⌝ ∗ continuation a b ∗ True)%I.\n"
        source.write_text(definition + "Definition continuation (a b : Z) : Prop := final a b.\n"
                          "Definition final (a b : Z) : Prop := a = b.\n")
        summary = {"helper": "Library.base", "source": {"path": str(source), "sha256": generator.digest(source)},
            "definition": {"line_start": 1, "line_end": 1,
                "sha256": hashlib.sha256(definition.encode()).hexdigest()},
            "selected_application": {"callee": "Library.continuation", "require_unique": True},
            "explicit_alias_steps": ["Library.continuation"]}
        context = {"shared": {"continuation_summaries": {"Library.base": summary}},
            "source_closure": {"sources": {"Library": {"path": str(source), "sha256": generator.digest(source)}}},
            "globals": {"final": {"Library.final"}, "continuation": {"Library.continuation"}}}
        body = {"components": [{"kind": "base", "predicate": "Library.base", "arguments": ["left", "right"],
            "memory_deltas": [{"argument_index": 0, "value": "right"},
                              {"argument_index": 1, "value": "left"}]}]}
        selector = {"mode": "from_resource_component", "resource_component": 0,
            "placement": "included_in_base", "order": "resources_first", "helper_summary": "Library.base"}
        return context, body, selector, source

    def test_included_projection_applies_deltas_before_alias_substitution(self):
        with tempfile.TemporaryDirectory() as directory:
            context, body, selector, _ = self.fixture(directory)
            with unittest.mock.patch.object(generator, "_compact_expand", side_effect=lambda value, *_: value):
                result = generator._compact_continuation(selector, body, {}, context, {})
            self.assertEqual(result, {"mode": "included_in_base", "predicate": "Library.final",
                "arguments": ["right", "left"], "order": "resources_first", "component_index": 0})

    def test_bound_definition_role_preserves_projection(self):
        with tempfile.TemporaryDirectory() as directory:
            context, body, selector, _ = self.fixture(directory)
            with unittest.mock.patch.object(generator, "_compact_expand", side_effect=lambda value, *_: value):
                expected = generator._compact_continuation(selector, body, {}, context, {})
                summaries = context["shared"]["continuation_summaries"]
                summaries["Library.base"] = {key: value for key, value in summaries["Library.base"].items()
                    if key in {"selected_application", "explicit_alias_steps"}}
                summaries["Library.base"]["binding_role"] = "from_bound_definition"
                self.assertEqual(generator._compact_continuation(selector, body, {}, context, {}), expected)

    def test_bound_definition_role_rejects_copied_fields_changed_source_and_unknown_role(self):
        for change in ("helper", "source", "definition", "role", "bytes", "missing"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                context, body, selector, source = self.fixture(directory)
                summaries = context["shared"]["continuation_summaries"]
                old = summaries["Library.base"]
                summary = {"binding_role": "from_bound_definition", "selected_application": old["selected_application"],
                    "explicit_alias_steps": old["explicit_alias_steps"]}
                summaries["Library.base"] = summary
                if change in {"helper", "source", "definition"}:
                    summary[change] = old[change]
                elif change == "role":
                    summary["binding_role"] = "other"
                elif change == "bytes":
                    source.write_text(source.read_text() + "(* changed *)")
                else:
                    context["source_closure"]["sources"].clear()
                with unittest.mock.patch.object(generator, "_compact_expand", side_effect=lambda value, *_: value):
                    with self.assertRaises(ValueError):
                        generator._compact_continuation(selector, body, {}, context, {})

    def test_direct_projection_tracks_authored_origin_through_expansion(self):
        body = {"components": [{"kind": "register_resources"},
            {"kind": "continuation", "predicate": "Library.continuation", "arguments": ["left", "right"]}]}
        selector = {"mode": "from_resource_component", "resource_component": 1,
            "placement": "explicit", "order": "resources_first"}
        def expand(value, *_):
            return [{"kind": "register"}, {"kind": "register"}] if value["kind"] == "register_resources" else value
        with unittest.mock.patch.object(generator, "_compact_expand", side_effect=expand):
            result = generator._compact_continuation(selector, body, {}, {}, {})
        self.assertEqual(result["component_index"], 2)
        self.assertEqual(result["predicate"], "Library.continuation")

    def test_projection_rejects_changed_source_ambiguous_helpers_aliases_and_copied_outputs(self):
        for change in ("source", "ambiguous", "alias", "copied", "component", "arity", "binder", "shadow"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                context, body, selector, source = self.fixture(directory)
                summary = context["shared"]["continuation_summaries"]["Library.base"]
                if change == "source":
                    source.write_text(source.read_text() + "(* changed *)")
                elif change in {"ambiguous", "binder"}:
                    text = source.read_text()
                    text = text.replace("∗ True)%I", "∗ continuation a b)%I") if change == "ambiguous" else text.replace("(a b : Z)", "a b", 1)
                    source.write_text(text)
                    context["source_closure"]["sources"]["Library"]["sha256"] = generator.digest(source)
                    summary["source"]["sha256"] = generator.digest(source)
                    summary["definition"]["sha256"] = hashlib.sha256(text.splitlines(True)[0].encode()).hexdigest()
                elif change == "alias":
                    summary["explicit_alias_steps"].append("Library.continuation")
                elif change == "copied":
                    selector["predicate"] = "Library.final"
                elif change == "component":
                    selector["resource_component"] = True
                elif change == "shadow":
                    context["globals"]["continuation"].add("Other.continuation")
                else:
                    body["components"][0]["arguments"].append("extra")
                with unittest.mock.patch.object(generator, "_compact_expand", side_effect=lambda value, *_: value):
                    with self.assertRaises(ValueError):
                        generator._compact_continuation(selector, body, {}, context, {})


class FactChoiceTests(unittest.TestCase):
    def test_constructor_role_preserves_fact_records_and_rejects_overrides(self):
        with tempfile.TemporaryDirectory() as directory:
            shared, closure, evidence = self.fixture(directory)
            expected = deepcopy(shared)
            generator._compact_fact_choices(expected, closure, evidence)
            shared["registry_defaults"] = {key: shared["registry_defaults"][key]
                for key in ("locality", "priority", "explicit_lemma")}
            shared["registry_defaults"]["constructor_role"] = "simpl_and_true_fact"
            generator._compact_fact_choices(shared, closure, evidence)
            self.assertEqual(shared["support_metadata"], expected["support_metadata"])
        for change in ("unknown", "override", "missing"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.fixture(directory)
                defaults = {key: shared["registry_defaults"][key]
                    for key in ("locality", "priority", "explicit_lemma")}
                defaults["constructor_role"] = "simpl_and_true_fact"
                if change == "unknown":
                    defaults["constructor_role"] = "other"
                elif change == "override":
                    defaults["class"] = "OtherClass"
                else:
                    defaults.pop("priority")
                shared["registry_defaults"] = defaults
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)

    def fixture(self, directory):
        root = Path(directory)
        source = root / "Facts.v"
        source.write_text("Lemma helper args (n : Z) : P args -> Q n -> result args n.\n")
        closure = {"sources": {"Library.Facts": {
            "path": str(source), "sha256": generator.digest(source)}}}
        registry = "ZesuSsz.Automation.FactRegistry."
        shared = {"support_metadata": {}, "registry_defaults": {
            "locality": "export", "priority": None, "explicit_lemma": False,
            "class": "lithium.simpl_classes.SimplAnd", "class_arguments": ["conclusion", "True"],
            "constructor": registry + "zesu_simpl_and_fact",
            "constructor_application": "@" + registry + "zesu_simpl_and_fact conclusion helper_proof",
            "evidence_class": registry + "ZesuFactEvidence", "evidence_projection": registry + "zesu_fact_evidence",
            "evidence_application": "@" + registry + "zesu_fact_evidence premise_type evidence_binder"},
            "fact_choices": [{"helper": "Library.Facts.helper", "instance_name": "helperFact",
                "activation_premises": [{"name": "Hq", "source_premise": 1},
                                        {"name": "Hp", "source_premise": 0}]}]}

        def packet(name, value):
            path = root / name
            path.write_text(json.dumps(value))
            return {"path": str(path), "sha256": generator.digest(path)}

        printed = "Library.Args"
        key = hashlib.sha256(printed.encode()).hexdigest()
        text = packet("printed.json", {"retained": True})
        signatures = packet("signatures.json", {"query": text, "stdout": text, "signatures": [{
            "helper": "Library.Facts.helper", "source": closure["sources"]["Library.Facts"],
            "binders": [{"name": "args", "type": printed, "type_sha256": key},
                        {"name": "n", "type": "BinNums.Z",
                         "type_sha256": hashlib.sha256(b"BinNums.Z").hexdigest()}]}]})
        evidence = {"signature_packets": [signatures], "type_spellings": packet("types.json", {
            "shared_type_spellings": [{"printed_type": printed, "printed_type_sha256": key,
                                       "spelling": "Args"}]}),
            "spelling_choices": packet("spellings.json", [{"helper": "Library.Facts.helper",
                "spelling_choices": [{"field": "conclusion",
                    "source_clause_sha256": hashlib.sha256(b"result args n").hexdigest(),
                    "source_sha256": generator.digest(source), "spelling": "(result args n)"}]}])}
        return shared, closure, evidence

    def test_constructs_clauses_and_preserves_activation_and_argument_orders(self):
        with tempfile.TemporaryDirectory() as directory:
            shared, closure, evidence = self.fixture(directory)
            generator._compact_fact_choices(shared, closure, evidence)
            fact = shared["support_metadata"]["facts"][0]
            self.assertEqual(fact["parameters"], [
                {"name": "args", "type": "Args", "implicit": False},
                {"name": "n", "type": "Z", "implicit": False}])
            self.assertEqual([row["name"] for row in fact["premises"]], ["Hq", "Hp"])
            self.assertEqual([row["type"] for row in fact["premises"]], ["Q n", "P args"])
            self.assertEqual(fact["arguments"], ["args", "n",
                "@ZesuSsz.Automation.FactRegistry.zesu_fact_evidence _ Hp",
                "@ZesuSsz.Automation.FactRegistry.zesu_fact_evidence _ Hq"])
            self.assertEqual(fact["conclusion"], "(result args n)")
            self.assertIsNone(fact["priority"])

    def naming_policy(self):
        return {"activation_names": "source_position_hfact", "instance_suffix_default": "RegisteredFact"}

    def named_fixture(self, directory):
        shared, closure, evidence = self.fixture(directory)
        shared["fact_name_policy"] = self.naming_policy()
        choice = shared["fact_choices"][0]
        del choice["instance_name"]
        for activation in choice["activation_premises"]:
            del activation["name"]
        return shared, closure, evidence

    def test_naming_preserves_source_positions_and_independent_argument_order(self):
        with tempfile.TemporaryDirectory() as directory:
            shared, closure, evidence = self.named_fixture(directory)
            original = deepcopy(shared)
            expected = deepcopy(shared)
            del expected["fact_name_policy"]
            choice = expected["fact_choices"][0]
            choice["instance_name"] = "helperRegisteredFact"
            choice["activation_premises"][0]["name"] = "Hfact2"
            choice["activation_premises"][1]["name"] = "Hfact1"
            generator._compact_fact_choices(expected, closure, evidence)
            generator._compact_fact_choices(shared, closure, evidence)
            self.assertEqual(shared["support_metadata"], expected["support_metadata"])
            self.assertEqual(shared["fact_choices"], original["fact_choices"])
            fact = shared["support_metadata"]["facts"][0]
            self.assertEqual([row["name"] for row in fact["premises"]], ["Hfact2", "Hfact1"])
            self.assertTrue(fact["arguments"][-2].endswith(" Hfact1"))
            self.assertTrue(fact["arguments"][-1].endswith(" Hfact2"))

    def test_naming_preserves_explicit_exceptions_suffixes_and_attributes(self):
        for suffix in (None, "Fact", "Hint"):
            with self.subTest(suffix=suffix), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.named_fixture(directory)
                choice = shared["fact_choices"][0]
                choice.update(locality="local", priority=7, explicit_lemma=True)
                if suffix is not None:
                    choice["instance_suffix"] = suffix
                choice["activation_premises"][0]["name"] = "Hlength"
                generator._compact_fact_choices(shared, closure, evidence)
                fact = shared["support_metadata"]["facts"][0]
                self.assertEqual(fact["name"], "helper" + (suffix or "RegisteredFact"))
                self.assertEqual([row["name"] for row in fact["premises"]], ["Hlength", "Hfact1"])
                self.assertEqual((fact["locality"], fact["priority"], fact["explicit_lemma"]),
                                 ("local", 7, True))
                self.assertTrue(fact["arguments"][-1].endswith(" Hlength"))

    def test_naming_rejects_copied_and_conflicting_names(self):
        for change in ("instance", "conventional", "conflicting", "parameter", "duplicate", "derived_instance"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.named_fixture(directory)
                choice = shared["fact_choices"][0]
                if change == "instance":
                    choice["instance_name"] = "helperRegisteredFact"
                elif change == "derived_instance":
                    shared["fact_choices"].append(deepcopy(choice))
                elif change == "duplicate":
                    for activation in choice["activation_premises"]:
                        activation["name"] = "Hsame"
                else:
                    choice["activation_premises"][0]["name"] = {
                        "conventional": "Hfact2", "conflicting": "Hfact1", "parameter": "args"}[change]
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)

    def test_naming_rejects_invalid_suffixes(self):
        for suffix in (None, True, 1, "", "1Fact", "Fact.Name", "Fact;", {}, []):
            with self.subTest(suffix=suffix), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.named_fixture(directory)
                shared["fact_choices"][0]["instance_suffix"] = suffix
                with self.assertRaisesRegex(ValueError, "invalid identifier"):
                    generator._compact_fact_choices(shared, closure, evidence)

    def test_naming_rejects_unsupported_incomplete_and_copied_policies(self):
        policies = [None, True, [], {}, {"activation_names": "source_position_hfact"},
                    {"instance_suffix_default": "RegisteredFact"},
                    dict(self.naming_policy(), activation_names="list_position_hfact"),
                    dict(self.naming_policy(), instance_suffix_default="Hint"),
                    dict(self.naming_policy(), instance_name="copied")]
        for policy in policies:
            with self.subTest(policy=policy), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.named_fixture(directory)
                shared["fact_name_policy"] = policy
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)
        with self.assertRaisesRegex(ValueError, "require fact choices"):
            generator._compact_fact_choices({"fact_name_policy": self.naming_policy()}, {}, None)

    def test_naming_does_not_infer_source_positions_or_allow_invalid_positions(self):
        for index in (None, True, -1, 2, "0", {}, []):
            with self.subTest(index=index), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.named_fixture(directory)
                shared["fact_choices"][0]["activation_premises"][0]["source_premise"] = index
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)
        with tempfile.TemporaryDirectory() as directory:
            shared, closure, evidence = self.named_fixture(directory)
            del shared["fact_choices"][0]["activation_premises"][0]["source_premise"]
            with self.assertRaises(ValueError):
                generator._compact_fact_choices(shared, closure, evidence)

    def test_unselected_naming_keeps_explicit_names_and_requires_them(self):
        with tempfile.TemporaryDirectory() as directory:
            shared, closure, evidence = self.fixture(directory)
            shared["fact_choices"][0]["activation_premises"][0]["name"] = "Hfact1"
            generator._compact_fact_choices(shared, closure, evidence)
            self.assertEqual(shared["support_metadata"]["facts"][0]["name"], "helperFact")
            self.assertEqual(shared["support_metadata"]["facts"][0]["premises"][0]["name"], "Hfact1")
        for change in ("suffix", "instance", "activation"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.fixture(directory)
                choice = shared["fact_choices"][0]
                if change == "suffix":
                    choice["instance_suffix"] = "Fact"
                elif change == "instance":
                    del choice["instance_name"]
                else:
                    del choice["activation_premises"][0]["name"]
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)

    def test_rejects_copied_missing_repeated_and_out_of_range_choices(self):
        for change in ("copied", "missing", "repeated", "range", "name", "unknown", "priority"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.fixture(directory)
                choice = shared["fact_choices"][0]
                if change == "copied":
                    shared["support_metadata"]["facts"] = []
                elif change == "missing":
                    choice["activation_premises"].pop()
                elif change == "repeated":
                    choice["activation_premises"][1]["source_premise"] = 1
                elif change == "range":
                    choice["activation_premises"][0]["source_premise"] = 2
                elif change == "name":
                    choice["activation_premises"][0]["name"] = "args"
                elif change == "unknown":
                    choice["parameters"] = []
                else:
                    choice["priority"] = True
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)

    def test_rejects_unbound_source_signature_type_or_clause(self):
        for change in ("source", "signature", "type", "clause"):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                shared, closure, evidence = self.fixture(directory)
                if change == "source":
                    Path(directory, "Facts.v").write_text("Lemma helper args : True.")
                elif change == "signature":
                    evidence["signature_packets"] = []
                else:
                    field = "type_spellings" if change == "type" else "spelling_choices"
                    path = Path(evidence[field]["path"])
                    value = json.loads(path.read_text())
                    if change == "type":
                        value["shared_type_spellings"][0]["printed_type_sha256"] = "0" * 64
                    else:
                        value[0]["spelling_choices"][0]["source_clause_sha256"] = "0" * 64
                    path.write_text(json.dumps(value))
                    evidence[field]["sha256"] = generator.digest(path)
                with self.assertRaises(ValueError):
                    generator._compact_fact_choices(shared, closure, evidence)


if __name__ == "__main__":
    unittest.main()
