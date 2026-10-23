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


if __name__ == "__main__":
    unittest.main()
