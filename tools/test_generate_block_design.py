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
