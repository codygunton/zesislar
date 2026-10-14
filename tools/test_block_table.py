"""Check structural refusal without adding semantic proof assumptions."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
import generate_table


class BlockTableTests(unittest.TestCase):
    def fixture(self):
        # Synthetic CFG: beq x0,x0,+8, followed by two return blocks.
        rows = [dict(pc=0x1000, size=4, word=0x463, kind="branch", imm=8,
                     successors=[0x1008, 0x1004]),
                dict(pc=0x1004, size=4, word=0x8067, kind="return", imm=0, successors=[]),
                dict(pc=0x1008, size=4, word=0x8067, kind="return", imm=0, successors=[])]
        cfg = {"schema": 1, "functions": [dict(name="fixture", entry=0x1000, end=0x100c, rows=rows,
            blocks=[dict(start=row["pc"], end=row["pc"] + 4, successors=row["successors"])
                    for row in rows], calls=[], returns=[0x1004, 0x1008])]}
        blocks = [dict(entry_pc="0x1000", end_pc_exclusive="0x1004",
                       successor_pcs=["0x1008", "0x1004"], incoming_edges=[
                           dict(from_block="caller", from_instruction=None, kind="entry")])]
        for pc, condition in [(0x1004, "ne"), (0x1008, "eq")]:
            blocks.append(dict(entry_pc=hex(pc), end_pc_exclusive=hex(pc + 4), successor_pcs=[],
                incoming_edges=[dict(from_block="0x1000", from_instruction="0x1000",
                                     path_condition=dict(op=condition, left="0", right="0"))],
                return_clause=dict(return_instruction_pc=hex(pc))))
        design = dict(function="fixture", entry_pc="0x1000", end_pc_exclusive="0x100c", blocks=blocks,
                      instruction_count=3, block_count=3, conditional_branch_count=1, loop_count=0)
        return cfg, design

    def test_exact_structure_covers_all_edges_and_returns(self):
        cfg, design = self.fixture()
        report = generate_table.structure(cfg, design)
        self.assertEqual(report["coverage"], dict(instructions=3, blocks=3, instruction_edges=2,
            block_edges=2, returns=2, calls=0, conditional_branches=1, loops=0))
        self.assertEqual(len(report["missing_entry_definitions"]), 3)

    def test_targets_come_from_words_not_displacement_metadata(self):
        cfg, design = self.fixture()
        cfg["functions"][0]["rows"][0]["imm"] = 99
        report = generate_table.structure(cfg, design)
        self.assertEqual(report["displacement_metadata_discrepancies"],
                         [dict(pc="0x1000", stored_imm=99, decoded_imm=8)])
        self.assertEqual({edge["target"] for edge in report["edges"]}, {"0x1004", "0x1008"})
        for word, expected in [(0x16060863, 368), (0xfeb798e3, -16)]:
            row = dict(pc=0x800d6970, word=word, size=4)
            self.assertEqual(generate_table.control(row)[3], expected)

    def test_missing_design_edge_is_rejected(self):
        cfg, design = self.fixture()
        design["blocks"][0]["successor_pcs"].pop()
        with self.assertRaisesRegex(ValueError, "omits or adds"):
            generate_table.structure(cfg, design)

    def test_wrong_condition_is_rejected(self):
        cfg, design = self.fixture()
        design["blocks"][1]["incoming_edges"][0]["path_condition"]["op"] = "eq"
        with self.assertRaisesRegex(ValueError, "incoming edges"):
            generate_table.structure(cfg, design)

    def test_overlapping_blocks_are_rejected(self):
        cfg, design = self.fixture()
        # Equal return successors cannot conceal duplicate instruction ownership.
        cfg["functions"][0]["blocks"][1]["end"] = 0x100c
        design["blocks"][1]["end_pc_exclusive"] = "0x100c"
        with self.assertRaisesRegex(ValueError, "inside a block|multiple blocks"):
            generate_table.structure(cfg, design)

    def test_return_inventory_and_exit_are_checked(self):
        for field in ("inventory", "clause"):
            with self.subTest(field=field):
                cfg, design = self.fixture()
                if field == "inventory":
                    cfg["functions"][0]["returns"].pop()
                else:
                    design["blocks"][1]["return_clause"]["return_instruction_pc"] = "0x1008"
                with self.assertRaisesRegex(ValueError, "return"):
                    generate_table.structure(cfg, design)

    def test_external_exit_and_indirect_transfer_are_rejected(self):
        cfg, design = self.fixture()
        cfg["functions"][0]["rows"][0]["word"] = 0x663
        cfg["functions"][0]["rows"][0]["successors"] = [0x100c, 0x1004]
        cfg["functions"][0]["blocks"][0]["successors"] = [0x100c, 0x1004]
        design["blocks"][0]["successor_pcs"] = ["0x100c", "0x1004"]
        with self.assertRaisesRegex(ValueError, "external exit"):
            generate_table.structure(cfg, design)
        with self.assertRaisesRegex(ValueError, "unresolved indirect"):
            generate_table.control(dict(pc=0x1000, word=0x00010067, size=4))

    def test_duplicate_instruction_is_rejected(self):
        cfg, design = self.fixture()
        cfg["functions"][0]["rows"].append(deepcopy(cfg["functions"][0]["rows"][0]))
        with self.assertRaisesRegex(ValueError, "repeats"):
            generate_table.structure(cfg, design)

    def test_manifest_and_design_hash_refusals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cfg, design = self.fixture()
            cfg["artifact_identity"] = "selected"
            cfg_path, design_path, recipe_path = (root / name for name in
                                                ("cfg.json", "design.json", "build-recipe.json"))
            cfg_path.write_text(json.dumps(cfg)); (root / "inventory.json").write_text("inventory")
            inventory_hash = generate_table.digest(root / "inventory.json")
            design["hashes"] = dict(selected_elf_sha256="elf", inventory_sha256=inventory_hash)
            design_path.write_text(json.dumps(design))
            recipe = dict(artifact_identity="selected", elf_sha256="elf",
                derived={"cfg.json": dict(artifact_identity="selected", schema_version=1)},
                artifacts={"cfg.json": generate_table.digest(cfg_path), "inventory.json": inventory_hash})
            recipe_path.write_text(json.dumps(recipe))
            self.assertEqual(generate_table.bound_inputs(recipe_path, cfg_path, design_path)["coverage"]["blocks"], 3)
            for field in ("cfg", "design"):
                with self.subTest(field=field):
                    if field == "cfg":
                        cfg_path.write_text(json.dumps(cfg) + "\n")
                    else:
                        cfg_path.write_text(json.dumps(cfg))
                        design["hashes"]["inventory_sha256"] = "stale"
                        design_path.write_text(json.dumps(design))
                    with self.assertRaisesRegex(ValueError, "hash"):
                        generate_table.bound_inputs(recipe_path, cfg_path, design_path)

    def test_function_identity_is_checked(self):
        cfg, design = self.fixture()
        design["function"] = "other"
        with self.assertRaisesRegex(ValueError, "different functions"):
            generate_table.structure(cfg, design)

    def test_selected_stock_structure(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / "build/stock-zisk/cfg.json").read_text())
        design = json.loads((root / "ZesuSsz/Evidence/decode_item_block_design.json").read_text())
        report = generate_table.structure(cfg, design)
        self.assertEqual(report["coverage"], dict(instructions=116, blocks=24,
            instruction_edges=124, block_edges=32, returns=6, calls=0, conditional_branches=14, loops=2))
        self.assertEqual({edge["header"] for edge in report["loop_edges"]}, {"0x800d6a24", "0x800d6ac4"})

    def test_selected_executable_names_are_bound_and_rendered_once(self):
        root = Path(__file__).resolve().parents[1]
        design_path = root / "ZesuSsz/Evidence/decode_item_block_design.json"
        design = json.loads(design_path.read_text())
        report = generate_table.bound_inputs(root / "build/stock-zisk/build-recipe.json",
                                             root / "build/stock-zisk/cfg.json", design_path)
        self.assertEqual(report["missing_entry_definitions"], [])
        source = generate_table.render_table(design, report)
        self.assertEqual(source.count("Definition decodeItemState"), 24)
        for block in design["blocks"]:
            name = f"decodeItemState{generate_table.address(block['entry_pc']):x}"
            self.assertEqual(source.count(f"Definition {name} :"), 1)
            self.assertIn(f"(* Entry: {block['entry_definition']}.", source)

    def executable_fixture(self):
        cfg, design = self.fixture()
        design["table_convention"] = {
            "entry_type": "(Z * iProp Sigma)",
            "pc_ownership": "instr_pre pc state supplies PC; entry predicates do not own PC",
            "existential_binders": "Each row's binders, in their listed order",
            "resource_application": "Apply resource_predicate to arguments in order",
            "code_persistence": "block_table_pre boxes the supplied code resource",
            "code_resource": "Contracts.Code.fixtureCode",
            "code_source_hashes": {"Contracts/Code.v": "0" * 64},
        }
        for block in design["blocks"]:
            name = f"ZesuSsz.Contracts.Fixture.entry{address_suffix(block['entry_pc'])}"
            block.update(entry_definition=name, resource_predicate=name,
                         binders=[dict(name="args", type="FixtureArgs"),
                                  dict(name="frameBytes", type="list byte")],
                         arguments=["args", "frameBytes"], source_hashes={"Fixture.v": "0" * 64})
        return design, generate_table.structure(cfg, design)

    def test_edge_alternative_is_preserved_in_structural_metadata(self):
        cfg, design = self.fixture()
        target = design["blocks"][1]
        name = "Fixture.Contracts.selectedEntry"
        target.update(entry_definition="Fixture.Contracts.defaultEntry",
                      resource_predicate="Fixture.Contracts.defaultEntry", binders=[],
                      arguments=[], source_hashes={"Fixture/Contracts.v": "0" * 64})
        target["incoming_edges"][0]["resource_alternative"] = name
        report = generate_table.structure(cfg, design)
        selected = [edge for edge in report["edges"] if edge["target"] == "0x1004"]
        self.assertEqual(selected[0]["resource_alternative"], name)
        self.assertNotIn("resource_alternative", report["edges"][0])
        self.assertEqual(target["resource_predicate"], "Fixture.Contracts.defaultEntry")

    def test_alternative_does_not_hide_a_changed_control_edge(self):
        cfg, design = self.fixture()
        target = design["blocks"][1]
        target.update(entry_definition="Fixture.Contracts.entry",
                      resource_predicate="Fixture.Contracts.entry", binders=[],
                      arguments=[], source_hashes={"Fixture/Contracts.v": "0" * 64})
        target["incoming_edges"][0].update(resource_alternative="Fixture.Contracts.otherEntry",
                                           from_instruction="0x1004")
        with self.assertRaisesRegex(ValueError, "incoming edges"):
            generate_table.structure(cfg, design)

    def test_absent_alternatives_preserve_exact_rendering(self):
        import hashlib
        design, report = self.executable_fixture()
        source = generate_table.render_table(design, report).encode()
        self.assertEqual(hashlib.sha256(source).hexdigest(),
                         "cf4fcf414856f25a4cb05305a950bfdff7ae562fc7a16f183a33eddeb0324df7")

    def test_rendering_preserves_exact_binders_and_arguments(self):
        design, report = self.executable_fixture()
        design["blocks"][0]["arguments"] = ["frameBytes", "args"]
        source = generate_table.render_table(design, report)
        self.assertTrue(source.startswith("Require Import ZesuSsz.Automation.All.\n"))
        self.assertIn("∃ (args : FixtureArgs) (frameBytes : list byte), "
                      "ZesuSsz.Contracts.Fixture.entry1000 (frameBytes) (args)", source)
        self.assertNotIn("∀ (args : FixtureArgs)", source)
        self.assertEqual(source.count("Definition decodeItemState"), 3)
        self.assertIn("block_table_complete decodeItemBlockTable.", source)
        self.assertIn("(0x1000, 0x1008)", source)
        self.assertIn("(0x1004, 0x1004)", source)
        self.assertNotIn("Lemma ", source)
        self.assertNotIn("Axiom ", source)
        self.assertNotIn("Admitted", source)

    def test_rendering_leaves_parameter_free_entries_unquantified(self):
        design, report = self.executable_fixture()
        design["blocks"][0]["binders"] = []
        design["blocks"][0]["arguments"] = []
        source = generate_table.render_table(design, report)
        self.assertIn("(ZesuSsz.Contracts.Fixture.entry1000)%I.", source)
        self.assertNotIn("∃ ,", source)

    def test_rendering_imports_bound_argument_types(self):
        design, report = self.executable_fixture()
        design["blocks"][0]["source_hashes"]["Contracts/ArgumentTypes.v"] = "0" * 64
        source = generate_table.render_table(design, report)
        shared = "Require Import Contracts.ArgumentTypes."
        self.assertEqual(source.count(shared), 1)
        self.assertLess(source.index(shared), source.index("(args : FixtureArgs)"))

    def test_rendering_rejects_missing_entries_and_duplicate_binders(self):
        design, report = self.executable_fixture()
        del design["blocks"][0]["entry_definition"]
        with self.assertRaisesRegex(ValueError, "lacks approved fields"):
            generate_table.render_table(design, report)
        design, report = self.executable_fixture()
        design["blocks"][0]["binders"].append(dict(name="args", type="FixtureArgs"))
        with self.assertRaisesRegex(ValueError, "repeated or reserved"):
            generate_table.render_table(design, report)

    def test_executable_sources_require_exact_local_hashes(self):
        design, _ = self.executable_fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Contracts.v"
            path.write_text("supplied declaration")
            (root / "Contracts").mkdir()
            code = root / "Contracts/Code.v"
            code.write_text("supplied code resource")
            design["table_convention"]["code_source_hashes"] = {"Contracts/Code.v": generate_table.digest(code)}
            expected = generate_table.digest(path)
            for block in design["blocks"]:
                block["source_hashes"] = {"Contracts.v": expected}
            self.assertEqual(generate_table.entry_source_hashes(design, root),
                             {"Contracts.v": expected, "Contracts/Code.v": generate_table.digest(code)})
            path.write_text("changed declaration")
            with self.assertRaisesRegex(ValueError, "source hash changed"):
                generate_table.entry_source_hashes(design, root)
            design["blocks"][0]["source_hashes"] = {"../Contracts.v": expected}
            with self.assertRaisesRegex(ValueError, "repository-relative"):
                generate_table.entry_source_hashes(design, root)

    def test_table_code_resource_is_bound_and_rendered(self):
        design, report = self.executable_fixture()
        source = generate_table.render_table(design, report)
        self.assertIn("Require Import Contracts.Code.", source)
        self.assertIn("block_table_code := Contracts.Code.fixtureCode;", source)
        self.assertIn("block_table_entries := [", source)
        del design["table_convention"]["code_resource"]
        with self.assertRaisesRegex(ValueError, "fully qualified"):
            generate_table.render_table(design, report)

    def test_table_code_source_is_required(self):
        design, report = self.executable_fixture()
        design["table_convention"]["code_source_hashes"] = {"Other.v": "0" * 64}
        with self.assertRaisesRegex(ValueError, "declaration has no bound source"):
            generate_table.render_table(design, report)

    def test_unknown_table_convention_is_rejected(self):
        design, report = self.executable_fixture()
        design["table_convention"]["existential_binders"] = "Invented locals"
        with self.assertRaisesRegex(ValueError, "approved convention"):
            generate_table.render_table(design, report)

    def test_design_generator_uses_approved_table_convention(self):
        root = Path(__file__).resolve().parents[1]
        path = root / "ZesuSsz/Evidence/generate_decode_item_block_design.py"
        spec = importlib.util.spec_from_file_location("decode_item_block_design", path)
        generator = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(generator)
        design = generator.build()
        convention = generate_table.table_convention(design)
        self.assertNotIn("universal_binders", convention)
        source_hashes = generate_table.entry_source_hashes(design, root)
        for path, expected in convention["code_source_hashes"].items():
            self.assertEqual(source_hashes[path], expected)

    def test_universal_state_convention_is_rejected(self):
        design, report = self.executable_fixture()
        convention = design["table_convention"]
        convention["universal_binders"] = convention.pop("existential_binders")
        with self.assertRaisesRegex(ValueError, "approved convention"):
            generate_table.render_table(design, report)


def address_suffix(value):
    return f"{int(value, 0):x}"


if __name__ == "__main__":
    unittest.main()
