"""Validate supplied contracts without creating missing entry resources."""
from copy import deepcopy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from entry_schema import contract_fields, design_states, edge_contract_fields, entry_state, FIELDS
import chain_root


class EntrySchemaTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        source = self.root / "Fixture/Contracts.v"
        source.parent.mkdir()
        source.write_text("From Coq Require Import ZArith.\n"
                          "Definition DecodeItemArgs := unit.\n"
                          "Definition entry (args : DecodeItemArgs) (n : Z) := True.\n"
                          "Definition resources (args : DecodeItemArgs) (n : Z) := True.\n")
        self.row = {"entry_pc": "0x10", "entry_class": "return",
                    "entry_definition": "Fixture.Contracts.entry",
                    "binders": [{"name": "args", "type": "DecodeItemArgs"},
                                {"name": "n", "type": "Z"}],
                    "arguments": ["args", "n + 1"],
                    "resource_predicate": "Fixture.Contracts.resources",
                    "source_hashes": {"Fixture/Contracts.v": hashlib.sha256(source.read_bytes()).hexdigest()}}

    def state(self, row=None):
        return entry_state(row or self.row, self.root, "Fixture.Traces.instrs", ["  selectedCode -∗"])

    def test_description_has_no_executable_contract(self):
        self.assertIsNone(contract_fields({"entry_class": "return"}))

    def test_partial_schema_is_a_gap(self):
        row = {"entry_pc": "0x10", "entry_definition": "Fixture.entry"}
        states, errors = design_states({"blocks": [row]}, self.root, "Fixture.Traces.instrs", ["code -∗"])
        self.assertEqual(states, {})
        self.assertIn("lacks approved fields", errors[16])

    def test_absent_edge_alternative_preserves_contract_fields(self):
        self.assertEqual(edge_contract_fields(self.row, {"from_block": "0x8"}),
                         contract_fields(self.row))

    def test_edge_alternative_preserves_parameters_and_source_bindings(self):
        original = deepcopy(self.row)
        fields = edge_contract_fields(self.row, {"from_block": "0x8",
            "resource_alternative": "Fixture.Contracts.otherEntry"})
        self.assertEqual(fields["entry_definition"], "Fixture.Contracts.otherEntry")
        self.assertEqual(fields["resource_predicate"], "Fixture.Contracts.otherEntry")
        for key in ("binders", "arguments", "source_hashes"):
            self.assertEqual(fields[key], self.row[key])
        fields["binders"][0]["type"] = "nat"
        self.assertEqual(self.row, original)

    def test_edge_alternative_rejects_invalid_names(self):
        for name in (None, "", "entry", "Fixture.Contracts.entry. Abort.", 1):
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, "fully qualified"):
                    edge_contract_fields(self.row, {"from_block": "0x8",
                                                   "resource_alternative": name})

    def test_edge_alternative_requires_bound_target_source(self):
        with self.assertRaisesRegex(ValueError, "do not bind"):
            edge_contract_fields(self.row, {"from_block": "0x8",
                "resource_alternative": "Other.Contracts.entry"})

    def test_edge_alternative_rejects_caller_selection(self):
        with self.assertRaisesRegex(ValueError, "caller entry"):
            edge_contract_fields(self.row, {"from_block": "caller",
                "resource_alternative": "Fixture.Contracts.entry"})

    def test_edge_alternative_requires_executable_target(self):
        with self.assertRaisesRegex(ValueError, "lacks a target contract"):
            edge_contract_fields({}, {"from_block": "0x8",
                "resource_alternative": "Fixture.Contracts.entry"})

    def test_selected_edge_entry_checks_actual_declaration(self):
        fields = edge_contract_fields(self.row, {"from_block": "0x8",
            "resource_alternative": "Fixture.Contracts.absent"})
        with self.assertRaisesRegex(ValueError, "lacks Definition"):
            self.state({**self.row, **fields})
        fields = edge_contract_fields(self.row, {"from_block": "0x8",
            "resource_alternative": "Fixture.Contracts.entry"})
        state = self.state({**self.row, **fields})
        self.assertEqual(state["spatial"], ["Fixture.Contracts.entry (args) (n + 1)"])

    def test_only_approved_fields_are_consumed(self):
        self.row["needed_resources"] = {"description": "owned memory"}
        self.assertEqual(set(contract_fields(self.row)), FIELDS)

    def test_input_values_remain_unchanged(self):
        original = deepcopy(self.row)
        result = contract_fields(self.row)
        result["binders"][0]["type"] = "nat"
        self.state()
        self.assertEqual(self.row, original)

    def test_names_must_be_fully_qualified(self):
        for key in ("entry_definition", "resource_predicate"):
            for name in ("entry", "Fixture.entry. Abort."):
                with self.subTest(key=key, name=name):
                    row = deepcopy(self.row)
                    row[key] = name
                    with self.assertRaisesRegex(ValueError, "fully qualified"):
                        contract_fields(row)

    def test_nested_shapes_reject_ambiguous_records(self):
        for key, value in (("binders", {}), ("binders", [{"name": "args", "type": "Z", "value": "0"}]),
                           ("arguments", "args n"), ("source_hashes", []),
                           ("source_hashes", {"Fixture/Contracts.v": "123"})):
            with self.subTest(key=key, value=value):
                row = deepcopy(self.row)
                row[key] = value
                with self.assertRaises(ValueError):
                    contract_fields(row)

    def test_binder_names_are_unique(self):
        self.row["binders"].append({"name": "args", "type": "Z"})
        with self.assertRaisesRegex(ValueError, "repeated"):
            contract_fields(self.row)

    def test_resource_arguments_retain_order_and_expressions(self):
        state = self.state()
        self.assertEqual(state["spatial"], ["Fixture.Contracts.resources (args) (n + 1)"])
        self.assertEqual(state["arguments"], "args n")
        self.assertTrue(state["binders"].endswith("(args : DecodeItemArgs) (n : Z)"))
        self.assertEqual(state["root_provenance"], contract_fields(self.row))

    def test_source_hash_changes_prevent_execution(self):
        (self.root / "Fixture/Contracts.v").write_text("Definition entry := False.")
        states, errors = design_states({"blocks": [self.row]}, self.root, "Fixture.Traces.instrs", ["code -∗"])
        self.assertFalse(states)
        self.assertIn("source hash changed", errors[16])

    def test_both_definitions_require_bound_sources(self):
        self.row["resource_predicate"] = "Other.Contracts.resources"
        with self.assertRaisesRegex(ValueError, "do not bind"):
            self.state()

    def test_source_paths_cannot_escape_repository(self):
        for name in ("../Contracts.v", "/tmp/Contracts.v", "Fixture//Contracts.v"):
            with self.subTest(name=name):
                self.row["source_hashes"] = {name: "0" * 64}
                with self.assertRaisesRegex(ValueError, "repository-relative"):
                    contract_fields(self.row)

    def test_schema_and_description_can_share_a_design(self):
        states, errors = design_states({"blocks": [self.row, {"entry_pc": "0x20"}]},
                                      self.root, "Fixture.Traces.instrs", ["code -∗"])
        self.assertEqual(list(states), [16])
        self.assertFalse(errors)

    def test_shared_renderer_retains_supplied_resources(self):
        block = {"start": "0x10", "end": "0x14", "successors": ["0x14"]}
        with patch.object(chain_root.gen_block.call_sites, "premises", return_value=([], [], [])), \
             patch.object(chain_root.gen_block.call_sites, "contracts", return_value={}), \
             patch.object(chain_root.gen_block.call_sites, "call_sites", return_value={}):
            source = chain_root.render_probe(self.state(), block, 20)
        self.assertIn("Fixture.Contracts.resources (args) (n + 1)", source)
        self.assertIn("DesignedEntry_10 args n", source)
        self.assertIn("selectedCode -∗", source)
        self.assertIn("Require Import Fixture.Contracts.", source)
        self.assertIn("instr_pre 0x14", source)


if __name__ == "__main__":
    unittest.main()
