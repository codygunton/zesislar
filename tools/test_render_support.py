"""Check declaration rendering, refusal boundaries, and output freshness."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import render_support as renderer


class SupportRendererTests(unittest.TestCase):
    def fixture(self, root):
        source = root / "Contracts/Fixture.v"
        source.parent.mkdir(parents=True)
        source.write_text("\n".join([
            "Definition base (args : Args) (frame : list byte) (pointer : bv 64) : iProp Sigma := True%I.",
            "Definition continuationAt (args : Args) (address : Z) : iProp Sigma := True%I.",
            "Definition entry (args : Args) (frame : list byte) (prefix : byte) (rest : list byte) : iProp Sigma := True%I.",
            "Definition head (args : Args) (prefix : byte) (rest : list byte) : Prop := True.",
        ]) + "\n")
        row = {
            "entry_pc": "0x1000",
            "entry_definition": "Contracts.Fixture.entry",
            "resource_predicate": "Contracts.Fixture.entry",
            "binders": [{"name": name, "type": kind} for name, kind in [
                ("args", "Args"), ("frame", "list byte"),
                ("prefix", "byte"), ("rest", "list byte")]],
            "arguments": ["args", "frame", "prefix", "rest"],
            "source_hashes": {"Contracts/Fixture.v": hashlib.sha256(source.read_bytes()).hexdigest()},
            "incoming_edges": [{"from_block": "0xff0", "from_instruction": "0xffc"}],
            "support": {
                "version": 1,
                "existentials": [{"name": name, "type": "bv 64"} for name in ("x13", "x14")],
                "components": [
                    {"kind": "pure", "terms": [
                        {"term": "head args prefix rest", "provenance": {"kind": "data", "source": "Contracts.Fixture.head"}},
                        {"term": "bv_unsigned (Z_to_bv 64 (lengthZ args)) <> 0", "provenance": {
                            "kind": "path", "from_block": "0xff0", "from_instruction": "0xffc"}},
                    ]},
                    {"kind": "register", "name": "x13", "value": "RVal_Bits x13"},
                    {"kind": "register", "name": "x14", "value": "RVal_Bits x14"},
                    {"kind": "base", "predicate": "Contracts.Fixture.base", "arguments": [
                        "args", "frame", "Z_to_bv 64 (pointer args)"], "memory_deltas": []},
                ],
                "loop": None,
                "continuation": {"mode": "included_in_base", "component_index": 3,
                                 "predicate": "Contracts.Fixture.continuationAt",
                                 "arguments": ["args", "returnAddress args"], "order": "resources_first"},
                "additional_definitions": [],
            },
        }
        metadata = {
            "version": 1,
            "entries_imports": [{"mode": "import", "module": "ZesuSsz.Automation.All"},
                                {"mode": "import", "module": "Contracts.Fixture"}],
            "entries_scopes": ["Z_scope"],
            "registrations_imports": [{"mode": "import", "module": "ZesuSsz.Automation.All"},
                                      {"mode": "import", "module": "isla.automation"}],
            "unfold_entries": ["entry"], "introductions": [],
            "hint_umbrella": [], "scoped_imports": [], "facts": [],
        }
        return {"function": "sample.fixture", "blocks": [row], "support": metadata}

    def test_preserves_parameters_exists_casts_and_resource_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            outputs = renderer.render_support(design, root, name_prefix="fixture")
            source = outputs[Path("ZesuSsz/Generated/Fixture/Entries.v")]
            fragments = ["(args : Args)", "(frame : list byte)", "(prefix : byte)", "(rest : list byte)",
                         "∃ (x13 : bv 64) (x14 : bv 64)",
                         "head args prefix rest) /\\", "bv_unsigned (Z_to_bv 64 (lengthZ args)) <> 0)⌝",
                         '"x13" ↦ᵣ (RVal_Bits x13)', '"x14" ↦ᵣ (RVal_Bits x14)',
                         "Contracts.Fixture.base (args) (frame) (Z_to_bv 64 (pointer args))"]
            positions = [source.index(value) for value in fragments]
            self.assertEqual(positions, sorted(positions))
            self.assertNotIn("True", source)
            self.assertNotIn("continuationAt", source)
            self.assertNotIn("Proof.", source)
            self.assertNotIn("Lemma", source)
            self.assertEqual(len(outputs), 2)

    def test_registrations_preserve_pairs_and_import_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            design["support"]["hint_umbrella"] = [
                {"mode": "export", "module": "Facts.Second"},
                {"mode": "export", "module": "Facts.First"}]
            result = renderer.render_support(design, root, name_prefix="fixture")
            source = result[Path("ZesuSsz/Generated/Fixture/Registrations.v")]
            self.assertIn("Global Instance : LithiumUnfold (@entry) := I.\nGlobal Typeclasses Opaque entry.", source)
            self.assertIn("Require Export ZesuSsz.Generated.Fixture.Entries.", source)
            self.assertLess(source.index("Facts.Second"), source.index("Facts.First"))
            self.assertNotIn("Proof.", source)

    def test_auxiliary_traversal_preserves_dependency_order_and_validates_parameters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            main = design["blocks"][0]
            before = deepcopy(main)
            before.update(entry_definition="Contracts.Fixture.before", resource_predicate="Contracts.Fixture.before")
            after = deepcopy(before)
            after.update(entry_definition="Contracts.Fixture.after", resource_predicate="Contracts.Fixture.after")
            after["support"]["components"] = [{
                "kind": "disjunction", "alternatives": [
                    {"kind": "application", "predicate": "ZesuSsz.Generated.Fixture.Entries.before",
                     "arguments": ["args", "frame", "prefix", "rest"]},
                    {"kind": "application", "predicate": "ZesuSsz.Generated.Fixture.Entries.entry",
                     "arguments": ["args", "frame", "prefix", "rest"]}]}]
            after["support"]["continuation"] = {"mode": "none"}
            main["support"]["additional_definitions"] = [
                {"position": "before", "declaration": before},
                {"position": "after", "declaration": after}]
            design["support"]["unfold_entries"] = ["before", "entry", "after"]
            self.assertEqual([row["entry_definition"].rsplit(".", 1)[-1]
                              for row in renderer.support_declarations(design)], ["before", "entry", "after"])
            output = renderer.render_support(design, root, name_prefix="fixture")
            source = output[Path("ZesuSsz/Generated/Fixture/Entries.v")]
            self.assertLess(source.index("Definition before"), source.index("Definition entry"))
            self.assertLess(source.index("Definition entry"), source.index("Definition after"))
            self.assertIn(" ∨", source)
            before["binders"][0]["type"] = "ltac:(exact I)"
            with self.assertRaisesRegex(ValueError, "command or tactic"):
                renderer.support_declarations(design)
            before["binders"][0]["type"] = "Args"
            after["entry_definition"] = main["entry_definition"]
            with self.assertRaisesRegex(ValueError, "repeated"):
                renderer.support_declarations(design)

    def test_handwritten_unfold_sources_are_ordered_bound_and_disjoint(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            support = design["support"]
            support["source_hashes"] = deepcopy(design["blocks"][0]["source_hashes"])
            support["unfold_sources"] = ["Contracts.Fixture.continuationAt", "Contracts.Fixture.base"]
            source = renderer.render_support(design, root, name_prefix="fixture")[
                Path("ZesuSsz/Generated/Fixture/Registrations.v")]
            expected = ["Global Typeclasses Opaque entry.",
                        "Global Instance : LithiumUnfold (@Contracts.Fixture.continuationAt) := I.",
                        "Global Typeclasses Opaque Contracts.Fixture.continuationAt.",
                        "Global Instance : LithiumUnfold (@Contracts.Fixture.base) := I.",
                        "Global Typeclasses Opaque Contracts.Fixture.base."]
            positions = [source.index(value) for value in expected]
            self.assertEqual(positions, sorted(positions))
            for invalid in (["Contracts.Fixture.base"] * 2,
                            ["Contracts.Fixture.entry"],
                            ["ZesuSsz.Generated.Fixture.Entries.other"],
                            ["Contracts.Fixture.absent"],
                            ["Unbound.Source.base"],
                            ["Contracts.Fixture.base. Proof. exact I. Qed."],
                            "Contracts.Fixture.base"):
                support["unfold_sources"] = invalid
                with self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")
            support["unfold_sources"] = ["Contracts.Fixture.base"]
            support["source_hashes"]["Contracts/Fixture.v"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "hash changed"):
                renderer.render_support(design, root, name_prefix="fixture")

    def test_generated_references_refuse_self_forward_cycles_and_wrong_arity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = self.fixture(root)
            for target in ("entry", "missing"):
                design = deepcopy(original)
                design["blocks"][0]["support"]["components"][3]["predicate"] = (
                    "ZesuSsz.Generated.Fixture.Entries." + target)
                with self.assertRaisesRegex(ValueError, "must precede"):
                    renderer.render_support(design, root, name_prefix="fixture")
            design = deepcopy(original)
            after = deepcopy(design["blocks"][0])
            after.update(entry_definition="Contracts.Fixture.after", resource_predicate="Contracts.Fixture.after")
            after["support"]["components"] = [{"kind": "application",
                "predicate": "ZesuSsz.Generated.Fixture.Entries.entry", "arguments": ["args"]}]
            after["support"]["continuation"] = {"mode": "none"}
            design["blocks"][0]["support"]["additional_definitions"] = [{"position": "after", "declaration": after}]
            design["support"]["unfold_entries"].append("after")
            with self.assertRaisesRegex(ValueError, "declared arity"):
                renderer.render_support(design, root, name_prefix="fixture")
            after["support"]["components"][0]["arguments"] = ["args", "frame", "prefix", "rest"]
            design["blocks"][0]["support"]["components"][3]["predicate"] = "ZesuSsz.Generated.Fixture.Entries.after"
            with self.assertRaisesRegex(ValueError, "must precede"):
                renderer.render_support(design, root, name_prefix="fixture")

    def test_explicit_memory_lets_true_and_continuation_keep_component_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            support = design["blocks"][0]["support"]
            support["lets"] = [{"name": "local", "type": "Args", "value": "args"}]
            support["components"] = [
                {"kind": "register_collection", "value": "regs local"},
                {"kind": "byte_array", "address": "pointer local", "value": "frame"},
                {"kind": "unknown_byte_array", "address": "pointer local - 16", "length": "16"},
                {"kind": "continuation", "predicate": "Contracts.Fixture.continuationAt",
                 "arguments": ["args", "returnAddress args"]}, {"kind": "true"}]
            support["continuation"] = {"mode": "explicit", "component_index": 3,
                "predicate": "Contracts.Fixture.continuationAt", "arguments": ["args", "returnAddress args"],
                "order": "resources_first"}
            outputs = renderer.render_support(design, root, name_prefix="fixture")
            source = outputs[Path("ZesuSsz/Generated/Fixture/Entries.v")]
            fragments = ["let local : Args := (args) in", "reg_col (regs local)",
                         "(pointer local) ↦ₘ∗ (frame)", "(pointer local - 16) ↦ₘ? (16)",
                         "Contracts.Fixture.continuationAt (args) (returnAddress args)", "(True)"]
            self.assertEqual([source.index(x) for x in fragments], sorted(source.index(x) for x in fragments))
            support["continuation"] = {"mode": "none"}
            with self.assertRaisesRegex(ValueError, "conceals"):
                renderer.render_support(design, root, name_prefix="fixture")

    def test_loop_metadata_matches_existing_lvar_binders_and_invariant(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            support = design["blocks"][0]["support"]
            support["existentials"] += [{"name": "n", "type": 'lvar "count" Z'},
                                        {"name": "i", "type": 'lvar "index" Z'}]
            support["loop"] = {"count": {"name": "n", "label": "count"},
                               "index": {"name": "i", "label": "index"},
                               "invariant": {"component_index": 3, "predicate": "Contracts.Fixture.base",
                                             "arguments": ["args", "frame", "Z_to_bv 64 (pointer args)"]}}
            renderer.validate_support(design, root, name_prefix="fixture")
            support["loop"]["index"]["label"] = "wrong"
            with self.assertRaisesRegex(ValueError, "lvar binder"):
                renderer.validate_support(design, root, name_prefix="fixture")

    def test_fact_constructors_preserve_evidence_locality_priority_and_hidden_binders(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            helper = root / "ZesuSsz/Automation/FactRegistry.v"
            helper.parent.mkdir(parents=True)
            helper.write_text("Definition zesu_simpl_and_fact := I.\n"
                              "Class ZesuFactEvidence (P : Prop) := { zesu_fact_evidence : P }.\n")
            lemma = root / "Facts/Fixture.v"
            lemma.parent.mkdir()
            lemma.write_text("Lemma suppliedFact (key hidden : nat) : True. Proof. exact I. Qed.\n")
            design["support"]["source_hashes"] = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                                                    for p in (helper, lemma)}
            design["support"]["registrations_imports"].append({"mode": "import", "module": "ZesuSsz.Automation.FactRegistry"})
            fact = {"name": "registeredFact", "parameters": [
                {"name": "key", "type": "nat", "implicit": False},
                {"name": "hidden", "type": "nat", "implicit": True}],
                "premises": [{"name": "H", "type": "key = hidden", "implicit": False}],
                "conclusion": "True", "lemma": "Facts.Fixture.suppliedFact",
                "arguments": ["key", "hidden", "@ZesuSsz.Automation.FactRegistry.zesu_fact_evidence _ H"],
                "explicit_lemma": True, "priority": 5, "locality": "local"}
            design["support"]["facts"] = [fact]
            output = renderer.render_support(design, root, name_prefix="fixture")
            text = output[Path("ZesuSsz/Generated/Fixture/Registrations.v")]
            self.assertIn("#[local] Instance registeredFact (key : nat) {hidden : nat} "
                          "(H : ZesuSsz.Automation.FactRegistry.ZesuFactEvidence (key = hidden))", text)
            self.assertIn("SimplAnd (True) True | 5", text)
            self.assertIn("(@Facts.Fixture.suppliedFact (key) (hidden) "
                          "(@ZesuSsz.Automation.FactRegistry.zesu_fact_evidence _ H))", text)
            self.assertNotIn("Proof.", text)
            fact["priority"] = None
            omitted = renderer.render_support(design, root, name_prefix="fixture")
            self.assertIn("SimplAnd (True) True :=", omitted[Path("ZesuSsz/Generated/Fixture/Registrations.v")])
            for invalid in (True, False, -1, "1", 1.0):
                fact["priority"] = invalid
                with self.subTest(priority=invalid), self.assertRaisesRegex(ValueError, "priority"):
                    renderer.render_support(design, root, name_prefix="fixture")
            fact["priority"] = 1
            fact["lemma"] = "Facts.Fixture.missing"
            with self.assertRaisesRegex(ValueError, "unambiguous declaration"):
                renderer.render_support(design, root, name_prefix="fixture")
            fact["lemma"] = "Facts.Fixture.suppliedFact"
            fact["arguments"][0] = "ltac:(exact I)"
            with self.assertRaisesRegex(ValueError, "command or tactic"):
                renderer.render_support(design, root, name_prefix="fixture")

    def test_scoped_imports_are_fixed_ordered_commands_with_strict_targets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            design["support"]["scoped_imports"] = [
                {"target": "entries", "module": "ListNotations"},
                {"target": "entries", "module": "Example.Notations"},
                {"target": "registrations", "module": "Example.Notations"}]
            result = renderer.render_support(design, root, name_prefix="fixture")
            entries = result[Path("ZesuSsz/Generated/Fixture/Entries.v")]
            self.assertIn("Import ListNotations.\nImport Example.Notations.\nOpen Scope", entries)
            design["support"]["registrations_scopes"] = ["Z_scope", "list_scope"]
            registrations = renderer.render_support(design, root, name_prefix="fixture")[
                Path("ZesuSsz/Generated/Fixture/Registrations.v")]
            self.assertIn("Open Scope Z_scope.\nOpen Scope list_scope.", registrations)
            for scopes in (["Z_scope", "Z_scope"], "Z_scope", [True], ["Z_scope. Admitted."]):
                design["support"]["registrations_scopes"] = scopes
                with self.subTest(scopes=scopes), self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")
            design["support"]["registrations_scopes"] = []
            for value in [
                [{"target": "proofs", "module": "ListNotations"}],
                [{"target": "entries", "module": "X. Admitted."}],
                [{"target": "entries", "module": "ListNotations", "body": "exact I"}],
                [{"target": "entries", "module": "ListNotations"}] * 2,
            ]:
                design["support"]["scoped_imports"] = value
                with self.subTest(value=value), self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")

    def test_introductions_preserve_contexts_parameters_targets_and_direct_lemmas(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            helper = root / "Automation/Intro.v"
            helper.parent.mkdir()
            helper.write_text("Class EntryIntro (source : iProp Sigma) (facts : Prop) := evidence : True.\n"
                              "Lemma introduction : True. Proof. exact I. Qed.\n")
            design["support"]["source_hashes"] = {
                str(helper.relative_to(root)): hashlib.sha256(helper.read_bytes()).hexdigest()}
            value = {"name": "registeredIntroduction", "iris_contexts": ["!islaG Sigma", "!threadG"],
                     "parameters": [{"name": name, "type": kind, "implicit": False}
                                    for name, kind in [("args", "Args"), ("frame", "list byte"),
                                                       ("prefix", "byte"), ("rest", "list byte")]],
                     "class": "Automation.Intro.EntryIntro",
                     "source": {"predicate": "ZesuSsz.Generated.Fixture.Entries.entry",
                                "arguments": ["args", "frame", "prefix", "rest"]},
                     "facts": "True", "lemma": "Automation.Intro.introduction",
                     "arguments": ["args", "frame", "prefix", "rest"], "explicit_lemma": False,
                     "priority": None, "locality": "export"}
            design["support"]["introductions"] = [value]
            text = renderer.render_support(design, root, name_prefix="fixture")[
                Path("ZesuSsz/Generated/Fixture/Registrations.v")]
            self.assertIn("#[export] Instance registeredIntroduction `{!islaG Sigma} `{!threadG} "
                          "(args : Args) (frame : list byte) (prefix : byte) (rest : list byte)", text)
            self.assertIn("Automation.Intro.EntryIntro (ZesuSsz.Generated.Fixture.Entries.entry "
                          "(args) (frame) (prefix) (rest)) (True) :=", text)
            self.assertIn("Automation.Intro.introduction (args) (frame) (prefix) (rest).", text)
            original = deepcopy(value)
            for field, bad in [("iris_contexts", ["ltac:(exact I)"]), ("facts", "ltac:(exact I)"),
                               ("priority", True), ("arguments", ["ltac:(exact I)"])]:
                value[field] = bad
                with self.subTest(field=field), self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")
                value[field] = original[field]
            value["source"]["predicate"] = "ZesuSsz.Generated.Fixture.Entries.missing"
            with self.assertRaisesRegex(ValueError, "must precede"):
                renderer.render_support(design, root, name_prefix="fixture")

    def test_memory_deltas_replace_complete_arguments_at_explicit_positions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            base = design["blocks"][0]["support"]["components"][3]
            base["memory_deltas"] = [
                {"argument_index": 2, "value": "Z_to_bv 64 (newPointer args)"},
                {"argument_index": 1, "value": "{| field := frame; bytes := output |}"},
            ]
            original = deepcopy(design)
            result = renderer.render_support(design, root, name_prefix="fixture")
            source = result[Path("ZesuSsz/Generated/Fixture/Entries.v")]
            self.assertIn("Contracts.Fixture.base (args) ({| field := frame; bytes := output |}) "
                          "(Z_to_bv 64 (newPointer args))", source)
            self.assertEqual(design, original)
            for deltas in [
                [{"argument_index": -1, "value": "frame"}],
                [{"argument_index": 3, "value": "frame"}],
                [{"argument_index": True, "value": "frame"}],
                [{"argument_index": 1, "value": "frame"},
                 {"argument_index": 1, "value": "otherFrame"}],
                [{"argument_index": 1, "value": "ltac:(exact I)"}],
            ]:
                base["memory_deltas"] = deltas
                with self.subTest(deltas=deltas), self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")

    def test_refuses_tactics_commands_and_unbalanced_expressions(self):
        for value in ["ltac:(exact I)", "ltac2:(f ())", "nat. Admitted.",
                      "True; exact I", "Proof", "(nat", "nat)", "nat (* unfinished",
                      "{| field := x; other := y }", "{| field := (x; y) |}"]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                renderer.expression(value, "fixture")
        for value in ["Z_to_bv 64 (x + 1)", '"Proof. ltac:(x)"',
                      "fun x => (x, x)", "nat (* Proof. Qed. *)", "Facts.proof_value",
                      "{| field := {| inner := x; other := y |}; bytes := [x; y] |}"]:
            self.assertEqual(renderer.expression(value, "fixture"), value)

    def test_every_expression_field_rejects_injected_proof_text(self):
        def setters(design):
            row = design["blocks"][0]
            support = row["support"]
            return [(row["binders"][0], "type"), (row["arguments"], 0),
                    (support["existentials"][0], "type"),
                    (support["components"][0]["terms"][0], "term"),
                    (support["components"][1], "value"),
                    (support["components"][3]["arguments"], 0),
                    (support["continuation"]["arguments"], 0)]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = self.fixture(root)
            for index in range(7):
                for text in ["ltac:(exact I)", "nat. Definition injected := True."]:
                    design = deepcopy(original)
                    owner, key = setters(design)[index]
                    owner[key] = text
                    with self.subTest(field=index, text=text), self.assertRaisesRegex(ValueError, "command or tactic"):
                        renderer.render_support(design, root, name_prefix="fixture")

    def test_refuses_unknown_bodies_shadowing_and_unapproved_extensions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = self.fixture(root)
            cases = []
            value = deepcopy(original)
            value["blocks"][0]["support"]["body"] = "Proof. exact I. Qed."
            cases.append(value)
            value = deepcopy(original)
            value["blocks"][0]["support"]["existentials"][0]["name"] = "args"
            cases.append(value)
            value = deepcopy(original)
            value["support"]["facts"] = [{"body": "exact I"}]
            cases.append(value)
            value = deepcopy(original)
            value["blocks"][0]["support"]["components"][3]["memory_deltas"] = [{"body": "ignored"}]
            cases.append(value)
            for design in cases:
                with self.subTest(design=design), self.assertRaises(ValueError):
                    renderer.render_support(design, root, name_prefix="fixture")

    def test_refuses_duplicate_continuation_and_wrong_source_bindings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = self.fixture(root)
            value = deepcopy(original)
            value["blocks"][0]["support"]["components"].append({
                "kind": "continuation", "predicate": "Contracts.Fixture.continuationAt",
                "arguments": ["args", "returnAddress args"]})
            with self.assertRaisesRegex(ValueError, "duplicates"):
                renderer.render_support(value, root, name_prefix="fixture")
            value = deepcopy(original)
            value["blocks"][0]["binders"].reverse()
            with self.assertRaisesRegex(ValueError, "parameters differ"):
                renderer.validate_transition_parameters(value["blocks"][0], root)
            (root / "Contracts/Fixture.v").write_text("changed")
            with self.assertRaisesRegex(ValueError, "source hash changed"):
                renderer.render_support(original, root, name_prefix="fixture")

    def test_production_render_needs_no_old_entry_or_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            source = root / "Contracts/Fixture.v"
            original = source.read_text()
            source.write_text("\n".join(line for line in original.splitlines()
                                       if not line.startswith("Definition entry ")) + "\n")
            row = design["blocks"][0]
            row["entry_definition"] = "ZesuSsz.Generated.Fixture.Entries.entry"
            row["resource_predicate"] = row["entry_definition"]
            row["source_hashes"] = {
                "Contracts/Fixture.v": hashlib.sha256(source.read_bytes()).hexdigest()}
            self.assertFalse((root / "ZesuSsz/Generated").exists())
            outputs = renderer.render_support(design, root, name_prefix="fixture")
            self.assertIn("Definition entry", outputs[Path("ZesuSsz/Generated/Fixture/Entries.v")])
            # Existing output content cannot affect input validation.
            target = root / "ZesuSsz/Generated/Fixture/Entries.v"
            target.parent.mkdir(parents=True)
            target.write_text("stale output")
            self.assertEqual(renderer.render_support(design, root, name_prefix="fixture"), outputs)
            self.assertEqual(target.read_text(), "stale output")
            for output in outputs:
                row["source_hashes"][str(output)] = "a" * 64
                with self.assertRaisesRegex(ValueError, "generated output as an input"):
                    renderer.validate_support(design, root, name_prefix="fixture")
                del row["source_hashes"][str(output)]

    def test_mixed_design_validates_and_registers_exactly_supported_rows(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            legacy = deepcopy(design["blocks"][0])
            del legacy["support"]
            legacy["entry_definition"] = "Contracts.Fixture.legacy"
            legacy["resource_predicate"] = legacy["entry_definition"]
            design["blocks"].insert(0, legacy)
            before = {str(p): p.read_bytes() for p in root.rglob("*") if p.is_file()}
            original = deepcopy(design)
            self.assertIsNone(renderer.validate_support(design, root, name_prefix="fixture"))
            self.assertEqual(design, original)
            self.assertEqual(before, {str(p): p.read_bytes() for p in root.rglob("*") if p.is_file()})
            outputs = renderer.render_support(design, root, name_prefix="fixture")
            self.assertTrue(all("legacy" not in text for text in outputs.values()))
            design["support"]["unfold_entries"].append("legacy")
            with self.assertRaisesRegex(ValueError, "each rendered entry once"):
                renderer.validate_support(design, root, name_prefix="fixture")
            design["support"]["unfold_entries"].pop()
            design["blocks"][1]["support"]["body"] = "exact I"
            with self.assertRaises(ValueError):
                renderer.validate_support(design, root, name_prefix="fixture")

    def test_freshness_checks_both_outputs_and_changes_no_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            path = root / "design.json"
            path.write_text(json.dumps(design))
            argv = ["render_support.py", "--function", "fixture", "--design", str(path)]
            with patch.object(renderer, "ROOT", root), patch.object(sys, "argv", argv):
                renderer.main()
                outputs = renderer.render_support(design, root, name_prefix="fixture")
                for relative, source in outputs.items():
                    self.assertEqual((root / relative).read_text(), source)
                with patch.object(sys, "argv", argv + ["--check"]):
                    renderer.main()
                    for relative in outputs:
                        target = root / relative
                        before = target.read_bytes() + b"\n"
                        target.write_bytes(before)
                        with self.assertRaisesRegex(ValueError, "stale"):
                            renderer.main()
                        self.assertEqual(target.read_bytes(), before)
                        target.write_text(outputs[relative])

    def test_rejects_duplicate_json_and_handwritten_overwrite(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON"):
            json.loads('{"support": 1, "support": 2}', object_pairs_hook=renderer.unique_object)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            design = self.fixture(root)
            path = root / "design.json"
            path.write_text(json.dumps(design))
            directory = root / "ZesuSsz/Generated/Fixture"
            directory.mkdir(parents=True)
            target = directory / "Registrations.v"
            target.write_text("(* handwritten *)\n")
            with patch.object(renderer, "ROOT", root), patch.object(sys, "argv", [
                    "render_support.py", "--function", "fixture", "--design", str(path)]):
                with self.assertRaisesRegex(ValueError, "handwritten"):
                    renderer.main()
            self.assertEqual(target.read_text(), "(* handwritten *)\n")
            self.assertFalse((directory / "Entries.v").exists())


if __name__ == "__main__":
    unittest.main()
