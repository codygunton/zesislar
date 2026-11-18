"""Check complete witness emission and pre-proof refusal boundaries."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from witness_data import (declared_witness_slots, resolved_witness_data, _array_owners,
                          witness_profile_metadata, product)
from entry_bindings import normalize_type
from render_support import witness_mapping_source


class WitnessDataTests(unittest.TestCase):
    def test_explicit_full_array_definition_preserves_source(self):
        text = 'Definition owner : iProp Sigma := isla.ghost_state.mem_mapsto_array_def ((base)%Z) (DfracOwn 1) (payload).'
        owners = _array_owners(text, 'owner')
        self.assertEqual(len(owners), 1)
        self.assertEqual(owners[0]['address'], ['base'])
        self.assertEqual(owners[0]['payload'], ['payload'])
        self.assertEqual(owners[0]['fraction']['term'], 'DfracOwn 1')
        self.assertEqual(owners[0]['fraction']['source'], '(DfracOwn 1)')

    def test_explicit_array_definition_refuses_other_fractions(self):
        for fraction in ['DfracOwn 2', 'DfracOwn q', 'DfracDiscarded', 'DfracOwn (1 / 2)', 'DfracOwn']:
            with self.subTest(fraction=fraction), self.assertRaisesRegex(ValueError, 'unsupported explicit fraction'):
                _array_owners('Definition owner : iProp Sigma := isla.ghost_state.mem_mapsto_array_def (base) (' + fraction + ') (payload).', 'owner')

    target = '''Definition target (K : iProp Sigma) : iProp Sigma :=
      ((∃ (unused : Z) (count : Z) (frame : list (bv 8%N))
          (loaded first second : bv 64%N),
       "r1" ↦ᵣ RVal_Bits first ∗ "r2" ↦ᵣ RVal_Bits second ∗
       10 ↦ₘ∗ frame ∗ ⌜count = 0 /\\ loaded = first⌝) ∗ K)%I.'''

    def fixture(self, root):
        source = root / "Source.v"
        source.write_text('''Definition source : iProp Sigma :=
          "r1" ↦ᵣ RVal_Bits before ∗ "r2" ↦ᵣ RVal_Bits after.
Definition choice : Z := 0%Z.
Definition bytes : list (bv 8%N) := [].
''')
        def provenance(name):
            return dict(path=str(source), sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                        declaration=name)
        def expression(name, kind, term, origin):
            return dict(name=name, type=kind, value=term,
                        source=dict(kind="expression", provenance=provenance(origin)))
        def register(name, reg):
            return dict(name=name, type="bv 64%N", value=None,
                        source=dict(kind="register", register=reg, width=64,
                                    provenance=provenance("source")))
        return dict(name="data", parameters=[], source_assertion=provenance("source"),
                    value_sources=[provenance("choice"), provenance("bytes")], slots=[
            expression("count", "Z", "0%Z", "choice"),
            expression("frame", "list (bv 8%N)", "[]", "bytes"),
            register("loaded", "r1"), register("first", "r1"), register("second", "r2")])

    def test_complete_slots_and_single_reversal(self):
        with tempfile.TemporaryDirectory() as directory:
            value = self.fixture(Path(directory))
            result = resolved_witness_data(self.target, "target", value)
            self.assertEqual([slot["name"] for slot in result["declaration_order"]],
                             ["count", "frame", "loaded", "first", "second"])
            self.assertEqual([(slot["name"], normalize_type(slot["type"])) for slot in result["internal_order"]],
                             [(slot["name"], normalize_type(slot["type"])) for slot in reversed(result["declaration_order"])])
            self.assertEqual(result["registers"], [("r1", 64), ("r2", 64)])
            self.assertEqual([row["name"] for row in result["vacuous"]], ["unused"])
            self.assertIn("fst (snd source_words)", result["source"])
            self.assertNotIn("Proof", result["source"])

    def test_refuses_missing_extra_wrong_type_and_equal_typed_order(self):
        for defect in ("missing", "extra", "type", "order", "internal_order"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                value = self.fixture(Path(directory))
                if defect == "missing":
                    value["slots"].pop(1)  # An owned frame is still a required slot.
                elif defect == "extra":
                    value["slots"].append(deepcopy(value["slots"][-1]))
                elif defect == "type":
                    value["slots"][0]["type"] = "nat"
                elif defect == "order":
                    value["slots"][-2:] = reversed(value["slots"][-2:])
                else:
                    value["slots"].reverse()
                with self.assertRaises(ValueError):
                    resolved_witness_data(self.target, "target", value)

    def test_refuses_missing_source_or_invented_value(self):
        for defect in ("provenance", "hash", "register", "value", "expression", "width"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                value = self.fixture(Path(directory))
                if defect == "provenance":
                    value["slots"][0]["source"]["provenance"] = None
                elif defect == "hash":
                    value["slots"][0]["source"]["provenance"]["sha256"] = "0" * 64
                elif defect == "register":
                    value["slots"][-1]["source"]["register"] = "r1"
                elif defect == "value":
                    value["slots"][-1]["value"] = "before"
                elif defect == "expression":
                    value["slots"][0]["value"] = "1%Z"
                else:
                    value["slots"][-1]["source"]["width"] = 32
                with self.assertRaises(ValueError):
                    resolved_witness_data(self.target, "target", value)

    def test_refuses_shadowing_instead_of_guessing_vacuity(self):
        with self.assertRaisesRegex(ValueError, "nested binders"):
            declared_witness_slots(self.target.replace("count = 0", "(let count := 0 in count) = 0"), "target")

    def test_frozen_mapping_metadata_refuses_same_type_slot_swap(self):
        slots = declared_witness_slots(self.target, "target")["remaining"]
        supplied = deepcopy(slots)
        first = next(i for i, slot in enumerate(supplied) if slot["name"] == "first")
        second = next(i for i, slot in enumerate(supplied) if slot["name"] == "second")
        supplied[first], supplied[second] = supplied[second], supplied[first]
        with self.assertRaisesRegex(ValueError, "slot order"):
            witness_profile_metadata(self.target, "target", supplied, name="profile",
                typed="", entry="target K", witness_type=product([s["type"] for s in slots]),
                mapping_fragment="unchanged emitted mapping")

    def test_frozen_phase_uses_authenticated_original_metadata(self):
        slots = declared_witness_slots(self.target, "target")["remaining"][::2]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "emission.json"
            path.write_text(json.dumps({"phase": [s["name"] for s in slots]}))
            phase = {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                     "pointer": "/phase"}
            arguments = dict(name="profile", typed="", entry="target K",
                             witness_type=product([s["type"] for s in slots]),
                             mapping_fragment="unchanged mapping", phase_metadata=phase)
            result = witness_profile_metadata(self.target, "target", slots, **arguments)
            self.assertEqual(result["source_slots"], slots)
            self.assertEqual(result["phase_metadata"], phase)
            path.write_text(json.dumps({"phase": list(reversed([s["name"] for s in slots]))}))
            with self.assertRaisesRegex(ValueError, "metadata changed"):
                witness_profile_metadata(self.target, "target", slots, **arguments)
            phase["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "declaration order"):
                witness_profile_metadata(self.target, "target", slots, **arguments)

    def test_frozen_mapping_metadata_keeps_fragment_hash(self):
        slots = declared_witness_slots(self.target, "target")["remaining"]
        fragment = "unchanged emitted mapping"
        result = witness_profile_metadata(self.target, "target", slots, name="profile",
            typed="", entry="target K", witness_type=product([s["type"] for s in slots]),
            mapping_fragment=fragment)
        self.assertEqual(result["mapping_fragment_sha256"], hashlib.sha256(fragment.encode()).hexdigest())
        self.assertFalse(result["runtime_names_recovered"])

    def test_mapping_renderer_checks_complete_data_before_registration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            data = self.fixture(root)
            target, inputs = root / "Contracts/Target.v", root / "Support/Inputs.v"
            target.parent.mkdir()
            inputs.parent.mkdir()
            target.write_text(self.target)
            inputs.write_text("Class Mapping (key : Type) (Input Witness : Type) := {}.")
            fields = dict(source_hashes={str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                                         for path in (target, inputs)})
            mapping = dict(name="mapping", iris_contexts=[], parameters=[
                dict(name="K", type="iProp Sigma", implicit=False)],
                **{"class": "Support.Inputs.Mapping"},
                source=dict(predicate="Contracts.Target.target", arguments=["K"]),
                locality="export", data=data)
            text = witness_mapping_source(mapping, fields, root, {"Support.Inputs", "Contracts.Target"})
            self.assertLess(text.index("Definition data"), text.index("Instance mapping"))
            self.assertIn("zesu_witness_mapping := data", text)
            self.assertNotIn("Proof", text)
            self.assertIn("ZesuEntryWitnessSourceProfile", text)
            self.assertIn("ZesuEntryWitnessDataProfile", text)
            mapping["data"]["slots"].pop(1)
            with self.assertRaisesRegex(ValueError, "slot count"):
                witness_mapping_source(mapping, fields, root, {"Support.Inputs", "Contracts.Target"})
            del mapping["data"]
            mapping.update(input_type="unit", witness_type="unit", input="ZesuWitnessUnit", mapping="I")
            with self.assertRaisesRegex(ValueError, "complete source-resolved"):
                witness_mapping_source(mapping, fields, root, {"Support.Inputs", "Contracts.Target"})

    def test_refuses_dependent_or_shadowed_telescope(self):
        with self.assertRaisesRegex(ValueError, "dependent product"):
            declared_witness_slots(self.target.replace("frame : list (bv 8%N)", "frame : vector (bv 8%N) count"), "target")
        with self.assertRaisesRegex(ValueError, "shadows"):
            declared_witness_slots(self.target.replace("(K : iProp Sigma)", "(K : iProp Sigma) (count : Z)"), "target")

    def test_array_value_comes_from_exact_same_owner(self):
        for defect in (None, "address", "duplicate", "value"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                data = self.fixture(root)
                source = root / "Array.v"
                base = "11" if defect == "address" else "10"
                owners = "(10%Z) ↦ₘ∗ [] ∗ " if defect == "duplicate" else ""
                source.write_text('Definition array : iProp Sigma := "r1" ↦ᵣ RVal_Bits before ∗ "r2" ↦ᵣ RVal_Bits after ∗ ' + owners + '(' + base + '%Z) ↦ₘ∗ [].')
                frame = data["slots"][1]
                frame["source"] = dict(kind="array", provenance=dict(
                    path=str(source), sha256=hashlib.sha256(source.read_bytes()).hexdigest(), declaration="array"))
                data["source_assertion"] = frame["source"]["provenance"]
                for slot in data["slots"]:
                    if slot["source"]["kind"] == "register":
                        slot["source"]["provenance"] = data["source_assertion"]
                frame["value"] = "[]" if defect == "value" else None
                target = self.target.replace("10 ↦ₘ∗", "(10) ↦ₘ∗")
                if defect:
                    with self.assertRaises(ValueError):
                        resolved_witness_data(target, "target", data)
                else:
                    result = resolved_witness_data(target, "target", data)
                    self.assertIn("(([]),", result["source"])

    def test_refuses_target_or_pure_conclusion_as_provenance(self):
        for role in ("owner", "value", "pure"):
            with self.subTest(role=role), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                data = self.fixture(root)
                path = root / "Target.v"
                path.write_text(self.target)
                reference = dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest(), declaration="target")
                if role == "owner":
                    data["source_assertion"] = reference
                else:
                    if role == "pure":
                        path.write_text("Definition pure_fact : Prop := 0%Z = 0%Z.")
                        reference.update(sha256=hashlib.sha256(path.read_bytes()).hexdigest(), declaration="pure_fact")
                    data["value_sources"].append(reference)
                    data["slots"][0]["source"]["provenance"] = reference
                with self.assertRaisesRegex(ValueError, "target declaration|pure conclusion"):
                    resolved_witness_data(self.target, "target", data)


if __name__ == "__main__":
    unittest.main()
