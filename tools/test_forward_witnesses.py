"""Check pass-output integration without supplying a target slot table."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from functools import partial
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).parent / "block"))
sys.path.insert(0, str(Path(__file__).parent))
import test_witness_data as fixtures
from forward_witnesses import forward_witness_data
from witness_data import resolved_witness_data


def binding(path):
    return dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest())


class ForwardWitnessTests(unittest.TestCase):
    def fixture(self, root):
        fixtures.WitnessDataTests().fixture(root)
        source = root / "Source.v"
        source.write_text(source.read_text().replace('RVal_Bits after.', 'RVal_Bits after ∗ (10) ↦ₘ∗ [].') +
            'Definition template (loaded : bv 64%N) : iProp Sigma := "r1" ↦ᵣ RVal_Bits loaded.\n')
        facts = root / "Facts.v"
        facts.write_text('Definition source_parameters (count : Z) : Prop := 0 <= count.\n')
        report = root / "Pass.json"
        fact = dict(source=dict(original_term='source_parameters (0)'), expansion=[
            dict(declaration="source_parameters", source=dict(module="Support.Facts", **binding(facts)))])
        report.write_text(json.dumps(dict(definitions=[dict(parameters=[], existentials=[], lets=[],
            resources=[dict(kind="register", name="r1", value="RVal_Bits before"), dict(kind="register", name="r2", value="RVal_Bits after"), dict(kind="byte_array", address="(10)", value="[]")], execution_facts=[fact])])))
        forward = dict(name="pass_data", report=binding(report), pointer="/definitions/0",
            source_assertion=dict(**binding(source), declaration="source"),
            declaration_sources=[dict(module="Support.Facts", **binding(facts))],
            resource_templates=[dict(**binding(source), declaration="template")])
        return fixtures.WitnessDataTests.target.replace("10 ↦ₘ∗", "(10) ↦ₘ∗"), forward

    def test_emits_every_slot_from_pass_arguments_and_owners(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target, forward = self.fixture(root)
            self.assertNotIn("slots", forward)
            result = forward_witness_data(forward, target, "target", [], root / "out.v")
            emitted = resolved_witness_data(target, "target", result["data"], source_texts=result["source_texts"])
            self.assertEqual([slot["name"] for slot in result["data"]["slots"]],
                             ["count", "frame", "loaded", "first", "second"])
            self.assertEqual(emitted["registers"], [("r1", 64), ("r2", 64)])
            self.assertEqual(result["data"]["slots"][1]["source"]["kind"], "array")
            self.assertEqual(result["certificates"][0]["candidates"][0]["parameter"], "count")
            self.assertNotIn("Proof", result["prefix"])

    def test_refuses_missing_conflicting_or_unbound_source_data(self):
        for defect in ("argument", "conflict", "type", "role", "owner", "hash", "source_value", "source_address", "source_payload", "source_fraction"):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                target, forward = self.fixture(root)
                path = Path(forward["report"]["path"])
                report = json.loads(path.read_text())
                row = report["definitions"][0]
                if defect == "argument":
                    row["execution_facts"] = []  # Target count=0 cannot supply data.
                elif defect == "conflict":
                    other = deepcopy(row["execution_facts"][0])
                    other["source"]["original_term"] = "source_parameters (1)"
                    row["execution_facts"].append(other)
                elif defect == "type":
                    facts = root / "Facts.v"
                    facts.write_text(facts.read_text() + "Definition other_parameters (count : nat) : Prop := count = count.\n")
                    current = binding(facts)
                    forward["declaration_sources"][0].update(current)
                    row["execution_facts"][0]["expansion"][0]["source"].update(current)
                    other = deepcopy(row["execution_facts"][0])
                    other["source"]["original_term"] = "other_parameters (0)"
                    other["expansion"][0]["declaration"] = "other_parameters"
                    row["execution_facts"].append(other)
                elif defect.startswith("source_"):
                    path2 = root / "Other.v"
                    text = Path(forward["source_assertion"]["path"]).read_text()
                    if defect == "source_value":
                        text = text.replace("RVal_Bits before", "RVal_Bits changed")
                    elif defect == "source_address":
                        text = text.replace("(10) ↦ₘ∗", "(11) ↦ₘ∗")
                    elif defect == "source_payload":
                        text = text.replace("↦ₘ∗ []", "↦ₘ∗ [BV 8%N 0%Z]")
                    else:
                        text = text.replace("↦ₘ∗ []", "↦ₘ∗{q} []")
                    path2.write_text(text)
                    forward["source_assertion"] = dict(**binding(path2), declaration="source")
                elif defect == "role":
                    forward["resource_templates"] = []  # Target loaded=first is not a source role.
                elif defect == "owner":
                    row["resources"].pop()
                path.write_text(json.dumps(report))
                forward["report"] = binding(path)
                if defect == "hash":
                    forward["report"]["sha256"] = "0" * 64
                with self.assertRaises(ValueError):
                    forward_witness_data(forward, target, "target", [], root / "out.v")

    def test_generate_block_design_main_consumes_forward_metadata(self):
        from tools import test_generate_block_design as design_fixture
        import forward_witnesses

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inventory, profile = design_fixture.FunctionDesignTests().support_fixture(root)
            target, forward = self.fixture(root)
            owner, inputs = root / "Contracts/Target.v", root / "Contracts/Inputs.v"
            owner.write_text(target)
            inputs.write_text("Class Mapping (key Input Witness : Type) := {}.")
            module = dict(module="ZesuSsz.Generated.Fixture.PassMappings", scopes=["Z_scope"],
                imports=[dict(mode="import", module="Contracts.Target"), dict(mode="import", module="Contracts.Inputs")],
                source_hashes={str(path.relative_to(root)): binding(path)["sha256"] for path in (owner, inputs)},
                mappings=[dict(name="pass_mapping", iris_contexts=[], parameters=[dict(name="K", type="iProp Sigma", implicit=False)],
                    **{"class": "Contracts.Inputs.Mapping"}, source=dict(predicate="Contracts.Target.target", arguments=["K"]),
                    locality="export", forward=forward)])
            profile["design"]["support"]["witness_mappings"] = [module]
            inventory_path, profile_path, output = (root / name for name in ("inventory.json", "profile.json", "design.json"))
            inventory_path.write_text(json.dumps(inventory))
            profile_path.write_text(json.dumps(profile))
            generator = design_fixture.generator
            command = ["generate_block_design.py", "--function", "fixture", "--inventory", str(inventory_path),
                       "--profile", str(profile_path), "--output", str(output)]
            # Inject only the temporary filesystem root. The real CLI, builder,
            # CFG checks, source checks, renderer, and forward producer all run.
            actual_build = partial(generator.build, root=root)
            with patch.object(generator.sys, "argv", command), patch.object(generator, "build", wraps=actual_build), \
                    patch.object(forward_witnesses, "forward_witness_data", wraps=forward_witness_data) as produced:
                generator.main()
            self.assertEqual(produced.call_count, 1)
            result = json.loads(output.read_text())
            self.assertEqual(result["support"]["witness_mappings"][0]["mappings"][0]["forward"], forward)


if __name__ == "__main__":
    unittest.main()
