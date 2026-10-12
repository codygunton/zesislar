"""Exercise array-store acceptance with fictional linked evidence and mutations."""
import json
from pathlib import Path
import tempfile
import unittest

from check_decode_item_route_repair import (
    ARRAY_STORE_CONTROLS as CONTROLS, ARRAY_STORE_IDENTITY as IDENTITY,
    ARRAY_STORE_INDEX as INDEX, ARRAY_STORE_SITES as SITES,
    array_store_acceptance as acceptance, array_store_missing as missing,
    array_store_schema as schema,
    dry_run,
)
from test_route_repair_linked_evidence import SyntheticEvidence


class ArrayStoreAcceptanceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.fixture = SyntheticEvidence(self.root, sites=SITES, repair_identity=IDENTITY,
                                         control_names=["s152a_correct_selection", "s152b_correct_selection"])
        self.index = self.fixture.index
        self.bundle = self.fixture.bundle
        self.index.update({"version": 1, "repair_identity": {**IDENTITY, "status": "reserved"},
                           "controls": []})
        for case, record in zip(self.index["cases"], self.bundle["native_cases"]):
            case.update({"source_root": self.bundle["candidate_delta"]["base_root"],
                         "capture_scope": {
                             "approved": self.fixture.modules["ZesuSsz.Automation.Approved"]["source"],
                             "hints": self.fixture.modules["ZesuSsz.Compliance.DecodeItemHints"]["source"]},
                         "retained_captures": [case["capture"]],
                         "capture_provenance": self.fixture.write("provenance/" + case["block"] + ".json", {})})
            record["captured_state_provenance"] = {key: case[key] for key in
                ("capture", "native_source", "source_root", "capture_scope", "capture_provenance", "retained_captures")}
        for label, record in zip(CONTROLS, self.bundle["rejections"]):
            theorem = record["theorem"]
            statement = "Lemma " + theorem + " : True."
            reviewed = self.fixture.write(label + "-review.json", {"synthetic": True})
            self.index["controls"].append({"id": label, "theorem": theorem,
                "source": self.index["control_module"],
                "statement": self.fixture.write(label + ".txt", statement),
                "reviewed_certificate": reviewed,
                "eligible_as_exact_native_selection_control": True})
            record.update({"control_id": label, "reviewed_certificate": reviewed,
                "eligible_as_exact_native_selection_control": True})

    def check(self):
        return acceptance(self.index, self.bundle, self.root)

    def test_complete_fictional_bundle(self):
        self.assertEqual([row["block"] for row in self.check()], SITES)

    def test_complete_fictional_dry_bundle_stays_nonaccepting(self):
        report = dry_run(self.index, self.root, bundle=self.bundle, array_store=True)
        self.assertFalse(report["accepted"])
        self.assertEqual([row["block"] for row in report["checked_native_cases"]], SITES)
        self.assertEqual(report["missing_certificates"], [])

    def test_dry_mode_keeps_the_actual_control_requirements(self):
        self.bundle["rejections"][0].pop("compilation")
        with self.assertRaises(KeyError):
            dry_run(self.index, self.root, bundle=self.bundle, array_store=True)

    def test_placeholder_cannot_accept(self):
        self.index["repair_identity"] = {**dict.fromkeys(IDENTITY), "status": "placeholder"}
        with self.assertRaisesRegex(ValueError, "reserved switch identity"):
            self.check()

    def test_missing_correct_selection_certificate(self):
        self.index["controls"][1]["reviewed_certificate"] = None
        with self.assertRaisesRegex(ValueError, "S152b"):
            self.check()

    def test_conflict_controls_cannot_replace_selection(self):
        self.bundle["rejections"][0]["control_id"] = "S119"
        with self.assertRaisesRegex(ValueError, "S152"):
            self.check()

    def test_pure_candidate_control_is_rejected(self):
        self.index["controls"][0]["eligible_as_exact_native_selection_control"] = False
        with self.assertRaisesRegex(ValueError, "exact selection eligibility"):
            self.check()

    def test_unspecified_control_eligibility_is_rejected(self):
        self.index["controls"][0].pop("eligible_as_exact_native_selection_control")
        with self.assertRaisesRegex(ValueError, "exact selection eligibility"):
            self.check()

    def test_wrong_capture_state_provenance(self):
        self.bundle["native_cases"][0]["captured_state_provenance"]["source_root"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "captured state"):
            self.check()

    def test_missing_native_certificate(self):
        self.bundle["native_cases"].pop()
        with self.assertRaisesRegex(ValueError, "six actual"):
            self.check()

    def test_different_control_statement(self):
        self.index["controls"][0]["statement"] = self.fixture.write("wrong.txt", "Lemma wrong : False.")
        with self.assertRaisesRegex(ValueError, "control statement changed"):
            self.check()

    def test_wrong_reviewed_control(self):
        self.bundle["rejections"][0]["reviewed_certificate"] = self.fixture.write("unrelated.json", {})
        with self.assertRaisesRegex(ValueError, "reviewed certificate"):
            self.check()

    def test_missing_control_compilation(self):
        self.bundle["rejections"][0].pop("compilation")
        with self.assertRaises(KeyError):
            self.check()

    def test_changed_hint_scope_is_rejected(self):
        self.bundle["native_cases"][0]["captured_state_provenance"] = {
            **self.bundle["native_cases"][0]["captured_state_provenance"],
            "capture_scope": {"hints": "a different scope"}}
        with self.assertRaisesRegex(ValueError, "captured state"):
            self.check()

    def test_inventory_schema_stays_nonaccepting(self):
        index = json.loads(INDEX.read_text())
        schema(index)
        self.assertTrue(missing(index))
        with self.assertRaisesRegex(ValueError, "dependencies are missing"):
            acceptance(index, {})

    def test_vos_is_rejected(self):
        record = self.bundle["native_cases"][0]
        position = record["compilation"]["call"]
        self.fixture.mutate_file(self.bundle["sessions"][0]["raw_calls"],
                                 lambda calls: calls[position]["arguments"].update(mode="vos"))
        with self.assertRaisesRegex(ValueError, "full compilation"):
            self.check()

    def test_unavailable_groups_are_rejected(self):
        record = self.bundle["native_cases"][0]
        position = record["proof_trace"]["exports"][-1]
        def mutation(calls):
            result = calls[position]["raw_response"]["structuredContent"]
            self.fixture.mutate_file(result, lambda groups: groups.update(stack=None))
            result["bytes"] = Path(result["path"]).stat().st_size
        self.fixture.mutate_file(self.bundle["sessions"][0]["raw_calls"], mutation)
        with self.assertRaises(ValueError):
            self.check()


if __name__ == "__main__":
    unittest.main()
