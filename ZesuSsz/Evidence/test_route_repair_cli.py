"""Exercise the acceptance command without native proof execution."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_decode_item_route_repair import (
    ARRAY_STORE_IDENTITY, ROOT, actual_groups, closed_groups, dry_run,
)
from test_route_repair_linked_evidence import SyntheticEvidence


class AcceptanceCommandTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.fixture = SyntheticEvidence(self.root)
        self.index = self.root / "index.json"
        self.index.write_text(json.dumps(self.fixture.index))

    def command(self, *arguments):
        return subprocess.run([sys.executable, str(ROOT / "ZesuSsz/Evidence/check_decode_item_route_repair.py"),
                               "--workspace", str(self.root), *arguments],
                              capture_output=True, text=True)

    def test_stub_dry_run_reports_all_missing_certificates(self):
        stub = self.fixture.modules[self.fixture.bundle["repair_identity"]["module"]]["source"]["path"]
        result = self.command("--index", str(self.index), "--dry-run", "--switch-source", stub)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["accepted"])
        self.assertFalse(report["runtime_activation_checked"])
        self.assertEqual(len(report["missing_certificates"]), 13)
        self.assertEqual(report["checked_native_cases"], [])
        self.assertEqual(report["workspace"], str(self.root))

    def test_complete_fictional_bundle_uses_the_explicit_workspace(self):
        bundle = self.root / "bundle.json"
        bundle.write_text(json.dumps(self.fixture.bundle))
        result = self.command("--index", str(self.index), "--results", str(bundle))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)["native_cases"]), 9)

    def test_complete_fictional_bundle_stays_nonaccepting_in_dry_mode(self):
        report = dry_run(self.fixture.index, self.root, bundle=self.fixture.bundle)
        self.assertFalse(report["accepted"])
        self.assertEqual(len(report["checked_native_cases"]), 9)
        self.assertEqual(report["missing_certificates"], [])

    def test_missing_loop_application_stays_incomplete_in_dry_mode(self):
        for count in (0, 1):
            with self.subTest(count=count):
                bundle = copy.deepcopy(self.fixture.bundle)
                bundle["loop_negative_controls"] = bundle["loop_negative_controls"][:count]
                report = dry_run(self.fixture.index, self.root, bundle=bundle)
                self.assertFalse(report["accepted"])
                self.assertFalse(report["runtime_activation_checked"])
                for case in self.fixture.index["loop_negative_controls"]:
                    self.assertIn("control: " + case["control_id"], report["missing_certificates"])

    def test_altered_loop_id_stays_incomplete_in_dry_mode(self):
        self.fixture.bundle["loop_negative_controls"][0]["control_id"] = "altered"
        report = dry_run(self.fixture.index, self.root, bundle=self.fixture.bundle)
        self.assertFalse(report["accepted"])
        self.assertEqual(report["checked_native_cases"], [])

    def test_invalid_complete_bundle_fails_in_dry_mode(self):
        self.fixture.bundle["native_cases"][0].pop("verification")
        with self.assertRaises(KeyError):
            dry_run(self.fixture.index, self.root, bundle=self.fixture.bundle)

    def test_stub_override_cannot_enter_real_acceptance(self):
        stub = self.fixture.modules[self.fixture.bundle["repair_identity"]["module"]]["source"]["path"]
        result = self.command("--index", str(self.index), "--switch-source", stub)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires dry mode", result.stderr)

    def test_entry_normalization_dry_run_is_unsupported(self):
        result = self.command("--dry-run", "--entry-normalization")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Dry mode does not support entry normalization", result.stderr)

    def test_array_store_uses_the_same_dry_command(self):
        stub = self.root / "ArrayStoreSelection.v"
        stub.write_text("(* Uncompiled interface stub. *)\n" + ARRAY_STORE_IDENTITY["class"] + " " +
                        ARRAY_STORE_IDENTITY["instance"] + "\n")
        result = self.command("--workspace", str(ROOT), "--array-store", "--dry-run",
                              "--switch-source", str(stub))
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["accepted"])
        self.assertFalse(report["runtime_activation_checked"])
        self.assertEqual(report["repair_identity"], ARRAY_STORE_IDENTITY)
        self.assertEqual(len(report["missing_certificates"]), 8)
        self.assertTrue(report["pending_inventory"])


class KernelGroupTests(unittest.TestCase):
    def setUp(self):
        goal = {"info": {"id": 1}, "ty": "True",
                "hyps": [{"names": ["IPM_JANNO"], "ty": "nat", "def": "HIDDEN"}]}
        self.groups = {"goals": [copy.deepcopy(goal)],
                       "stack": [[[copy.deepcopy(goal)], [copy.deepcopy(goal)]]],
                       "shelf": [copy.deepcopy(goal)], "given_up": [copy.deepcopy(goal)]}
        kernel = copy.deepcopy(self.groups)
        for group in [kernel["goals"], *kernel["stack"][0], kernel["shelf"], kernel["given_up"]]:
            for full in group:
                full["hyps"][0].update(ty="Datatypes.nat", **{"def": "S O"})
        self.groups["kernel_groups"] = kernel
        self.groups["local_definition_export"] = {"original_state_preserved": True}

    def test_all_groups_and_kernel_definitions_are_checked_separately(self):
        actual_groups(self.groups)
        self.assertEqual(self.groups["goals"][0]["hyps"][0]["def"], "HIDDEN")
        self.assertEqual(self.groups["kernel_groups"]["goals"][0]["hyps"][0]["def"], "S O")

    def test_hidden_or_truncated_kernel_definition_rejects_each_group(self):
        for key in ("goals", "stack", "shelf", "given_up"):
            for body in ("HIDDEN", "S (...)"):
                groups = copy.deepcopy(self.groups)
                goal = groups["kernel_groups"][key][0]
                if key == "stack":
                    goal = goal[1][0]
                goal["hyps"][0]["def"] = body
                with self.subTest(key=key, body=body), self.assertRaises(ValueError):
                    actual_groups(groups)

    def test_changed_kernel_context_or_group_count_rejects(self):
        groups = copy.deepcopy(self.groups)
        groups["kernel_groups"]["shelf"] = []
        with self.assertRaisesRegex(ValueError, "count differs"):
            actual_groups(groups)
        groups = copy.deepcopy(self.groups)
        groups["kernel_groups"]["goals"][0]["hyps"][0]["names"] = ["other"]
        with self.assertRaisesRegex(ValueError, "ordered context"):
            actual_groups(groups)

    def test_metadata_cannot_hide_open_kernel_groups(self):
        with self.assertRaisesRegex(ValueError, "remains open"):
            closed_groups(self.groups)
        empty = {key: [] for key in ("goals", "stack", "shelf", "given_up")}
        closed_groups({**empty, "kernel_groups": copy.deepcopy(empty),
                       "local_definition_export": {"original_state_preserved": True}})
        with self.assertRaisesRegex(ValueError, "lacks its kernel"):
            actual_groups({**empty, "local_definition_export": {}})


if __name__ == "__main__":
    unittest.main()
