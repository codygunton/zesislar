"""Check selected-point coverage and the complete external evidence seal."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import trace_block
from trace_block_stream import build_stream_trace, write_offline_bundle
from test_trace_block import fixture
import test_trace_block_stream as fixture_tools
from test_trace_block_stream import FixtureView


def selected_fixture():
    request, result = fixture("return")
    request["selected_rules"] = ["ReturnRoute"]
    request["entry_descriptors"] = {"ReturnRoute.normalize": {"rule": "ReturnRoute"}}
    result["points"][0]["trigger"].update(client="ReturnRoute.normalize", invocation=1)
    result["coverage"].update(attempted_entries={"ReturnRoute": 2}, actual_triggers={"ReturnRoute": 1},
                              raw_event_index="raw/INDEX.json", requested_trigger_instruction_list=[])
    result["instruction_visits"] = []
    return request, result


class SelectedCoverageTests(unittest.TestCase):
    def test_valid_selected_coverage(self):
        request, result = selected_fixture()
        trace = build_stream_trace(request, FixtureView(result))
        self.assertTrue(trace["completion"]["trace_complete"])

    def test_zero_actual_count_cannot_hide_retained_point(self):
        request, result = selected_fixture()
        for key in ("attempted_entries", "actual_triggers", "entry_events", "captured_events"):
            result["coverage"][key] = {"ReturnRoute": 0}
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_new_counts_cannot_disagree_with_existing_counts(self):
        request, result = selected_fixture()
        result["coverage"]["actual_triggers"] = {"ReturnRoute": 0}
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_actual_cannot_exceed_attempted(self):
        request, result = selected_fixture()
        result["coverage"]["attempted_entries"] = {"ReturnRoute": 0}
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_counts_require_nonnegative_integers(self):
        for value in (True, -1, 0.5, "2"):
            request, result = selected_fixture()
            result["coverage"]["attempted_entries"]["ReturnRoute"] = value
            with self.subTest(value=value):
                self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_selected_trace_rejects_lookup_points(self):
        request, result = selected_fixture()
        result["points"][0]["trigger"]["kind"] = "instruction"
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_selected_trace_rejects_extra_snapshots(self):
        request, result = selected_fixture()
        result["snapshots"]["unselected"] = copy.deepcopy(result["snapshots"]["entry"])
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_selected_trace_rejects_inline_instruction_list(self):
        request, result = selected_fixture()
        result["instruction_visits"] = [{"instruction": "lookup"}]
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_selected_trace_requires_fixed_raw_index_path(self):
        request, result = selected_fixture()
        result["coverage"]["raw_event_index"] = "other.json"
        self.assertFalse(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])

    def test_context_switch_assignments_need_no_observer_counts(self):
        request, result = selected_fixture()
        request["rule_set"].append({"name": "EntryIntro", "enabled": False})
        result["completion"]["final_obligations"]["session"] = trace_block.logical_session_id(request)
        self.assertTrue(build_stream_trace(request, FixtureView(result))["completion"]["trace_complete"])


class SelectedSealTests(unittest.TestCase):
    def setUp(self):
        self.data = fixture_tools.EvidenceMappingTests()
        self.data.setUp()
        self.addCleanup(self.data.doCleanups)
        data = self.data
        capture = data.directory / "capture"
        capture.mkdir()
        data.raw.rename(capture / "evidence")
        data.raw = capture / "evidence"
        data.request_path = data.raw / "REQUEST.json"
        data.operations[0]["path"] = str(data.raw / "start.json")
        data.update_session()
        self.request = json.loads(data.request_path.read_text())
        self.request["selected_rules"] = ["ReturnRoute"]
        self.request["entry_descriptors"] = {"ReturnRoute.normalize": {"rule": "ReturnRoute"}}
        data.request_path.write_bytes(trace_block.json_bytes(self.request))
        data.request_hash = hashlib.sha256(data.request_path.read_bytes()).hexdigest()
        data.trace["coverage"].update(attempted_entries={"ReturnRoute": 2}, actual_triggers={"ReturnRoute": 1},
                                      raw_event_index="raw/INDEX.json", requested_trigger_instruction_list=[])
        data.trace["instruction_visits"] = []
        data.trace["points"][0]["trigger"].update(client="ReturnRoute.normalize", invocation=1)
        events = []
        for invocation in (1, 2):
            path = data.raw / ("events/process-42/event-%08d.json" % invocation)
            path.write_bytes(trace_block.json_bytes({"kind": "native-entry", "rule": "ReturnRoute.normalize",
                                                     "invocation": invocation, "trial": False}))
            events.append({"path": str(path.relative_to(data.raw)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        (data.raw / "EVENT-SEAL.json").write_bytes(trace_block.json_bytes({"streams": events}))
        self.index = {"session": data.trace["session"]["id"], "events": events,
                      "attempted_entries": [{"rule": "ReturnRoute", "client": "ReturnRoute.normalize",
                        "invocation": i + 1, "classification": "actual-trigger" if i == 0 else "non-trigger",
                        "event": event} for i, event in enumerate(events)], "instruction_lookups": []}
        self.index_path = data.directory / "INDEX.json"
        self.root_seal = data.directory / "RAW-SEAL.json"
        self.refresh_index()
        self.refresh_seal()

    def refresh_index(self):
        self.index_path.write_bytes(trace_block.json_bytes(self.index))
        self.index_hash = hashlib.sha256(self.index_path.read_bytes()).hexdigest()

    def refresh_seal(self):
        root = self.data.raw.parent
        files = [{"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                  "bytes": path.stat().st_size} for path in sorted(root.rglob("*")) if path.is_file()]
        self.root_seal.write_bytes(trace_block.json_bytes({"root": str(root),
            "session_id": self.data.trace["session"]["id"], "files": files}))
        self.seal_hash = hashlib.sha256(self.root_seal.read_bytes()).hexdigest()

    def write(self):
        data = self.data
        return write_offline_bundle(data.out, data.trace, data.raw,
            expected_session_sha256=data.expected, request_path=data.request_path,
            expected_request_sha256=data.request_hash, raw_index_path=self.index_path,
            expected_raw_index_sha256=self.index_hash, raw_seal_path=self.root_seal,
            expected_raw_seal_sha256=self.seal_hash)

    def test_selected_index_and_complete_raw_seal_are_bound(self):
        hashes = self.write()
        self.assertEqual(hashes["raw/INDEX.json"], self.index_hash)
        self.assertEqual(hashes["RAW-SEAL.json"], self.seal_hash)
        mapping = json.loads((self.data.out / "EVIDENCE-MAP.json").read_text())
        self.assertEqual(mapping["raw_verification"]["verified_events"], 2)
        self.assertEqual(mapping["raw_verification"]["complete_raw_seal"]["verified_files"], 8)
        self.assertEqual((self.data.out / "raw/INDEX.json").read_bytes(), self.index_path.read_bytes())

    def test_changed_event_in_other_process_stream_rejects(self):
        other = self.data.raw / "events/process-99/event-00000001.json"
        other.parent.mkdir()
        other.write_text("initial")
        self.refresh_seal()
        other.write_text("changed")
        with self.assertRaisesRegex(ValueError, "raw evidence reference changed"):
            self.write()

    def test_unsealed_other_process_file_rejects(self):
        other = self.data.raw / "events/process-99/event-00000001.json"
        other.parent.mkdir()
        other.write_text("unsealed")
        with self.assertRaisesRegex(ValueError, "file set differs"):
            self.write()

    def test_wrong_raw_classification_counts_rejects(self):
        self.index["attempted_entries"][1]["classification"] = "actual-trigger"
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "counts differ"):
            self.write()

    def test_retained_point_must_match_index_identity(self):
        self.data.trace["points"][0]["trigger"]["invocation"] = 2
        with self.assertRaisesRegex(ValueError, "retained points differ"):
            self.write()

    def test_missing_selected_index_rejects(self):
        with self.assertRaisesRegex(ValueError, "external raw index"):
            write_offline_bundle(self.data.out, self.data.trace, self.data.raw,
                expected_session_sha256=self.data.expected, request_path=self.data.request_path,
                expected_request_sha256=self.data.request_hash)

    def test_unknown_classification_cannot_claim_complete(self):
        self.index["attempted_entries"][1]["classification"] = "unknown"
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "Unknown raw trigger"):
            self.write()

    def test_legacy_index_files_can_be_absent_after_controller_stop(self):
        (self.data.raw / "EVENT-INDEX.json").unlink()
        (self.data.raw / "EVENT-SEAL.json").unlink()
        self.refresh_seal()
        self.write()

    def test_inconsistent_legacy_event_seal_rejects(self):
        (self.data.raw / "EVENT-SEAL.json").write_text('{"streams": []}')
        self.refresh_seal()
        with self.assertRaisesRegex(ValueError, "existing raw event seal differs"):
            self.write()

    def test_external_index_session_must_match(self):
        self.index["session"] = "wrong-session"
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "different logical session"):
            self.write()

    def test_complete_seal_session_must_match(self):
        value = json.loads(self.root_seal.read_text())
        value["session_id"] = "wrong-session"
        self.root_seal.write_bytes(trace_block.json_bytes(value))
        self.seal_hash = hashlib.sha256(self.root_seal.read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "different root or session"):
            self.write()


if __name__ == "__main__":
    unittest.main()
