"""Check bounded raw metadata reads and complete native-entry association."""

import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
from trace_block_event_identity import read_event_identity
from trace_block_seal import verify_raw_evidence
import trace_block
import test_trace_block_selected as selected_tests


class EventIdentityReaderTests(unittest.TestCase):
    def read(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "event.json"
            path.write_text(text, encoding="utf-8")
            return read_event_identity(path)

    def test_payload_fields_cannot_substitute_top_level_identity(self):
        payload = {"capture": {"kind": "native-entry", "rule": "wrong", "invocation": 19,
                               "trial": True, "nested": [None, True, False, -1.25e9, {}, []]},
                   "kind": "native-entry", "rule": "ReturnRoute.normalize",
                   "invocation": 1, "trial": False}
        self.assertEqual(self.read(json.dumps(payload)),
                         {key: payload[key] for key in ("kind", "rule", "invocation", "trial")})

    def test_strings_and_escapes_cross_buffer_boundaries(self):
        text = 'x' * 65520 + '\\" } ] \\u0061 é \\n' + 'y' * 150000
        payload = {"message": text, "kind": "native-entry", "rule": "R\\\"é",
                   "invocation": 1, "trial": False}
        self.assertEqual(self.read(json.dumps(payload, ensure_ascii=False))["rule"], payload["rule"])

    def test_large_payload_does_not_enter_returned_metadata(self):
        payload = {"kind": "feedback", "message": "x" * (1024 * 1024),
                   "capture": [{"a": [1, 2, 3]}] * 3000}
        self.assertEqual(self.read(json.dumps(payload)), {"kind": "feedback"})

    def test_deep_payload_uses_an_iterative_stack(self):
        self.assertEqual(self.read('{"capture":' + '[' * 2000 + '0' + ']' * 2000
                                   + ',"kind":"feedback"}'), {"kind": "feedback"})

    def test_invalid_json_and_duplicate_fields_reject(self):
        for text in ('{"kind":"feedback","kind":"native-entry"}',
                     '{"kind":"feedback","capture":[1,]}',
                     '{"kind":"feedback","capture":{"x":1,}}',
                     '{"kind":"feedback","capture":[1}}',
                     '{"kind":"feedback","capture":"\\q"}',
                     '{"kind":"feedback","capture":"\\u12xz"}',
                     '{"kind":"feedback","capture":NaN}',
                     '{"kind":"feedback"}null',
                     '{"kind":"feedback","capture":"unterminated}',
                     '{"kind":"feedback","capture":"line\nbreak"}',
                     '{"capture":0}', '{"kind":null}', '[]'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.read(text)


class NativeEntrySealTests(selected_tests.SelectedSealTests):
    def verify(self):
        data = self.data
        return verify_raw_evidence(data.raw, data.trace, data.request_path,
            expected_session_sha256=data.expected, expected_request_sha256=data.request_hash,
            raw_index_path=self.index_path, expected_raw_index_sha256=self.index_hash,
            raw_seal_path=self.root_seal, expected_raw_seal_sha256=self.seal_hash)

    def update_events(self):
        for event in self.index["events"]:
            event["sha256"] = hashlib.sha256((self.data.raw / event["path"]).read_bytes()).hexdigest()
        (self.data.raw / "EVENT-SEAL.json").write_bytes(trace_block.json_bytes(
            {"streams": self.index["events"]}))
        self.refresh_index()
        self.refresh_seal()

    def change_raw(self, number, **changes):
        path = self.data.raw / self.index["events"][number - 1]["path"]
        value = json.loads(path.read_text())
        value.update(changes)
        path.write_bytes(trace_block.json_bytes(value))
        self.update_events()

    def add_raw(self, value):
        path = self.data.raw / "events/process-42/event-00000003.json"
        path.write_bytes(trace_block.json_bytes(value))
        event = {"path": str(path.relative_to(self.data.raw)), "sha256": "pending"}
        self.index["events"].append(event)
        self.update_events()
        return event

    def test_verified_identity_list_binds_every_selected_raw_entry(self):
        verified = self.verify()["verified_native_entries"]
        self.assertEqual(verified, [{key: row[key] for key in ("rule", "client", "invocation", "event")}
                                   for row in self.index["attempted_entries"]])

    def test_omitted_nontrigger_cannot_hide_behind_reduced_counter(self):
        self.index["attempted_entries"].pop()
        self.data.trace["coverage"]["attempted_entries"]["ReturnRoute"] = 1
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "complete raw native-entry set"):
            self.verify()

    def test_omitted_trigger_and_point_cannot_hide_behind_reduced_counters(self):
        self.index["attempted_entries"].pop(0)
        self.data.trace["points"] = []
        for name in ("actual_triggers", "entry_events", "captured_events"):
            self.data.trace["coverage"][name]["ReturnRoute"] = 0
        self.data.trace["coverage"]["attempted_entries"]["ReturnRoute"] = 1
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "complete raw native-entry set"):
            self.verify()

    def test_invocation_substitution_in_both_index_and_point_rejects(self):
        self.index["attempted_entries"][0]["invocation"] = 99
        self.data.trace["points"][0]["trigger"]["invocation"] = 99
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "differs from its sealed native entry"):
            self.verify()

    def test_classification_cannot_borrow_another_entry_event_hash(self):
        rows = self.index["attempted_entries"]
        rows[0]["event"], rows[1]["event"] = rows[1]["event"], rows[0]["event"]
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "differs from its sealed native entry"):
            self.verify()

    def test_extra_feedback_row_cannot_hide_behind_increased_counter(self):
        event = self.add_raw({"kind": "feedback", "message": "native-entry", "invocation": 3})
        row = copy.deepcopy(self.index["attempted_entries"][1])
        row.update(invocation=3, event=event)
        self.index["attempted_entries"].append(row)
        self.data.trace["coverage"]["attempted_entries"]["ReturnRoute"] = 3
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "differs from its sealed native entry"):
            self.verify()

    def test_duplicate_raw_identity_rejects_even_when_index_omits_it(self):
        self.add_raw({"kind": "native-entry", "rule": "ReturnRoute.normalize",
                      "invocation": 1, "trial": False})
        with self.assertRaisesRegex(ValueError, "duplicate entry identity"):
            self.verify()

    def test_trial_entry_is_excluded_but_cannot_get_a_classification(self):
        event = self.add_raw({"kind": "native-entry", "rule": "ReturnRoute.normalize",
                              "invocation": 3, "trial": True})
        self.assertEqual(len(self.verify()["verified_native_entries"]), 2)
        row = copy.deepcopy(self.index["attempted_entries"][1])
        row.update(invocation=3, event=event)
        self.index["attempted_entries"].append(row)
        self.data.trace["coverage"]["attempted_entries"]["ReturnRoute"] = 3
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "differs from its sealed native entry"):
            self.verify()

    def test_raw_identity_types_and_attribution_must_be_exact(self):
        for changes in ({"trial": None}, {"trial": 0}, {"invocation": True},
                        {"invocation": 0}, {"invocation": "1"}, {"rule": None}):
            with self.subTest(changes=changes), self.assertRaisesRegex(ValueError, "invalid identity"):
                self.change_raw(1, **{
                    "trial": changes.get("trial", False), "invocation": changes.get("invocation", 1),
                    "rule": changes.get("rule", "ReturnRoute.normalize")})
                self.verify()

    def test_unknown_client_cannot_conceal_an_entry(self):
        self.change_raw(1, rule="unregistered-client")
        with self.assertRaisesRegex(ValueError, "no client descriptor"):
            self.verify()

    def add_descriptor(self, client, rule):
        self.request["entry_descriptors"][client] = {"rule": rule}
        self.data.request_path.write_bytes(trace_block.json_bytes(self.request))
        self.data.request_hash = hashlib.sha256(self.data.request_path.read_bytes()).hexdigest()
        self.refresh_seal()

    def test_client_substitution_in_both_index_and_point_rejects(self):
        self.add_descriptor("ReturnRoute.other", "ReturnRoute")
        self.index["attempted_entries"][0]["client"] = "ReturnRoute.other"
        self.data.trace["points"][0]["trigger"]["client"] = "ReturnRoute.other"
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "differs from its sealed native entry"):
            self.verify()

    def test_context_only_rule_needs_no_selected_classification(self):
        self.add_descriptor("EntryIntro.other", "EntryIntro")
        self.add_raw({"kind": "native-entry", "rule": "EntryIntro.other",
                      "invocation": 3, "trial": False})
        self.assertEqual(len(self.verify()["verified_native_entries"]), 2)

    def test_plain_mirror_symlink_requires_completed_storage_records(self):
        path = self.data.raw / self.index["events"][0]["path"]
        mirror = self.data.directory / "plain-mirror.json"
        path.rename(mirror)
        path.symlink_to(mirror)
        with self.assertRaisesRegex(ValueError, "completed storage records"):
            self.verify()

    def test_missing_trial_attribution_rejects(self):
        path = self.data.raw / self.index["events"][0]["path"]
        value = json.loads(path.read_text())
        del value["trial"]
        path.write_bytes(trace_block.json_bytes(value))
        self.update_events()
        with self.assertRaisesRegex(ValueError, "invalid identity or trial attribution"):
            self.verify()

    def test_raw_entry_order_cannot_be_reversed(self):
        self.index["attempted_entries"].reverse()
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "complete raw native-entry set in order"):
            self.verify()

    def test_removing_all_declared_counts_cannot_remove_selected_raw_entries(self):
        self.index["attempted_entries"] = []
        self.data.trace["coverage"]["attempted_entries"] = {}
        self.data.trace["coverage"]["actual_triggers"] = {}
        self.data.trace["points"] = []
        self.refresh_index()
        with self.assertRaisesRegex(ValueError, "complete raw native-entry set"):
            self.verify()


if __name__ == "__main__":
    unittest.main()
