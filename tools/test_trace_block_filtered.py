"""Check filter descriptors and counter completeness without a proof run."""

import copy
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parent / "block"))
from trace_block_filtered import CounterProjection, bind_descriptors, guard_manifest, typed_guards


class FilteredTests(unittest.TestCase):
    def setUp(self):
        self.descriptors = {client: {"rule": "MemoryAccess" if client.startswith("MemoryAccess.") else "ConjunctMatch" if client.startswith("Hooks.") else "ReturnRoute",
                                     "commands": {"whole-rule": "original"}}
                            for client in typed_guards()}
        self.process = {"pid": 17, "start_ticks": 99}
        self.bound = bind_descriptors(self.descriptors)

    def row(self, classification="actual-trigger", sequence=1):
        client = "ReturnRoute.normalize"
        return {"kind": "guard-counter", "sequence": sequence, "invocation": sequence,
                "parent_invocation": None, "trial": False, "client": client, "rule": "ReturnRoute",
                "guard_hash": self.bound[client]["typed_guard"]["sha256"],
                "classification": classification, "outcome": None,
                "fresh_evar_before": 17, "fresh_evar_after": 17}

    def capture(self, invocation=1):
        return {"process": self.process, "client": "ReturnRoute.normalize", "invocation": invocation}

    def test_trial_and_wrong_kind_reject(self):
        for change in ({"kind": "hand-accepted"}, {"trial": True}, {"trial": None}):
            row = self.row()
            row.update(change)
            with self.assertRaisesRegex(ValueError, "native guard"):
                CounterProjection(self.descriptors, self.process).add(row)

    def test_same_invocation_with_later_sequence_rejects(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row())
        with self.assertRaisesRegex(ValueError, "invocation identity"):
            projection.add(self.row(sequence=2) | {"invocation": 1})

    def test_equal_counts_with_wrong_identity_reject(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row())
        with self.assertRaisesRegex(ValueError, "unrecorded"):
            projection.coverage([self.capture(2)])

    def test_wrong_process_and_duplicate_capture_reject(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row())
        for captures in ([self.capture() | {"process": {"pid": 18, "start_ticks": 99}}],
                         [self.capture(), self.capture()]):
            with self.assertRaises(ValueError):
                projection.coverage(captures)

    def test_manifest_bytes_are_deterministic(self):
        value, raw = guard_manifest(self.descriptors)
        self.assertEqual((value, raw), guard_manifest(dict(reversed(list(self.descriptors.items())))))
        for client, row in value["clients"].items():
            self.assertEqual(row["sha256"], hashlib.sha256(row["command"].encode()).hexdigest())
        self.assertEqual(self.bound["ReturnRoute.normalize"]["commands"], {"whole-rule": "original"})

    def test_guards_do_not_resolve_switches_or_select_witnesses(self):
        for command in typed_guards().values():
            for forbidden in ("zesu_switch_enabled", "unify", "zesu_return_decode_facts", "open_existentials", "vm_compute"):
                self.assertNotIn(forbidden, command)
        conjunct = typed_guards()["Hooks.zesu_conjunct_head_if_enabled"]
        self.assertIn("@ZesuEntryIntroApplied", conjunct)
        self.assertIn("ZesuEntryIntroHeads", conjunct)
        self.assertIn("zesu_expose_environment_alias", conjunct)
        self.assertNotIn("False", typed_guards()["ReturnRoute.implication"])

    def test_guard_uses_value_quotation(self):
        for command in typed_guards().values():
            self.assertIn('ltac1val:(fun _ => ', command)
            self.assertNotIn('ltac1:(fun _ => ', command)
            self.assertIn('(fun () => ltac1:(', command)

    def test_off_rule_still_counts_actual_shape(self):
        projection = CounterProjection(self.descriptors, self.process)
        row = self.row()
        row["outcome"] = "switch-refused"
        self.assertEqual(projection.add(row), "actual-trigger")
        coverage = projection.coverage([self.capture()])
        self.assertTrue(coverage["required_complete"])
        self.assertEqual(coverage["actual_triggers"]["ReturnRoute"], 1)

    def test_unknown_guard_blocks_completeness(self):
        for classification, guard_hash in (("unknown", None), ("non-trigger", "0" * 64)):
            with self.subTest(classification=classification):
                projection = CounterProjection(self.descriptors, self.process)
                row = self.row(classification)
                row["guard_hash"] = guard_hash
                self.assertEqual(projection.add(row), "unknown")
                coverage = projection.coverage([])
                self.assertFalse(coverage["required_complete"])
                self.assertEqual(coverage["unknown_guards"]["ReturnRoute"], 1)

    def test_missing_selected_capture_is_incomplete(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row())
        self.assertFalse(projection.coverage([])["required_complete"])

    def test_extra_capture_rejects(self):
        projection = CounterProjection(self.descriptors, self.process)
        with self.assertRaisesRegex(ValueError, "unrecorded"):
            projection.coverage([self.capture()])

    def test_nontrigger_has_no_capture(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row("non-trigger"))
        coverage = projection.coverage([])
        self.assertTrue(coverage["required_complete"])
        self.assertEqual(coverage["attempted_entries"]["ReturnRoute"], 1)

    def test_fresh_evar_change_rejects(self):
        row = self.row()
        row["fresh_evar_after"] += 1
        with self.assertRaisesRegex(ValueError, "changed"):
            CounterProjection(self.descriptors, self.process).add(row)

    def test_sequence_repetition_rejects(self):
        projection = CounterProjection(self.descriptors, self.process)
        projection.add(self.row())
        with self.assertRaisesRegex(ValueError, "identity|order"):
            projection.add(self.row())

    def test_bad_counter_keys_and_types_reject(self):
        projection = CounterProjection(self.descriptors, self.process)
        for counters in ({"ReturnRoute": 0}, {"ReturnRoute": True, "ConjunctMatch": 0}):
            with self.assertRaises(ValueError):
                projection.coverage(counters)

    def test_unsupported_clients_and_rules_reject(self):
        for descriptors in ({"Other": {"rule": "ReturnRoute"}},
                            {"ReturnRoute.normalize": {"rule": "ConjunctMatch"}}):
            with self.assertRaises(ValueError):
                bind_descriptors(descriptors)

    def test_unknown_classification_and_client_reject(self):
        for field, value in (("classification", "absent"), ("client", "Other"), ("rule", "Other")):
            row = copy.deepcopy(self.row())
            row[field] = value
            with self.assertRaises(ValueError):
                CounterProjection(self.descriptors, self.process).add(row)


if __name__ == "__main__":
    unittest.main()
