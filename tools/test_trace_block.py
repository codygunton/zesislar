"""Test deterministic rendering. These fixtures do not validate the observer."""

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "block"))
import trace_block

GOLDENS = Path(__file__).resolve().parent / "fixtures" / "trace_block"


def hyp(name, ty, body=None):
    return {"names": [name], "type": ty, "type_nonotation": ty,
            "body": body, "body_nonotation": body}


def goal(text, hyps):
    return {"goal": text, "goal_nonotation": text, "hyps": hyps}


def fixture(kind):
    """Construct explicit synthetic data for the three renderer boundaries."""
    contexts = {"introduction": [hyp("n", "nat"), hyp("cached", "nat", "S n")],
                "store": [hyp("base", "Z"), hyp("bytes", "list byte"),
                          hyp("Hextent", "0 <= base /\\ base + 40 <= 2 ^ 64")],
                "return": [hyp("target", "bv 64"), hyp("Halign", "bv_unsigned target mod 4 = 0")]}
    heads = {"introduction": "exists n : nat, key n /\\ n = cached",
             "store": "find_in_context (FindMemMapsTo (base + 32)) ?kind",
             "return": "LiTactic (normalize_instr_addr target) continuation"}
    context = contexts[kind]
    primary = goal(heads[kind], context)
    evars = {"availability": "complete", "entries": [
        {"id": "?goal17", "status": "undefined", "type": heads[kind],
         "type_nonotation": heads[kind], "context": context,
         "body": None, "body_nonotation": None},
        {"id": "?defined19", "status": "defined", "type": "nat", "type_nonotation": "nat",
         "context": [hyp("n", "nat")], "body": "S n", "body_nonotation": "S n"}],
        "show_existentials": "Existential 17 remains open.\nExistential 19 := S n.\n"}
    rule = {"introduction": "ConjunctMatch", "store": "MemoryAccess", "return": "ReturnRoute"}[kind]
    accepted = kind != "store"
    trial = {"command": "existing_" + rule + ".", "clause": "owned-array" if not accepted else None,
             "outcome": "accepted" if accepted else "refused",
             "feedback": "advanced" if accepted else "The complete extent fact is absent.",
             "before": "entry", "after_trial": "trial", "rollback": "entry", "rollback_equal": True}
    point = dict(primary, trigger={"kind": "rule-entry", "rule": rule,
        "entry": "existing_" + rule, "branch": "native/0", "ordinal": 0,
        "matches_stop": True, "program_counter": "0x1000"},
        evars=evars, hint_log={"availability": "complete", "filter": [rule],
                             "events": ["entry " + rule, "trial logging suppressed"]},
        hand_call=[trial], refusal=[] if accepted else [{"hand_call_index": 0,
            "clause": "owned-array", "message": trial["feedback"], "exposure": "exposed"}],
        current_goals=[primary], shelf=[], given_up=[],
        hidden_focus_frames={"availability": "unavailable", "reason":
            "Proofview.tclFOCUS stores hidden left/right goals in a lexical continuation. "
            "The public observer API does not expose those ordered frames."},
        completeness={"required_fields_complete": True, "missing_observations": [],
                      "hidden_frames_required": False})
    if kind == "introduction":
        point["current_goals"].append(goal("True", []))
        point["shelf"].append(goal("nat", []))
    residual = copy.deepcopy(point)
    residual["trigger"].update(kind="residual", ordinal=1, matches_stop=False)
    residual["hand_call"] = []
    residual["refusal"] = []
    residual["show_proof"] = {"availability": "complete", "text": "fun n => ?goal17\n"}
    closed = kind == "return"
    visits = [{"program_counter": "0x1000", "kind": {"introduction": "entry", "store": "WriteMem", "return": "jalr"}[kind]}]
    request = {"block_pc": "0x1000", "rule_set": [{"name": rule, "enabled": True}],
               "stop": {"kind": "rule", "value": rule},
               "scope": {"root": "a" * 40, "source": "Fixture.v", "source_sha256": "b" * 64, "statement_sha256": "c" * 64}}
    result = {"identity": {"root": "a" * 40, "source": "Fixture.v", "source_sha256": "b" * 64,
                          "statement_sha256": "c" * 64,
                          "switches": {"requested": [rule], "actual_instances": [rule + ".enabled"]}},
              "points": [point], "residual": None if closed else residual,
              "instruction_visits": visits,
              "coverage": {"entry_events": {rule: 1}, "captured_events": {rule: 1},
                  "missing_event_ids": [], "unobserved_regions": [], "required_complete": True,
                  "traversal": "proof-closed" if closed else "first-residual",
                  "requested_trigger": "occurred", "requested_trigger_instruction_list": visits},
              "completion": {"trace_complete": True, "proof_closed": closed, "reasons": []},
              "evidence": {"path": "/volatile/session-123.json", "timestamp": "volatile"},
              "owned_closure": {"server_pid": 123, "closed": True}}
    capture_fields = ("goal", "goal_nonotation", "hyps", "current_goals", "shelf", "given_up",
                      "evars", "hidden_focus_frames", "completeness")
    before = {key: copy.deepcopy(point[key]) for key in capture_fields}
    after = copy.deepcopy(before)
    if accepted:
        after["current_goals"] = after["current_goals"][1:]
        primary_after = after["current_goals"][0] if after["current_goals"] else {
            "goal": None, "goal_nonotation": None, "hyps": []}
        after.update({key: primary_after[key] for key in ("goal", "goal_nonotation", "hyps")})
    result["snapshots"] = {"entry": before, "trial": after}
    trial["commands"] = [{"command": trial["command"], "before": "#/snapshots/entry",
                          "after": "#/snapshots/trial", "outcome": trial["outcome"],
                          "refusal": None if accepted else trial["feedback"]}]
    if closed:
        result["completion"]["closure_check"] = {"command": "Qed.", "accepted": True,
                                                  "unresolved_evars": False}
        result["completion"]["final_obligations"] = {"availability": "complete",
            "session": trace_block.logical_session_id(request),
            "counts": {"goals": 0, "stack": 0, "shelf": 0, "given_up": 0},
            "undefined_evars": 0, "evidence": "evidence/SESSION.json#/final_snapshot"}
    return request, result


class RendererTests(unittest.TestCase):
    def test_three_golden_bundles(self):
        for kind in ("introduction", "store", "return"):
            with self.subTest(kind=kind):
                trace = trace_block.build_trace(*fixture(kind))
                self.assertTrue(trace["completion"]["trace_complete"])
                self.assertEqual(trace_block.json_bytes(trace), (GOLDENS / (kind + ".json")).read_bytes())
                self.assertEqual(trace_block.render_markdown(trace), (GOLDENS / (kind + ".md")).read_text())

    def test_maps_sort_and_ordered_lists_remain_exact(self):
        request, result = fixture("introduction")
        expected = trace_block.json_bytes(trace_block.build_trace(request, result))
        result = dict(reversed(list(result.items())))
        actual = trace_block.build_trace(request, result)
        self.assertEqual(expected, trace_block.json_bytes(actual))
        self.assertEqual(actual["points"][0]["hyps"][1]["body"], "S n")
        self.assertEqual(actual["points"][0]["current_goals"][1]["goal"], "True")
        self.assertEqual(actual["points"][0]["shelf"][0]["goal"], "nat")

    def test_runtime_changes_do_not_change_bundle(self):
        request, result = fixture("return")
        original = trace_block.build_trace(request, result)
        result["evidence"] = {"path": "/another/runtime", "timestamp": "later"}
        result["owned_closure"]["server_pid"] = 456
        result["completion"]["timestamp"] = "later"
        self.assertEqual(original, trace_block.build_trace(request, result))

    def test_long_terms_and_markdown_fences_remain_complete(self):
        request, result = fixture("store")
        long = "symbol " * 15000 + "```end```"
        for point in (result["points"][0], result["residual"]):
            point["goal"] = point["current_goals"][0]["goal"] = long
        result["snapshots"]["entry"]["goal"] = result["snapshots"]["entry"]["current_goals"][0]["goal"] = long
        trace = trace_block.build_trace(request, result)
        self.assertTrue(trace["completion"]["trace_complete"])
        rendered = trace_block.render_markdown(trace)
        self.assertIn(long, rendered)
        self.assertIn("````\n" + long, rendered)
        self.assertIn("TRACE.json#/points/0/goal", rendered)
        self.assertEqual(trace_block.pointer("a/b", "c~d"), "/a~1b/c~0d")

    def test_immutable_write_checks_both_targets_before_writing(self):
        trace = trace_block.build_trace(*fixture("store"))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "TRACE.md").write_text("different")
            with self.assertRaises(ValueError):
                trace_block.write_bundle(path, trace)
            self.assertFalse((path / "TRACE.json").exists())
            (path / "TRACE.md").unlink()
            first = trace_block.write_bundle(path, trace)
            self.assertEqual(first, trace_block.write_bundle(path, trace))


class CompletenessTests(unittest.TestCase):
    def assert_incomplete(self, mutate, message):
        request, result = fixture("store")
        mutate(result)
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertTrue(any(message in reason for reason in trace["completion"]["reasons"]),
                        trace["completion"]["reasons"])

    def test_missing_internal_entry_is_incomplete(self):
        self.assert_incomplete(lambda r: r["coverage"]["captured_events"].update(MemoryAccess=0), "do not match")

    def test_matching_counters_without_retained_points_are_incomplete(self):
        self.assert_incomplete(lambda r: r.update(points=[]), "retained points")

    def test_missing_source_hash_is_incomplete(self):
        self.assert_incomplete(lambda r: r["identity"].pop("source_sha256"), "source_sha256")

    def test_show_existentials_alone_is_not_live_evd(self):
        self.assert_incomplete(lambda r: r["points"][0]["evars"].pop("entries"), "live Evd entries")

    def test_defined_evar_body_is_required(self):
        self.assert_incomplete(lambda r: r["points"][0]["evars"]["entries"][1].update(body=None), "body is unavailable")

    def test_truncated_goal_is_rejected(self):
        self.assert_incomplete(lambda r: r["points"][0].update(goal="..."), "truncated")

    def test_failed_trial_rollback_is_rejected(self):
        self.assert_incomplete(lambda r: r["points"][0]["hand_call"][0].update(rollback_equal=False), "rollback")

    def test_refused_trial_requires_matching_refusal(self):
        self.assert_incomplete(lambda r: r["points"][0].update(refusal=[]), "matching refusal")

    def test_refusal_index_and_exact_message_must_match(self):
        for change in ({"hand_call_index": 2}, {"message": "different"}, {"clause": "different"}):
            with self.subTest(change=change):
                self.assert_incomplete(lambda r: r["points"][0]["refusal"][0].update(change), "matching")

    def test_trial_feedback_is_required_even_when_accepted(self):
        self.assert_incomplete(lambda r: r["points"][0]["hand_call"][0].pop("feedback"), "feedback")
        request, result = fixture("return")
        result["points"][0]["hand_call"][0].pop("feedback")
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_trial_snapshot_references_are_required(self):
        for field in ("before", "after_trial", "rollback"):
            with self.subTest(field=field):
                self.assert_incomplete(lambda r: r["points"][0]["hand_call"][0].pop(field), "snapshot reference")

    def test_truncated_hint_refusal_and_feedback_text_are_rejected(self):
        changes = [lambda r: r["points"][0]["hint_log"]["events"].append({"message": "truncated ..."}),
                   lambda r: r["points"][0]["refusal"][0].update(message="truncated …"),
                   lambda r: r["points"][0]["hand_call"][0].update(feedback="truncated ...")]
        for change in changes:
            with self.subTest(change=change):
                self.assert_incomplete(change, "truncated")

    def test_file_references_cannot_replace_logical_snapshot_links(self):
        request, result = fixture("store")
        trial = result["points"][0]["hand_call"][0]
        for field in ("before", "after_trial", "rollback"):
            trial[field] = {"path": "evidence/" + field + ".json", "sha256": "d" * 64}
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_residual_proof_is_required(self):
        self.assert_incomplete(lambda r: r["residual"].pop("show_proof"), "Show Proof")

    def test_missing_group_is_not_an_empty_group(self):
        self.assert_incomplete(lambda r: r["points"][0].pop("shelf"), "shelf is unavailable")

    def test_unavailable_hidden_frames_are_optional(self):
        trace = trace_block.build_trace(*fixture("introduction"))
        self.assertTrue(trace["completion"]["trace_complete"])
        self.assertEqual(trace["points"][0]["hidden_focus_frames"]["availability"], "unavailable")

    def test_observed_absent_trigger_is_complete_with_instruction_list(self):
        request, result = fixture("store")
        result["coverage"]["requested_trigger"] = "not-occurred"
        trace = trace_block.build_trace(request, result)
        self.assertTrue(trace["completion"]["trace_complete"])
        result["coverage"]["requested_trigger"] = "unobserved"
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_step_bound_is_incomplete(self):
        self.assert_incomplete(lambda r: r["coverage"].update(traversal="interrupted"), "Traversal")

    def test_empty_groups_cannot_establish_closure(self):
        request, result = fixture("return")
        result["completion"].pop("closure_check")
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertFalse(trace["completion"]["proof_closed"])

    def test_refused_qed_cannot_establish_closure(self):
        request, result = fixture("return")
        result["completion"]["closure_check"]["accepted"] = False
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])


class ReviewRegressionTests(unittest.TestCase):
    def test_all_trial_references_must_name_retained_snapshots(self):
        for field in ("before", "after_trial", "rollback"):
            for missing in ("absent-snapshot", None, {"path": "evidence/raw.json", "sha256": "a" * 64}):
                with self.subTest(field=field, missing=missing):
                    request, result = fixture("store")
                    result["points"][0]["hand_call"][0][field] = missing
                    self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_command_endpoints_must_match_trial_references_even_for_identical_states(self):
        for field, wrong in (("before", "#/snapshots/trial"), ("after", "#/snapshots/entry")):
            request, result = fixture("store")
            self.assertEqual(result["snapshots"]["entry"], result["snapshots"]["trial"])
            result["points"][0]["hand_call"][0]["commands"][0][field] = wrong
            self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_rollback_flag_cannot_hide_a_different_snapshot(self):
        request, result = fixture("store")
        wrong = copy.deepcopy(result["snapshots"]["entry"])
        wrong["evars"]["entries"][0]["id"] = "?different"
        result["snapshots"]["wrong"] = wrong
        result["points"][0]["hand_call"][0]["rollback"] = "wrong"
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_first_command_snapshot_must_match_the_actual_point(self):
        request, result = fixture("store")
        result["snapshots"]["entry"]["evars"]["entries"][0]["id"] = "?different"
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_multiple_commands_require_a_continuous_snapshot_chain(self):
        request, result = fixture("introduction")
        trial = result["points"][0]["hand_call"][0]
        trial["commands"].append(copy.deepcopy(trial["commands"][0]))
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_no_command_follows_a_refusal(self):
        request, result = fixture("store")
        trial = result["points"][0]["hand_call"][0]
        first = copy.deepcopy(trial["commands"][0]); first["after"] = first["before"]
        trial["commands"].insert(0, first)
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_identity_must_equal_the_standalone_request_scope(self):
        for field, wrong in (("root", "d" * 40), ("source_sha256", "d" * 64),
                             ("statement_sha256", "d" * 64), ("source", "Other.v"),
                             ("prefix", {"path": "other.txt", "sha256": "d" * 64})):
            with self.subTest(field=field):
                request, result = fixture("store")
                result["identity"][field] = wrong
                self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])
        request, result = fixture("store"); request["scope"].pop("statement_sha256")
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])


class TerminalClaimTests(unittest.TestCase):
    def test_composite_idtac_records_cannot_claim_an_unrelated_umbrella(self):
        request, result = fixture("introduction")
        trial = result["points"][0]["hand_call"][0]
        trial["commands"] = [
            {"command": "idtac.", "before": "#/snapshots/entry", "after": "#/snapshots/entry", "outcome": "accepted", "refusal": None},
            {"command": "idtac.", "before": "#/snapshots/entry", "after": "#/snapshots/trial", "outcome": "accepted", "refusal": None}]
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertIn("unsupported composite", " ".join(trace["completion"]["reasons"]))

    def test_refutation_claim_is_rejected_without_a_certificate_validator(self):
        request, result = fixture("store")
        result["verdict"] = {"status": "established-unsatisfiable", "scope": "named-rule",
            "evidence": "#/points/0/hand_call/0", "certificate": {"kind": "refutation",
                "statement": "point hypotheses ⊢ ¬ clause side condition", "statement_sha256": "d" * 64,
                "accepted_qed": True, "assumptions": [], "closure_check": {"accepted": True}}}
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertIn("supported certificate validator", " ".join(trace["completion"]["reasons"]))
        self.assertEqual(trace["verdict"]["status"], "unresolved")

    def test_unknown_terminal_status_is_explicitly_incomplete(self):
        request, result = fixture("store")
        result["verdict"] = {"status": "terminal", "evidence": "#/points/0"}
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertIn("supplied terminal claim", " ".join(trace["completion"]["reasons"]))

    def test_supplied_success_needs_its_exact_terminal_pointer_and_scope(self):
        for kind, evidence, scope in (("store", "#/completion/closure_check", "whole-proof"),
                                      ("return", "#/points/0", "whole-proof"),
                                      ("return", "#/completion/closure_check", "named-rule")):
            request, result = fixture(kind)
            result["verdict"] = {"status": "actual-success", "evidence": evidence, "scope": scope}
            trace = trace_block.build_trace(request, result)
            self.assertFalse(trace["completion"]["trace_complete"])
            self.assertIn("matching terminal evidence", " ".join(trace["completion"]["reasons"]))
        request, result = fixture("return")
        result["verdict"] = {"status": "actual-success", "kind": "proof_closure", "session": trace_block.logical_session_id(request), "evidence": "#/completion/closure_check", "scope": "whole-proof"}
        self.assertTrue(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_unresolved_claim_cannot_hide_terminal_evidence(self):
        request, result = fixture("store")
        result["verdict"] = {"status": "unresolved", "evidence": "#/points/0"}
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertIn("unsupported terminal claim", " ".join(trace["completion"]["reasons"]))


class SuccessKindTests(unittest.TestCase):
    def test_proof_closure_needs_empty_complete_final_obligations(self):
        changes = (lambda c: c.pop("final_obligations"),
                   lambda c: c["final_obligations"]["counts"].update(shelf=1),
                   lambda c: c["final_obligations"]["counts"].update(stack=1),
                   lambda c: c["final_obligations"]["counts"].update(goals=False),
                   lambda c: c["final_obligations"].update(undefined_evars=1),
                   lambda c: c["final_obligations"].update(availability="unavailable"),
                   lambda c: c["final_obligations"].update(session="another-session"))
        for change in changes:
            request, result = fixture("return"); change(result["completion"])
            trace = trace_block.build_trace(request, result)
            self.assertFalse(trace["completion"]["trace_complete"])
            self.assertFalse(trace["completion"]["proof_closed"])
            self.assertEqual(trace["verdict"]["status"], "unresolved")
            self.assertIsNone(trace["verdict"]["kind"])

    def test_rule_success_requires_the_targeted_goal_to_disappear(self):
        request, result = SessionTests().named_rule_terminal_fixture()
        after = result["snapshots"]["trial"]
        after["current_goals"] = [copy.deepcopy(result["snapshots"]["entry"]["current_goals"][0])]
        after.update({key: after["current_goals"][0][key] for key in ("goal", "goal_nonotation", "hyps")})
        trace = trace_block.build_trace(request, result)
        self.assertTrue(trace["completion"]["trace_complete"])
        self.assertEqual(trace["verdict"]["status"], "unresolved")

    def test_rule_success_requires_the_explicit_whole_rule_trial(self):
        request, result = SessionTests().named_rule_terminal_fixture()
        result["points"][0]["hand_call"][0]["clause"] = "prefix-only"
        trace = trace_block.build_trace(request, result)
        self.assertEqual(trace["verdict"]["status"], "unresolved")

    def test_rule_success_can_preserve_an_identified_unrelated_shelf(self):
        request, result = SessionTests().named_rule_terminal_fixture()
        peer = dict(goal("nat", []), id="?peer23")
        result["snapshots"]["entry"]["shelf"] = [copy.deepcopy(peer)]
        result["snapshots"]["trial"]["shelf"] = [copy.deepcopy(peer)]
        result["points"][0]["shelf"] = [copy.deepcopy(peer)]
        trace = trace_block.build_trace(request, result)
        self.assertTrue(trace["completion"]["trace_complete"])
        self.assertEqual(trace["verdict"]["kind"], "rule_success")
        self.assertFalse(trace["completion"]["proof_closed"])
        result["snapshots"]["trial"]["shelf"][0].pop("id")
        self.assertEqual(trace_block.build_trace(request, result)["verdict"]["status"], "unresolved")

    def test_supplied_success_kind_and_session_must_match(self):
        for field, wrong in (("kind", "rule_success"), ("session", "other-session")):
            request, result = fixture("return")
            result["verdict"] = {"status": "actual-success", "kind": "proof_closure",
                "session": trace_block.logical_session_id(request), "scope": "whole-proof",
                "evidence": "#/completion/closure_check"}
            result["verdict"][field] = wrong
            self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_refutation_payload_is_unsupported_even_with_an_unresolved_label(self):
        request, result = fixture("store")
        result["verdict"] = {"status": "unresolved", "kind": None,
            "session": trace_block.logical_session_id(request), "evidence": None,
            "certificate": {"kind": "refutation"}}
        trace = trace_block.build_trace(request, result)
        self.assertFalse(trace["completion"]["trace_complete"])
        self.assertIn("supplied refutation claim", " ".join(trace["completion"]["reasons"]))


class SessionTests(unittest.TestCase):
    def test_session_identity_is_stable_and_shared(self):
        request, result = fixture("store")
        trace = trace_block.build_trace(request, result)
        session = trace["session"]["id"]
        self.assertEqual(trace["points"][0]["session_id"], session)
        self.assertEqual(trace["residual"]["session_id"], session)
        self.assertTrue(all(snapshot["session_id"] == session for snapshot in trace["snapshots"].values()))
        self.assertEqual(trace["pet_start_tick"], "evidence/SESSION.json#/ownership/pet/start_ticks")
        result["owned_closure"]["server_pid"] = 999
        self.assertEqual(trace, trace_block.build_trace(request, result))

    def test_command_pointers_resolve_to_actual_snapshots(self):
        trace = trace_block.build_trace(*fixture("store"))
        command = trace["points"][0]["hand_call"][0]["commands"][0]
        self.assertEqual(trace_block.snapshot_key(command["before"]), "entry")
        self.assertIn(trace_block.snapshot_key(command["after"]), trace["snapshots"])
        self.assertEqual(command["refusal"], "The complete extent fact is absent.")

    def test_missing_command_or_snapshot_is_incomplete(self):
        for change in (lambda r: r["points"][0]["hand_call"][0].pop("commands"),
                       lambda r: r["snapshots"].pop("trial"),
                       lambda r: r["points"][0]["hand_call"][0]["commands"][0].update(before="#/points/0")):
            with self.subTest(change=change):
                request, result = fixture("store")
                change(result)
                self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_mixed_session_snapshots_are_incomplete(self):
        request, result = fixture("store")
        result["snapshots"]["entry"]["session_id"] = "another-session"
        self.assertFalse(trace_block.build_trace(request, result)["completion"]["trace_complete"])

    def test_refusal_does_not_prove_unsatisfiability(self):
        trace = trace_block.build_trace(*fixture("store"))
        self.assertTrue(trace["completion"]["trace_complete"])
        self.assertEqual(trace["verdict"]["status"], "unresolved")
        self.assertIsNone(trace["verdict"]["evidence"])

    def test_progress_keeps_an_unresolved_terminal_verdict(self):
        trace = trace_block.build_trace(*fixture("introduction"))
        self.assertEqual(trace["points"][0]["hand_call"][0]["outcome"], "accepted")
        self.assertEqual(trace["verdict"]["status"], "unresolved")
        self.assertIsNone(trace["verdict"]["evidence"])
        self.assertFalse(trace["completion"]["proof_closed"])

    def test_actual_success_requires_an_accepted_qed(self):
        trace = trace_block.build_trace(*fixture("return"))
        self.assertTrue(trace["completion"]["proof_closed"])
        self.assertEqual(trace["verdict"]["status"], "actual-success")
        self.assertEqual(trace["verdict"]["evidence"], "#/completion/closure_check")
        self.assertEqual(trace["verdict"]["kind"], "proof_closure")
        request, result = fixture("return")
        result["completion"]["closure_check"]["accepted"] = False
        self.assertEqual(trace_block.build_trace(request, result)["verdict"]["status"], "unresolved")

    def named_rule_terminal_fixture(self):
        request, result = fixture("store")
        trial = result["points"][0]["hand_call"][0]
        trial.update(clause="whole-rule", outcome="accepted", feedback="The exact entry goal closed.")
        trial["commands"][0].update(outcome="accepted", refusal=None)
        result["points"][0]["refusal"] = []
        before, after = result["snapshots"]["entry"], result["snapshots"]["trial"]
        before["current_goals"][0]["id"] = "?goal17"
        result["points"][0]["current_goals"][0]["id"] = "?goal17"
        peer = dict(before["evars"]["entries"][0], id="?peer23", type="nat", type_nonotation="nat")
        before["evars"]["entries"].append(peer)
        result["points"][0]["evars"]["entries"].append(copy.deepcopy(peer))
        after["evars"]["entries"].append(copy.deepcopy(peer))
        after["evars"]["entries"][0].update(status="defined", body="exact_entry_proof", body_nonotation="exact_entry_proof")
        after.update(current_goals=[], goal=None, goal_nonotation=None, hyps=[])
        return request, result

    def test_named_rule_terminal_success_preserves_existing_obligations(self):
        trace = trace_block.build_trace(*self.named_rule_terminal_fixture())
        self.assertTrue(trace["completion"]["trace_complete"])
        self.assertFalse(trace["completion"]["proof_closed"])
        self.assertEqual(trace["verdict"]["status"], "actual-success")
        self.assertEqual(trace["verdict"]["scope"], "named-rule")
        self.assertEqual(trace["verdict"]["kind"], "rule_success")
        self.assertEqual(trace["verdict"]["evidence"], "#/points/0/hand_call/0")
        check = trace["verdict"]["terminal_check"]
        self.assertEqual(check["entry_goal_evars"], ["?goal17"])
        self.assertEqual(check["after_undefined_evars"], ["?peer23"])
        self.assertIn(trace_block.snapshot_key(check["before"]), trace["snapshots"])
        self.assertIn(trace_block.snapshot_key(check["after"]), trace["snapshots"])

    def test_named_rule_progress_or_missing_evar_evidence_stays_unresolved(self):
        changes = (lambda b, a: b["current_goals"][0].pop("id"),
                   lambda b, a: a["evars"]["entries"][0].update(status="undefined", body=None, body_nonotation=None),
                   lambda b, a: a["evars"]["entries"].pop(0),
                   lambda b, a: a["evars"]["entries"].append(dict(a["evars"]["entries"][-1], id="?new41")))
        for change in changes:
            with self.subTest(change=change):
                request, result = self.named_rule_terminal_fixture()
                change(result["snapshots"]["entry"], result["snapshots"]["trial"])
                self.assertEqual(trace_block.build_trace(request, result)["verdict"]["status"], "unresolved")

    def test_snapshot_ids_use_rfc6901_escaping(self):
        self.assertEqual(trace_block.snapshot_key("#/snapshots/a~1b~0c"), "a/b~c")
        for value in ("#/snapshots/", "#/snapshots/a/b", "#/snapshots/a~2b", "other.json#/snapshots/a"):
            self.assertIsNone(trace_block.snapshot_key(value))


class CliTests(unittest.TestCase):
    def test_pc_and_all_stop_forms(self):
        self.assertEqual(trace_block.parse_pc("0X800D69B0"), "0x800d69b0")
        for value in ("pc:0x1000", "jalr", "WriteMem", "FindMemMapsTo", "mem_mapsto_kind",
                      "LiTactic (normalize_instr_addr _)", "LiTactic(normalize_instr_addr _)",
                      "residual", "rule:ConjunctMatch"):
            with self.subTest(value=value):
                self.assertIsInstance(trace_block.parse_stop(value), dict)
        for value in ("", "pc:-1", "ReadMem", "rule:", "pc:0x10000000000000000"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                trace_block.parse_stop(value)

    def test_rule_order_duplicates_and_invalid_values(self):
        self.assertEqual([r["name"] for r in trace_block.parse_rules("ReturnRoute=on,ConjunctMatch=off")],
                         ["ConjunctMatch", "ReturnRoute"])
        for value in ("ReturnRoute=on,ReturnRoute=off", "ReturnRoute=yes", "ReturnRoute", ""):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                trace_block.parse_rules(value)

    def test_source_and_exact_prefix_are_bound_before_backend(self):
        with tempfile.TemporaryDirectory() as directory:
            workspace = Path(directory)
            subprocess.run(["git", "init", "-q", directory], check=True)
            source = workspace / "Block.v"
            source.write_bytes(b"Lemma DesignedBoundary_1000 : True.\r\nProof.\r\nexact I.\r\nQed.\r\n")
            prefix = workspace / "prefix.txt"
            prefix.write_bytes(b'first [idtac "a.b" | exact I].\r\n')
            request = {"workspace": directory, "source": "Block.v", "prefix_file": "prefix.txt",
                       "block_pc": "0x1000", "theorem": None}
            with patch.object(trace_block.subprocess, "check_output", return_value="a" * 40):
                actual = trace_block.resolve_request(request)
            self.assertEqual(actual["prefix_text"], prefix.read_bytes().decode())
            self.assertEqual(actual["declaration"], "Lemma DesignedBoundary_1000 : True.\r\n")
            self.assertEqual(actual["scope"]["source_sha256"], trace_block.sha256(source))
            self.assertEqual(actual["scope"]["prefix"]["sha256"], trace_block.sha256(prefix))
            request["source"] = str(workspace.parent / "outside.v")
            with self.assertRaisesRegex(ValueError, "leaves"):
                trace_block.resolve_request(request)

    def test_cli_incomplete_trace_returns_nonzero_and_preserves_bundle(self):
        request, result = fixture("store")
        result["coverage"]["required_complete"] = False
        class Backend:
            @staticmethod
            def prepare_request(value, out):
                return value
            @staticmethod
            def run_capture(value, out):
                return result
        with tempfile.TemporaryDirectory() as directory:
            def project(value, out, backend):
                actual = trace_block.build_trace(value, backend.run_capture(value, out))
                trace_block.write_bundle(out, actual)
                return actual
            with patch.object(trace_block, "resolve_request", return_value=request), patch(
                    "trace_block_capture.capture_bundle", side_effect=project):
                code = trace_block.main(["--block", "1000", "--rules", "MemoryAccess=on",
                    "--stop", "residual", "--out", directory], Backend)
            self.assertEqual(code, 1)
            self.assertTrue((Path(directory) / "TRACE.json").exists())
            self.assertTrue((Path(directory) / "TRACE.md").exists())


if __name__ == "__main__":
    unittest.main()
