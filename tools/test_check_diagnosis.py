import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest

from tools.block import check_diagnosis as checker


class CitationFormatTests(unittest.TestCase):
    def test_renderer_links_and_bare_citations_keep_order(self):
        text = "[trace](one/TRACE.json#/a), `two/TRACE.json#/b`; [Checked command](TRACE.json#/c)"
        citations, remaining = checker.parse_citations(text)
        self.assertEqual(citations, [checker.Citation("one/TRACE.json", "/a"),
                                     checker.Citation("two/TRACE.json", "/b"),
                                     checker.Citation("TRACE.json", "/c")])
        self.assertEqual(remaining, "")

    def test_link_label_does_not_replace_the_target(self):
        citations, remaining = checker.parse_citations("[TRACE.json#/false](TRACE.json#/true)")
        self.assertEqual(citations, [checker.Citation("TRACE.json", "/true")])
        self.assertEqual(remaining, "")

    def test_links_preserve_pointer_escaping_and_empty_fragment(self):
        for pointer in ("/a~1b/space%20key", "/%CE%BB", ""):
            with self.subTest(pointer=pointer):
                self.assertEqual(checker.parse_citations(f"[trace](TRACE.json#{pointer})"),
                                 ([checker.Citation("TRACE.json", pointer)], ""))

    def test_unsupported_or_malformed_links_leave_unchecked_text(self):
        for text in ("[trace](other.json#/a)", "[trace](TRACE.json#/a", "prefix[trace](TRACE.json#/a",
                     "[trace](TRACE.json#/a) prose",
                     "[trace](TRACE.json#/a) [other](file.json#/b)"):
            with self.subTest(text=text):
                self.assertTrue(checker.parse_citations(text)[1])


class PointerTests(unittest.TestCase):
    def test_objects_arrays_empty_keys_and_root(self):
        value = {"": [0, {"answer": False}], "0": "object key"}
        self.assertIs(checker.resolve_pointer(value, ""), value)
        self.assertEqual(checker.resolve_pointer(value, "/0"), "object key")
        self.assertIs(checker.resolve_pointer(value, "//1/answer"), False)

    def test_rfc6901_and_uri_escaping(self):
        value = {"a/b": {"m~n": {"~1": {"space key": "λ"}}}}
        self.assertEqual(checker.resolve_pointer(value, "/a~1b/m~0n/~01/space%20key"), "λ")
        self.assertEqual(checker.resolve_pointer({"λ": 1}, "/%CE%BB"), 1)
        self.assertEqual(checker.resolve_pointer({"a": {"b": 2}}, "/a%2Fb"), 2)

    def test_unresolved_and_invalid_pointers(self):
        for document, pointer in [({}, "/absent"), ([], "/0"), ([1], "/1"),
                                  ([1], "/01"), ([1], "/-"), ([1], "/-1"),
                                  ([1], "/1.0"), ({}, "key"), ({}, "/a~2b"),
                                  ({}, "/trailing~"), ({}, "/bad%xx"),
                                  ({}, "/bad%FF"), ({"a": 1}, "/a/b")]:
            with self.subTest(document=document, pointer=pointer):
                with self.assertRaises(checker.DiagnosisError):
                    checker.resolve_pointer(document, pointer)


class RefusalObservationTests(unittest.TestCase):
    def trace(self):
        point = {"trigger": {"kind": "rule-entry"}, "goal": "goal",
                 "goal_nonotation": "full goal", "hyps": [], "current_goals": [{}],
                 "shelf": [], "given_up": [],
                 "evars": {"availability": "complete", "entries": [], "show_existentials": "none"},
                 "hint_log": {"availability": "complete", "events": [], "filter": []},
                 "completeness": {"required_fields_complete": True, "missing_observations": []},
                 "refusal": [{"clause": "typed_guard", "exposure": "exposed",
                              "hand_call_index": 0, "message": "No matching clauses"}],
                 "hand_call": [{"clause": "typed_guard", "command": "existing_rule.",
                                "before": "before", "after_trial": "trial", "rollback": "rollback",
                                "feedback": "No matching clauses", "outcome": "refused",
                                "rollback_equal": True}]}
        return {"schema_version": 1, "points": [point], "residual": point}

    def test_exact_refusal_links_to_its_recorded_trial(self):
        trace = self.trace()
        result = checker.refusal_observation(trace, "/points/0/refusal/0/message")
        self.assertEqual(result["trial"]["command"], "existing_rule.")
        self.assertEqual(result["refusal"]["message"], "No matching clauses")
        self.assertEqual(checker.refusal_observation(trace, "/residual/refusal/0/clause"), result)

    def test_hidden_focus_frames_are_not_required(self):
        trace = self.trace()
        self.assertNotIn("hidden_focus_frames", trace["points"][0])
        checker.refusal_observation(trace, "/points/0/refusal/0/message")
        trace["points"][0]["hidden_focus_frames"] = {"availability": "unavailable"}
        checker.refusal_observation(trace, "/points/0/refusal/0/message")

    def test_unrelated_citation_does_not_establish_a_refusal(self):
        for pointer in ("/points/0/goal", "/points/0/hand_call/0/outcome", "/identity"):
            with self.subTest(pointer=pointer), self.assertRaises(checker.DiagnosisError):
                checker.refusal_observation(self.trace(), pointer)

    def test_invalid_call_index_outcome_clause_or_rollback_fails(self):
        mutations = [lambda p: p["refusal"][0].update(hand_call_index=9),
                     lambda p: p["refusal"][0].update(hand_call_index=True),
                     lambda p: p["hand_call"][0].update(outcome="accepted"),
                     lambda p: p["hand_call"][0].update(clause="different"),
                     lambda p: p["hand_call"][0].update(rollback_equal=None),
                     lambda p: p["hand_call"][0].update(before=None),
                     lambda p: p["hand_call"][0].update(command="")]
        for mutate in mutations:
            trace = self.trace()
            mutate(trace["points"][0])
            with self.subTest(mutation=mutate), self.assertRaises(checker.DiagnosisError):
                checker.refusal_observation(trace, "/points/0/refusal/0/message")

    def test_missing_observations_do_not_qualify(self):
        mutations = [lambda p: p["completeness"].update(required_fields_complete=False),
                     lambda p: p["completeness"].update(missing_observations=["evars"]),
                     lambda p: p["evars"].update(availability="unavailable"),
                     lambda p: p["hint_log"].update(availability="unavailable"),
                     lambda p: p.update(goal_nonotation=None),
                     lambda p: p.pop("hyps")]
        for mutate in mutations:
            trace = self.trace()
            mutate(trace["points"][0])
            with self.subTest(mutation=mutate), self.assertRaises(checker.DiagnosisError):
                checker.refusal_observation(trace, "/points/0/refusal/0/message")

    def test_unknown_schema_is_not_silently_accepted(self):
        trace = self.trace()
        trace["schema_version"] = 2
        with self.assertRaises(checker.DiagnosisError):
            checker.refusal_observation(trace, "/points/0/refusal/0/message")


class DiagnosisTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "workspace"
        self.root.mkdir()
        self.trace = self.root / "capture/TRACE.json"
        self.trace.parent.mkdir()
        self.trace.write_text(json.dumps({"anything": ["goal", "No clause", "observed fact",
                                                       "rewrite fact", "success"]}))
        self.path = self.root / "DIAGNOSIS.md"

    def citation(self, index=0):
        return f"`capture/TRACE.json#/anything/{index}`"

    def text(self, cycles=1):
        rows = [("trigger_goal", "observed goal", self.citation())]
        for number in range(1, cycles + 1):
            rows.extend([(f"cycle.{number}.refusal", '`No clause`', self.citation(1)),
                         (f"cycle.{number}.reason", "observed fact", self.citation(2)),
                         (f"cycle.{number}.normalization", "rewrite fact", self.citation(3)),
                         (f"cycle.{number}.next_refusal", '`success`', self.citation(4))])
        rows.extend([("terminal", "success", self.citation(4)),
                     ("candidate", " + ".join(f"cycle.{i}.normalization"
                                               for i in range(1, cycles + 1)), self.citation(3))])
        return "| Row | Evidence | Trace citations |\n|---|---|---|\n" + "\n".join(
            f"| {name} | {evidence} | {cites} |" for name, evidence, cites in rows) + "\n"

    def errors(self, text=None, template=False):
        self.path.write_text(self.text() if text is None else text)
        return checker.violations(self.path, template=template, structure_only=not template)

    def test_complete_diagnosis_resolves_arbitrary_json_shape(self):
        self.assertEqual(self.errors(), [])

    def markdown_links(self, text):
        return re.sub(r"`([^`]*TRACE\.json#[^`]*)`", r"[trace](\1)", text)

    def test_renderer_links_resolve_each_filled_row(self):
        self.assertEqual(self.errors(self.markdown_links(self.text())), [])

    def test_renderer_links_keep_pointer_and_local_file_checks(self):
        for target in ("capture/TRACE.json#/missing", "https://host/TRACE.json#/anything/0"):
            text = self.markdown_links(self.text()).replace("capture/TRACE.json#/anything/0", target)
            with self.subTest(target=target):
                self.assertTrue(self.errors(text))

    def test_every_filled_row_requires_its_own_citation(self):
        for name in ["trigger_goal", "cycle.1.refusal", "cycle.1.reason",
                     "cycle.1.normalization", "cycle.1.next_refusal", "terminal", "candidate"]:
            with self.subTest(row=name):
                lines = self.text().splitlines()
                lines = [line.rsplit("|", 2)[0] + "| |" if line.startswith(f"| {name} |")
                         else line for line in lines]
                self.assertTrue(any("needs a TRACE.json citation" in error
                                    for error in self.errors("\n".join(lines))))

    def test_completion_rejects_a_citation_placeholder_beside_a_valid_citation(self):
        text = self.text().replace(self.citation(), self.citation() + " TODO")
        self.assertTrue(self.errors(text))

    def test_unresolved_pointer_fails_even_with_another_valid_citation(self):
        text = self.text().replace(self.citation(), self.citation() + " `capture/TRACE.json#/missing`")
        self.assertTrue(any("does not exist" in error for error in self.errors(text)))

    def test_missing_or_invalid_trace_file_fails(self):
        self.trace.unlink()
        self.assertTrue(any("Cannot read" in error for error in self.errors()))
        self.trace.write_text("{")
        self.assertTrue(any("Cannot read" in error for error in self.errors()))

    def test_sibling_worktree_and_absolute_local_citations_are_allowed(self):
        sibling = self.root.parent / "other-worktree/TRACE.json"
        sibling.parent.mkdir()
        sibling.write_bytes(self.trace.read_bytes())
        for path in ("../other-worktree/TRACE.json", str(sibling)):
            with self.subTest(path=path):
                self.assertEqual(self.errors(self.text().replace("capture/TRACE.json", path)), [])

    def test_relative_citation_uses_the_diagnosis_directory(self):
        nested = self.root / "review"
        nested.mkdir()
        self.path = nested / "DIAGNOSIS.md"
        text = self.text().replace("capture/TRACE.json", "../capture/TRACE.json")
        self.assertEqual(self.errors(text), [])

    def test_non_trace_files_and_network_uris_are_rejected(self):
        for path in ("capture/data.json", "https://host/capture/TRACE.json"):
            with self.subTest(path=path):
                self.assertTrue(self.errors(self.text().replace("capture/TRACE.json", path)))

    def test_json_strings_are_never_executed(self):
        self.trace.write_text(json.dumps({"anything": ["$(touch forbidden)"] * 5}))
        self.assertEqual(self.errors(), [])
        self.assertFalse((self.root / "forbidden").exists())

    def test_repeated_cycles_and_candidate_sum(self):
        self.assertEqual(self.errors(self.text(cycles=2)), [])
        self.assertEqual(self.errors(self.text(cycles=5)), [])
        text = self.text(cycles=2).replace("cycle.1.normalization + cycle.2.normalization |",
                                         "cycle.1.normalization |")
        self.assertTrue(any("ordered sum" in error for error in self.errors(text)))

    def test_missing_duplicate_or_out_of_order_cycles_fail(self):
        for text in [self.text().replace("cycle.1.", "cycle.2."),
                     self.text().replace("| cycle.1.reason |", "| unknown |"),
                     self.text() + self.text().splitlines()[2] + "\n",
                     "\n".join(reversed(self.text().splitlines()))]:
            with self.subTest(text=text):
                self.assertTrue(self.errors(text))

    def test_placeholder_mode_is_explicit(self):
        template = "\n".join("| " + line.split("|")[1].strip() + " | TODO | TODO |"
                             if index >= 2 else line
                             for index, line in enumerate(self.text().splitlines()))
        self.assertEqual(self.errors(template, template=True), [])
        self.assertTrue(self.errors(template))
        partial = template.replace("| trigger_goal | TODO | TODO |",
                                   "| trigger_goal | observed | TODO |")
        self.assertTrue(self.errors(partial, template=True))

    def test_filled_template_rows_still_resolve_citations(self):
        self.assertTrue(self.errors(self.text().replace("/anything/0", "/missing"), template=True))

    def test_placeholder_words_inside_real_text_are_not_placeholder_cells(self):
        self.assertEqual(self.errors(self.text().replace("observed fact", "The pending goal has this form.")), [])

    def test_refusal_rows_require_quotes_and_terminal_is_explicit(self):
        self.assertTrue(any("quote" in error for error in
                            self.errors(self.text().replace('`No clause`', "No clause"))))
        self.assertTrue(any("terminal value" in error for error in
                            self.errors(self.text().replace("| terminal | success |", "| terminal | probably |"))))

    def test_escaped_markdown_pipe_preserves_the_exact_clause(self):
        text = self.text().replace('`No clause`', '`match a \\| b`')
        self.assertEqual(self.errors(text), [])
        self.assertEqual(checker.table_rows(text)[1][2], '`match a | b`')

    def test_empty_or_malformed_table_fails(self):
        self.assertTrue(self.errors("# Diagnosis\n"))
        self.assertTrue(self.errors("| one | two |\n"))

    def test_completed_validation_rejects_a_trace_without_provenance(self):
        self.path.write_text(self.text())
        errors = checker.violations(self.path)
        self.assertTrue(any("Semantic validation" in error for error in errors))

    def test_structure_only_mode_is_explicit_and_does_not_claim_completion(self):
        self.path.write_text(self.text())
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            self.assertEqual(checker.main(["--structure-only", str(self.path)]), 0)
        self.assertIn("Structure-only", output.getvalue())
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(checker.main([str(self.path)]), 1)

    def test_cli_returns_failure_for_unresolved_citations(self):
        self.path.write_text(self.text().replace("/anything/0", "/missing"))
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(checker.main(["--structure-only", "--root", str(self.root), str(self.path)]), 1)

    def test_repository_template_is_valid_only_in_template_mode(self):
        path = checker.ROOT / "build/stock-zisk/automation-validation/DIAGNOSIS.template.md"
        self.assertEqual(checker.violations(path, template=True), [])
        self.assertTrue(checker.violations(path))

class CompletedDiagnosisTests(unittest.TestCase):
    """Synthetic additive013 records test validation, not native closure."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / "DIAGNOSIS.md"
        self.trace_path = self.root / "TRACE.json"
        self.trace = self.make_trace()
        self.rows = [
            ("trigger_goal", '`raw goal`', "/points/0/goal"),
            ("cycle.1.refusal", '`typed_guard`; `No matching clauses`', "/points/0/refusal/0/message"),
            ("cycle.1.reason", '`raw equality`', "/points/0/hyps/0/type"),
            ("cycle.1.normalization", '`rewrite fact.`', "/points/0/hand_call/1/commands/0/command"),
            ("cycle.1.next_refusal", '`accepted`', "/points/0/hand_call/1/commands/1/outcome"),
            ("terminal", "success", "/verdict/status"),
            ("candidate", "cycle.1.normalization", "/points/0/hand_call/1/commands/0/command"),
        ]

    @staticmethod
    def capture(goal):
        return {"session_id": "logical-session", "goal": goal, "goal_nonotation": goal,
                "hyps": [{"names": ["H"], "type": "raw equality"}],
                "current_goals": [goal] if goal is not None else [], "shelf": [], "given_up": [],
                "evars": {"availability": "complete", "entries": [], "show_existentials": "none"},
                "completeness": {"required_fields_complete": True, "missing_observations": []}}

    @staticmethod
    def command(text, before, after, outcome="accepted"):
        return {"command": text, "before": "#/snapshots/" + before,
                "after": "#/snapshots/" + after, "outcome": outcome,
                "refusal": "No matching clauses" if outcome == "refused" else None}

    @classmethod
    def trial(cls, commands, outcome):
        return {"command": "existing_rule.", "clause": "typed_guard", "outcome": outcome,
                "before": "before", "after_trial": "trial", "rollback": "restored",
                "rollback_equal": True, "feedback": "observed feedback", "commands": commands}

    @classmethod
    def make_trace(cls):
        point = cls.capture("raw goal")
        point.update(trigger={"kind": "rule-entry"},
                     hint_log={"availability": "complete", "events": [], "filter": []},
                     refusal=[{"clause": "typed_guard", "exposure": "exposed",
                               "hand_call_index": 0, "message": "No matching clauses"}],
                     hand_call=[cls.trial([cls.command("existing_rule.", "raw", "raw", "refused")], "refused"),
                                cls.trial([cls.command("rewrite fact.", "raw", "normalized"),
                                           cls.command("existing_rule.", "normalized", "closed")], "accepted")])
        return {"schema_version": 1, "session": {"id": "logical-session"}, "points": [point],
                "snapshots": {"raw": cls.capture("raw goal"),
                              "normalized": cls.capture("normalized goal"), "closed": cls.capture(None)},
                "residual": None,
                "completion": {"trace_complete": True, "proof_closed": True, "reasons": [],
                               "closure_check": {"command": "Qed.", "accepted": True, "unresolved_evars": False}},
                "coverage": {"required_complete": True, "missing_event_ids": [], "unobserved_regions": [],
                             "traversal": "proof-closed"},
                "verdict": {"status": "actual-success", "scope": "whole-proof",
                            "evidence": "#/completion/closure_check"}}

    def errors(self):
        self.trace_path.write_text(json.dumps(self.trace))
        self.path.write_text("| Row | Evidence | Trace citations |\n|---|---|---|\n" + "\n".join(
            f"| {name} | {value} | " + " ".join(f"`TRACE.json#{p}`" for p in pointers.split()) + " |"
            for name, value, pointers in self.rows) + "\n")
        return checker.violations(self.path)

    def test_complete_same_session_normalization_and_actual_qed(self):
        self.assertEqual(self.errors(), [])

    def test_markdown_links_preserve_completed_semantic_checks(self):
        self.errors()
        text = self.path.read_text()
        self.path.write_text(re.sub(r"`(TRACE\.json#[^`]*)`", r"[trace](\1)", text))
        self.assertEqual(checker.violations(self.path), [])
        self.trace["verdict"].update(status="unresolved", evidence=None, scope="session")
        self.trace_path.write_text(json.dumps(self.trace))
        self.assertTrue(any("unresolved" in error for error in checker.violations(self.path)))

    def test_hidden_frames_absent_or_unavailable_are_accepted(self):
        self.trace["points"][0]["hidden_focus_frames"] = {"availability": "unavailable"}
        self.assertEqual(self.errors(), [])

    def test_goal_clause_refusal_and_reason_must_be_verbatim(self):
        for index in (0, 1, 2, 3):
            original = self.rows[index]
            self.rows[index] = (original[0], '`invented`', original[2])
            with self.subTest(row=index):
                self.assertTrue(self.errors())
            self.rows[index] = original

    def test_trigger_must_name_the_first_refusal_state(self):
        other = dict(self.trace["points"][0], goal="different goal", goal_nonotation="different goal")
        self.trace["points"].append(other)
        self.rows[0] = ("trigger_goal", '`different goal`', "/points/1/goal")
        self.assertTrue(any("first refusal state" in error for error in self.errors()))

    def test_session_identity_is_checked_on_points_and_snapshots(self):
        for record in (self.trace["points"][0], self.trace["snapshots"]["normalized"]):
            record["session_id"] = "different"
            self.assertTrue(self.errors())
            record["session_id"] = "logical-session"

    def test_complete_unresolved_trace_is_not_a_completed_diagnosis(self):
        self.trace["verdict"].update(status="unresolved", evidence=None, scope="session")
        self.assertTrue(any("unresolved" in error for error in self.errors()))
        self.assertTrue(self.trace["completion"]["trace_complete"])

    def test_unsatisfiability_needs_an_agreed_certificate_contract(self):
        self.trace["verdict"].update(status="established-unsatisfiable", evidence="#/points/0/refusal/0")
        self.rows[5] = ("terminal", "unsatisfiable", "/verdict/status")
        self.assertTrue(any("payload is not specified" in error for error in self.errors()))

    def test_progress_does_not_establish_success(self):
        self.trace["snapshots"]["closed"]["shelf"] = ["remaining obligation"]
        self.assertTrue(any("only made progress" in error for error in self.errors()))

    def test_qed_and_traversal_must_agree(self):
        for key, value in (("command", "Abort."), ("accepted", False), ("unresolved_evars", True)):
            record = self.trace["completion"]["closure_check"]
            old = record[key]
            record[key] = value
            with self.subTest(key=key):
                self.assertTrue(self.errors())
            record[key] = old
        self.trace["coverage"]["traversal"] = "first-residual"
        self.assertTrue(self.errors())

    def test_missing_snapshot_and_undefined_evars_fail(self):
        snapshot = self.trace["snapshots"].pop("normalized")
        self.assertTrue(self.errors())
        self.trace["snapshots"]["normalized"] = snapshot
        self.trace["snapshots"]["closed"]["evars"]["entries"] = [{"status": "undefined"}]
        self.assertTrue(self.errors())

    def test_refused_normalization_and_broken_state_chain_fail(self):
        command = self.trace["points"][0]["hand_call"][1]["commands"][0]
        command.update(outcome="refused", refusal="refused")
        self.assertTrue(self.errors())
        command.update(outcome="accepted", refusal=None, before="#/snapshots/normalized")
        self.assertTrue(self.errors())

    def test_different_rule_and_nonfinal_rule_fail(self):
        trial = self.trace["points"][0]["hand_call"][1]
        trial["command"] = "other_rule."
        trial["commands"][1]["command"] = "other_rule."
        self.assertTrue(self.errors())
        trial["command"] = "existing_rule."
        trial["commands"][1]["command"] = "existing_rule."
        trial["commands"].append(self.command("extra.", "closed", "closed"))
        self.assertTrue(self.errors())

    def test_candidate_must_cite_the_executed_normalizations(self):
        self.rows[6] = ("candidate", "cycle.1.normalization", "/points/0/hand_call/1/commands/1/command")
        self.assertTrue(self.errors())

    def test_distinct_trace_bundles_cannot_mix_even_with_equal_session_ids(self):
        self.errors()
        (self.root / "other").mkdir()
        (self.root / "other/TRACE.json").write_bytes(self.trace_path.read_bytes())
        self.path.write_text(self.path.read_text().replace("`TRACE.json#/verdict/status`", "`other/TRACE.json#/verdict/status`"))
        self.assertTrue(any("one exact" in error for error in checker.violations(self.path)))

    def test_escaped_snapshot_identifier_resolves(self):
        self.trace["snapshots"]["norm/with~tilde"] = self.trace["snapshots"].pop("normalized")
        commands = self.trace["points"][0]["hand_call"][1]["commands"]
        commands[0]["after"] = "#/snapshots/norm~1with~0tilde"
        commands[1]["before"] = commands[0]["after"]
        self.assertEqual(self.errors(), [])

    def test_repeated_cycles_require_the_exact_previous_refusal(self):
        point = self.trace["points"][0]
        # The second trial now refuses after its accepted normalization.
        point["hand_call"][1]["outcome"] = "refused"
        point["hand_call"][1]["commands"][1] = self.command("existing_rule.", "normalized", "normalized", "refused")
        point["refusal"].append(dict(point["refusal"][0], hand_call_index=1))
        normalized_point = dict(self.trace["snapshots"]["normalized"],
                                trigger={"kind": "rule-entry"}, hint_log=point["hint_log"],
                                refusal=[], hand_call=[])
        self.trace["points"].append(normalized_point)
        point["hand_call"].append(self.trial([self.command("simplify.", "normalized", "normalized"),
                                            self.command("existing_rule.", "normalized", "closed")], "accepted"))
        self.rows[4] = ("cycle.1.next_refusal", self.rows[1][1], "/points/0/refusal/1/message")
        self.rows[5:5] = [
            ("cycle.2.refusal", self.rows[1][1], "/points/0/refusal/1/message"),
            ("cycle.2.reason", '`raw equality`', "/points/1/hyps/0/type"),
            ("cycle.2.normalization", '`simplify.`', "/points/0/hand_call/2/commands/0/command"),
            ("cycle.2.next_refusal", '`accepted`', "/points/0/hand_call/2/commands/1/outcome")]
        self.rows[-1] = ("candidate", "cycle.1.normalization + cycle.2.normalization",
                         "/points/0/hand_call/1/commands/0/command /points/0/hand_call/2/commands/0/command")
        self.assertEqual(self.errors(), [])
        self.rows[5] = ("cycle.2.refusal", self.rows[1][1], "/points/0/refusal/0/message")
        self.assertTrue(any("preceding next refusal" in error for error in self.errors()))


if __name__ == "__main__":
    unittest.main()
