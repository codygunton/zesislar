"""Test evidence links with synthetic tool records, never native proof claims."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_decode_item_route_repair import SITES, acceptance, closed_groups, import_modules
from test_loop_negative_controls import synthetic_loop_controls


class SyntheticEvidence:
    """A complete fictional bundle for parser and attribution mutation tests."""

    def __init__(self, root, sites=SITES, repair_identity=None, control_names=None):
        self.root = root
        self.files = {}
        self.empty = {"goals": [], "stack": [], "shelf": [], "given_up": []}
        identity = repair_identity or {"module": "ZesuSsz.Automation.Switches.ResourceFirstIntroduction",
                    "class": "ZesuStepResourceFirstIntroduction",
                    "instance": "zesu_switch_resource_first_introduction"}
        imports = ["ZesuSsz.Automation.All", "ZesuSsz.Automation.Approved",
                   "ZesuSsz.Compliance.DecodeItemHints", identity["module"]]
        self.modules = {}
        for module in imports + ["ZesuSsz.Automation.Hooks", "ZesuSsz.Automation.Finish"]:
            text = "(* Synthetic source. No proof execution. *)\n"
            if module == identity["module"]:
                text += identity["class"] + " " + identity["instance"] + "\n"
            source = self.write(module.replace(".", "/") + ".v", text)
            obj = self.write("artifacts/" + module + ".vo", "synthetic object")
            self.modules[module] = {"source": source, "object": obj}
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "add", "ZesuSsz"], check=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], check=True)
        commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
        self.bundle = {"version": 2, "verification_root": commit, "repair_identity": identity,
                       "switch_source": self.modules[identity["module"]]["source"], "sessions": [],
                       "native_cases": [], "rejections": []}
        self.bundle["candidate_delta"] = {"base_root": commit,
                                            "source_overlays": [self.bundle["switch_source"]]}
        prefix = "".join("Require Import " + module + ".\n" for module in imports[:-1])
        controls = control_names or ["s119_literal_committed_witness_conflict", "s119_successor_committed_witness_conflict"]
        self.index = {"repair_identity": identity, "ON_imports": imports, "cases": [],
                      "reject_controls": controls,
                      "checked_module_source": self.write("checked.v", "(* fixture *)"),
                      "reviewed_terminal_package": self.write("terminal.json", "{}")}
        for site in sites:
            theorem = "DesignedBoundary_800d" + site
            statement = "Lemma " + theorem + " : True."
            original = prefix + statement + "\nProof. exact I. Qed.\n"
            self.index["cases"].append({"block": site, "native_theorem": theorem,
                "native_source": self.write("original/" + site + ".v", original),
                "native_statement": self.write("statements/" + site + ".txt", statement),
                "capture": self.write("captures/" + site + ".json", json.dumps(self.empty))})
            source = prefix + "Require Import " + identity["module"] + ".\n" + statement + "\nProof. zesu_block. Qed.\n"
            self.bundle["native_cases"].append(self.record(site, theorem, source, statement, True))
        control_text = "\n".join("Lemma " + name + " : True.\nProof. exact I. Qed." for name in controls)
        self.index["control_module"] = self.write("controls.v", control_text)
        for name in controls:
            self.bundle["rejections"].append(self.record(name, name, control_text, "Lemma " + name + " : True.", False))
        roles = {"hooks": self.modules["ZesuSsz.Automation.Hooks"]["source"],
                 "finish": self.modules["ZesuSsz.Automation.Finish"]["source"],
                 "approved": self.modules["ZesuSsz.Automation.Approved"]["source"],
                 "hints": self.modules["ZesuSsz.Compliance.DecodeItemHints"]["source"],
                 "plugins": [self.write("plugin.cmxs", "synthetic plugin")],
                 "mapping": self.write("_RocqProject", "-Q artifacts ZesuSsz\n"),
                 "findlib": self.write("findlib.json", "{}"),
                 "recipe": self.write("recipe.json", "{}")}
        inputs = {}
        for entry in self.modules.values():
            for reference in entry.values(): inputs[reference["path"]] = reference["sha256"]
        for record in self.bundle["native_cases"] + self.bundle["rejections"]:
            reference = record["proof_source"]; inputs[reference["path"]] = reference["sha256"]
        for role in roles.values():
            for reference in role if isinstance(role, list) else [role]:
                inputs[reference["path"]] = reference["sha256"]
        self.bundle["input_index"] = self.write("seal.json", {"root": commit, "workspace": str(root),
                                                    "inputs": inputs, "roles": roles, "modules": self.modules})
        self.refresh_attributions()
        self.index["loop_negative_controls"], self.bundle["loop_negative_controls"] = synthetic_loop_controls(root)

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not isinstance(value, str): value = json.dumps(value)
        path.write_text(value)
        return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

    def call(self, session, tool, arguments, result, **extra):
        return {"session_id": session["id"], "controller_owner": session["owner"],
                "tool": tool, "arguments": arguments, "request_UTC": "2026-10-11T00:00:00Z",
                "elapsed_seconds": 0.01, "raw_response": {"structuredContent": result}, **extra}

    def record(self, key, theorem, text, statement, native):
        source = self.write("proofs/Fixture" + key + ".v", text)
        obj = self.write("proofs/Fixture" + key + ".vo", "synthetic object")
        session = {"id": key, "workspace": str(self.root), "verification_root": self.bundle["verification_root"],
                   "owner": {"pid": len(self.bundle["sessions"]) + 1, "start_ticks": 100}}
        calls = [self.call(session, "rocq_health", {}, {"success": True}),
                 self.call(session, "rocq_start", {"workspace": str(self.root), "file": source["path"],
                                                    "theorem": theorem}, {"success": True, "state_id": 1})]
        activation = {}
        if native:
            identity = self.bundle["repair_identity"]
            for command in ["Check (_ : " + identity["class"] + ").", "Print " + identity["instance"] + "."]:
                activation[command] = len(calls)
                calls.append(self.call(session, "rocq_query", {"command": command},
                                       {"success": True}, context_state_id=1))
        exports = []
        export_attributions = []
        for state in [1, 2]:
            if state == 2:
                step = len(calls)
                calls.append(self.call(session, "rocq_check", {"from_state": 1,
                    "body": "zesu_block." if native else "exact I."},
                    {"success": True, "state_id": 2, "from_state_id": 1, "commands_run": 1}))
            groups = copy.deepcopy(self.empty)
            if state == 1: groups["shelf"] = [{"goal": "Original shelf, retained in the complete export."}]
            groups_ref = self.write("exports/" + key + str(state) + ".json", groups)
            result = {"success": True, "state_id": state, **groups_ref,
                "bytes": Path(groups_ref["path"]).stat().st_size, "active_goals": 0, "stack_entries": 0,
                "shelved_goals": len(groups["shelf"]), "given_up_goals": 0, "stack_frame_goal_counts": []}
            export_attributions.append(self.write("attribution/export-" + key + str(state) + ".json", {
                "method": "controller_complete_export", "session_id": key, "call": len(calls),
                "state_id": state, "workspace": str(self.root), "theorem": theorem,
                "source": source, "export": groups_ref}))
            exports.append(len(calls))
            calls.append(self.call(session, "rocq_complete_goals", {"from_state": state}, result))
        qed = len(calls)
        calls.append(self.call(session, "rocq_check", {"from_state": 2, "body": "Qed."},
                               {"success": True, "state_id": 3, "from_state_id": 2,
                                "commands_run": 1, "proof_finished": True}))
        compile_call = len(calls)
        calls.append(self.call(session, "rocq_compile_file", {"workspace": str(self.root), "file": source["path"]},
                               {"success": True}))
        verify_call = len(calls)
        calls.append(self.call(session, "rocq_verify", {"workspace": str(self.root), "proof": text,
                               "problem_name": theorem, "problem_statement": statement},
                               {"success": True, "verification_method": "module_m", "assumptions": []}))
        session["raw_calls"] = self.write("logs/" + key + ".json", calls)
        session["closure"] = self.write("closures/" + key + ".json", {"session_id": key, "owner": session["owner"],
            "transport_closed_normally": True, "server_exit_verified": True, "cleanup_signals_sent": 0,
            "termination_fallback_calls": 0, "pet": {"pid": 1000 + session["owner"]["pid"], "start_ticks": 101},
            "Pet_exit_verified": True})
        self.bundle["sessions"].append(session)
        trace = {"session_id": key, "health_call": 0, "start_call": 1, "steps": [step],
                 "exports": exports, "export_attributions": export_attributions, "qed_call": qed}
        if native: trace.update(activation_calls=activation, native_operation_call=step)
        record = {"proof_source": source, "compiled_object": obj, "proof_trace": trace,
                  "compilation": {"session_id": key, "health_call": 0, "call": compile_call},
                  "verification": {"session_id": key, "health_call": 0, "call": verify_call}}
        record["block" if native else "theorem"] = key
        return record

    def refresh_attributions(self):
        for record in self.bundle["native_cases"] + self.bundle["rejections"]:
            compile_record = record["compilation"]
            attribution = {"method": "controller_post_compile_hash", "session_id": compile_record["session_id"],
                "call": compile_record["call"], "workspace": str(self.root), "source": record["proof_source"],
                "object": record["compiled_object"], "input_index": self.bundle["input_index"]}
            compile_record["object_attribution"] = self.write("attribution/" + compile_record["session_id"] + ".json", attribution)

    def mutate_file(self, reference, mutation):
        path = Path(reference["path"])
        data = json.loads(path.read_text()); mutation(data)
        path.write_text(json.dumps(data)); reference["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()


class LinkedEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fixture = SyntheticEvidence(Path(self.temp.name).resolve())
        self.bundle = self.fixture.bundle
        self.case = self.bundle["native_cases"][0]

    def tearDown(self):
        self.temp.cleanup()

    def check(self):
        return acceptance(self.fixture.index, self.bundle, self.fixture.root)

    def reject(self):
        with self.assertRaises((ValueError, KeyError, TypeError)):
            self.check()

    def session(self):
        return self.bundle["sessions"][0]

    def mutate_calls(self, mutation):
        self.fixture.mutate_file(self.session()["raw_calls"], mutation)

    def test_complete_synthetic_evidence_passes(self):
        self.assertEqual(len(self.check()), 9)

    def test_production_export_response_has_no_invented_identity(self):
        calls = json.loads(Path(self.session()["raw_calls"]["path"]).read_text())
        for position in self.case["proof_trace"]["exports"]:
            result = calls[position]["raw_response"]["structuredContent"]
            self.assertFalse(set(result) & {"source", "source_sha256", "theorem", "workspace",
                                            "groups_are_actual", "truncated"})
        self.assertEqual(len(self.check()), 9)

    def test_missing_export_attribution_rejects(self):
        self.case["proof_trace"].pop("export_attributions")
        self.reject()

    def test_wrong_export_theorem_attribution_rejects(self):
        reference = self.case["proof_trace"]["export_attributions"][-1]
        self.fixture.mutate_file(reference, lambda data: data.update(theorem="foreign"))
        self.reject()

    def change_hooks(self, overlay):
        reference = self.fixture.modules["ZesuSsz.Automation.Hooks"]["source"]
        path = Path(reference["path"])
        path.write_text(path.read_text() + "(* Candidate Hooks change. *)\n")
        reference["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        if overlay:
            self.bundle["candidate_delta"]["source_overlays"].append(reference)
        def update(seal):
            seal["inputs"][str(path)] = reference["sha256"]
            seal["roles"]["hooks"] = reference
            seal["modules"]["ZesuSsz.Automation.Hooks"]["source"] = reference
        self.fixture.mutate_file(self.bundle["input_index"], update)
        self.fixture.refresh_attributions()

    def test_uncommitted_hooks_overlay_passes(self):
        self.change_hooks(True)
        self.assertEqual(len(self.check()), 9)

    def test_omitted_hooks_change_rejects(self):
        self.change_hooks(False)
        self.reject()

    def test_duplicate_source_overlay_rejects(self):
        self.bundle["candidate_delta"]["source_overlays"].append(self.bundle["switch_source"])
        self.reject()

    def test_alias_overlay_duplicate_rejects(self):
        reference = copy.deepcopy(self.bundle["switch_source"])
        path = Path(reference["path"])
        reference["path"] = str(path.parent / ".." / path.parent.name / path.name)
        self.bundle["candidate_delta"]["source_overlays"].append(reference)
        self.reject()

    def test_frozen_generated_overlay_requires_generation_provenance(self):
        self.bundle["switch_source"]["kind"] = "frozen_generated_input"
        self.reject()

    def test_malformed_group_values_never_mean_closed(self):
        for group in self.fixture.empty:
            for bad in [None, {}, "", False, 0]:
                data = copy.deepcopy(self.fixture.empty); data[group] = bad
                with self.subTest(group=group, bad=bad), self.assertRaises(ValueError): closed_groups(data)

    def test_malformed_focus_frame_rejects(self):
        data = copy.deepcopy(self.fixture.empty); data["stack"] = [[{}, []]]
        with self.assertRaises(ValueError): closed_groups(data)

    def test_nested_comments_do_not_create_imports(self):
        self.assertEqual(import_modules('(* Require Import Fake. (* nested *) *)\nFrom Coq Require Import List ZArith.'),
                         ["Coq.List", "Coq.ZArith"])

    def test_session_splicing_rejects(self):
        self.case["proof_trace"]["session_id"] = self.bundle["sessions"][1]["id"]
        self.reject()

    def test_controller_owner_splicing_rejects(self):
        self.mutate_calls(lambda calls: calls[1].update(controller_owner={"pid": 999, "start_ticks": 9}))
        self.reject()

    def test_workspace_mismatch_rejects(self):
        self.session()["workspace"] = str(self.fixture.root / "foreign")
        self.reject()

    def test_start_file_mismatch_rejects(self):
        self.mutate_calls(lambda calls: calls[1]["arguments"].update(file="foreign.v"))
        self.reject()

    def test_advancing_state_mismatch_rejects(self):
        position = self.case["proof_trace"]["steps"][0]
        self.mutate_calls(lambda calls: calls[position]["raw_response"]["structuredContent"].update(from_state_id=99))
        self.reject()

    def test_export_state_mismatch_rejects(self):
        position = self.case["proof_trace"]["exports"][-1]
        self.mutate_calls(lambda calls: calls[position]["raw_response"]["structuredContent"].update(state_id=99))
        self.reject()

    def test_missing_initial_export_rejects(self):
        self.case["proof_trace"]["exports"].pop(0)
        self.reject()

    def test_intermediate_shelf_type_rejects(self):
        position = self.case["proof_trace"]["exports"][0]
        def mutation(calls):
            result = calls[position]["raw_response"]["structuredContent"]
            self.fixture.mutate_file(result, lambda groups: groups.update(shelf=None))
            result["bytes"] = Path(result["path"]).stat().st_size
        self.mutate_calls(mutation)
        self.reject()

    def test_native_tactic_substring_rejects(self):
        position = self.case["proof_trace"]["steps"][0]
        self.mutate_calls(lambda calls: calls[position]["arguments"].update(body="(* zesu_block *) exact I."))
        self.reject()

    def test_native_request_with_no_commands_rejects(self):
        position = self.case["proof_trace"]["steps"][0]
        self.mutate_calls(lambda calls: calls[position]["raw_response"]["structuredContent"].update(commands_run=0))
        self.reject()

    def test_activation_query_context_mismatch_rejects(self):
        position = next(iter(self.case["proof_trace"]["activation_calls"].values()))
        self.mutate_calls(lambda calls: calls[position].update(context_state_id=99))
        self.reject()

    def test_qed_from_other_state_rejects(self):
        position = self.case["proof_trace"]["qed_call"]
        self.mutate_calls(lambda calls: calls[position]["arguments"].update(from_state=99))
        self.reject()

    def test_successful_compile_does_not_replace_object_attribution(self):
        self.fixture.mutate_file(self.case["compilation"]["object_attribution"], lambda data: data.update(call=99))
        self.reject()

    def test_explicit_vos_with_stale_vo_rejects(self):
        # The retained synthetic .vo already exists. A vos pass cannot certify it.
        self.assertTrue(Path(self.case["compiled_object"]["path"]).is_file())
        position = self.case["compilation"]["call"]
        self.mutate_calls(lambda calls: calls[position]["arguments"].update(mode="vos"))
        self.reject()

    def test_explicit_full_compile_passes(self):
        position = self.case["compilation"]["call"]
        self.mutate_calls(lambda calls: calls[position]["arguments"].update(mode="full"))
        self.assertEqual(len(self.check()), 9)

    def test_unrelated_compiled_object_rejects(self):
        self.case["compiled_object"] = self.fixture.write("proofs/Unrelated.vo", "unrelated")
        self.reject()

    def test_verify_assumptions_rejects(self):
        position = self.case["verification"]["call"]
        self.mutate_calls(lambda calls: calls[position]["raw_response"]["structuredContent"].update(assumptions=["axiom"]))
        self.reject()

    def test_verify_other_theorem_rejects(self):
        position = self.case["verification"]["call"]
        self.mutate_calls(lambda calls: calls[position]["arguments"].update(problem_name="other"))
        self.reject()

    def test_missing_explicit_cleanup_count_rejects(self):
        self.fixture.mutate_file(self.session()["closure"], lambda data: data.pop("cleanup_signals_sent"))
        self.reject()

    def test_closure_owner_mismatch_rejects(self):
        self.fixture.mutate_file(self.session()["closure"], lambda data: data.update(owner={"pid": 999, "start_ticks": 9}))
        self.reject()

    def test_unrelated_switch_only_seal_rejects(self):
        switch = self.bundle["switch_source"]
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data.update(inputs={switch["path"]: switch["sha256"]}))
        self.fixture.refresh_attributions()
        self.reject()

    def test_missing_transitive_module_rejects(self):
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data["modules"].pop("ZesuSsz.Automation.All"))
        self.fixture.refresh_attributions()
        self.reject()

    def test_missing_activation_role_rejects(self):
        self.fixture.mutate_file(self.bundle["input_index"], lambda data: data["roles"].pop("hooks"))
        self.fixture.refresh_attributions()
        self.reject()

    def test_rejection_control_requires_linked_compile(self):
        self.bundle["rejections"][0].pop("compilation")
        self.reject()


if __name__ == "__main__":
    unittest.main()
