"""Synthetic parser controls. These fixtures supply no proof evidence."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from check_decode_item_route_repair import LOOP_NEGATIVE_IDS, loop_negative_controls


def synthetic_loop_controls(root):
    def write(name, value):
        path = root / "negative" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value if isinstance(value, str) else json.dumps(value))
        return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

    cases, records = [], []
    for site, control_id in zip(("6a24", "6ac4"), LOOP_NEGATIVE_IDS):
        theorem, certificate = "negative_" + site, "successor_" + site
        statement = "Lemma " + certificate + " : True."
        source = write(site + ".v", statement + "\nProof. exact I. Qed.\nLemma " + theorem + " : True.\nProof. Abort.")
        captured = write(site + "-context.json", {"kernel_goal": {"hyps": [], "ty": "committed_i"}})
        target = write(site + "-target.txt", "committed_i\n")
        expected = write(site + "-statement.txt", statement)
        exported = write(site + "-export.json", {"goals": [{}], "stack": [], "shelf": [], "given_up": [],
                                              "kernel_groups": {"goals": [{}]}})
        export = dict(exported, state_id=3, active_goals=1, stack_entries=0, shelved_goals=0,
                      given_up_goals=0, groups_are_actual=True, truncated=False)
        body = "exact successor_" + site + "."
        trial = {"results": [{"success": False, "reason": "tactic_failed", "error": "synthetic mismatch"}]}
        fixture = {"name": theorem, "site": site, "original_index": 1, "file": source["path"],
                   "certificate_name": certificate, "target": "committed_i"}
        row = {"fixture": fixture, "exact_certificate_statement": statement, "trial": trial,
               "operations": [{"after": export}], "rollback": export, "final": export,
               "advancement": None, "native_assignment_executed": False}
        scope = {"frozen_root": "frozen", "artifact_scope": "synthetic", "successor_root": "successor",
                 "successor_measurement_root": "measurement"}
        report = write(site + "-report.json", {"bindings": {}, "frozen_root": "frozen",
                                              "artifact_scope": "synthetic", "rows": [row]})
        phase = "exact-" + theorem
        calls = [{"phase": phase, "tool": "rocq_health", "arguments": {}, "result": {"success": True}},
                 {"phase": phase, "tool": "rocq_start", "arguments": {"theorem": theorem, "file": source["path"]},
                  "result": {"success": True}},
                 {"phase": phase, "tool": "rocq_step_multi", "arguments": {"tactics": [body], "from_state": 3},
                  "result": trial}]
        raw = [dict(c, raw_response={"structuredContent": c["result"]}) for c in calls]
        successor = write(site + "-successor.json", {"production_root": "successor", "measurement_root": "measurement",
                         "rows": [{"theorem": certificate, "verification": {"success": True, "assumptions": []},
                                   "advancing_Qed": True, "compiled_closed_assumptions": True}]})
        closure = {"phase": phase, "transport_closed_normally": True, "server_exit_verified": True,
                   "Pet_exit_verified": True, "work_success": True, "cleanup_signals_sent": 0}
        cases.append({"control_id": control_id, "header": site, "theorem": theorem, "certificate_name": certificate,
                      "trial_body": body, "scope": scope, "negative_report": report, "proof_source": source,
                      "certificate_source": source, "captured_context": captured, "target": target,
                      "certificate_statement": expected, "successor_report": successor,
                      "input_index": write(site + "-seal.json", {"root": "frozen", "inputs": {source["path"]: source["sha256"]}}),
                      "call_log": write(site + "-calls.json", calls), "raw_calls": write(site + "-raw.json", raw),
                      "closures": write(site + "-closure.json", [closure])})
        records.append({"control_id": control_id, "negative_report": report})
    return cases, records


class LoopNegativeControlsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.cases, self.records = synthetic_loop_controls(self.root)
        self.index = {"loop_negative_controls": self.cases}

    def tearDown(self):
        self.temp.cleanup()

    def check(self):
        return loop_negative_controls(self.index, self.records, self.root)

    def mutate(self, reference, change):
        path = Path(reference["path"])
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))
        reference["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()

    def reject(self):
        with self.assertRaises((ValueError, KeyError, TypeError)):
            self.check()

    def test_complete_negative_applications_pass(self):
        self.assertEqual([r["closed_certificate"] for r in self.check()], [False, False])

    def test_missing_control_rejects(self):
        self.records.pop()
        self.reject()

    def test_wrong_control_rejects(self):
        self.records[0]["control_id"] = self.records[1]["control_id"]
        self.reject()

    def test_changed_bytes_reject(self):
        Path(self.cases[0]["target"]["path"]).write_text("stepped_i")
        self.reject()

    def test_changed_target_rejects(self):
        self.mutate(self.cases[0]["captured_context"], lambda d: d["kernel_goal"].update(ty="stepped_i"))
        self.reject()

    def test_changed_scope_rejects(self):
        self.cases[0]["scope"]["frozen_root"] = "other"
        self.reject()

    def test_successful_application_rejects(self):
        self.mutate(self.cases[0]["negative_report"], lambda d: d["rows"][0]["trial"]["results"][0].update(success=True))
        self.reject()

    def test_changed_command_rejects(self):
        self.cases[0]["trial_body"] = "exact another_fact."
        self.reject()

    def test_changed_rollback_rejects(self):
        def change(data):
            data["rows"][0]["rollback"] = dict(data["rows"][0]["rollback"], sha256="0" * 64)
        self.mutate(self.cases[0]["negative_report"], change)
        self.reject()

    def test_truncated_groups_reject(self):
        self.mutate(self.cases[0]["negative_report"], lambda d: d["rows"][0]["final"].update(truncated=True))
        self.reject()

    def test_incomplete_groups_reject(self):
        self.mutate(self.cases[0]["negative_report"], lambda d: d["rows"][0]["final"].update(groups_are_actual=False))
        self.reject()

    def test_nonempty_assumptions_reject(self):
        self.mutate(self.cases[0]["successor_report"], lambda d: d["rows"][0]["verification"].update(assumptions=["axiom"]))
        self.reject()

    def test_abnormal_closure_rejects(self):
        self.mutate(self.cases[0]["closures"], lambda d: d[0].update(cleanup_signals_sent=1))
        self.reject()


if __name__ == "__main__":
    unittest.main()
