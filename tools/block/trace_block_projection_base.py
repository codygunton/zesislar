"""Project retained events one invocation or snapshot at a time.

This draft starts no server, compiler, or proof command. Use it only after the
owned capture closes. Runtime paths remain in this view and its evidence seal.
"""

from collections import defaultdict
import hashlib
import json
from pathlib import Path

from trace_block import logical_session_id
from trace_block_mcp import stable_capture, convert_entry_events


class ProjectionView:
    def __init__(self, request, evidence_dir):
        self.request = request
        self.directory = Path(evidence_dir)
        self.session_path = self.directory / "SESSION.json"
        self.session = json.loads(self.session_path.read_text())
        self.session_id = logical_session_id(request)
        identity = self.session["ownership"]["pet"]
        if identity is None:
            raise ValueError("The retained session has no owned Pet identity.")
        self.paths = sorted((self.directory / "events" /
                             ("process-%d" % identity["pid"])).glob("event-*.json"))
        self.rows = []
        self.by_invocation = defaultdict(list)
        self.points = []
        self.snapshot_rows = {}
        self.lookups = []
        self.residual_rows = []
        self.missing_feedback_attribution = []
        self.missing_checkpoint_attribution = False
        self.event_seal = []
        for index, path in enumerate(self.paths):
            payload = path.read_bytes()
            row = json.loads(payload)
            row.pop("capture", None)
            row.pop("message", None)
            row.pop("refusal", None)
            self.rows.append(row)
            self.event_seal.append({"path": str(path.relative_to(self.directory)),
                                    "sha256": hashlib.sha256(payload).hexdigest()})
            del payload
            kind = row["kind"]
            number = row.get("invocation")
            self.by_invocation[number].append(index)
            if kind == "feedback" and "invocation" not in row:
                self.missing_feedback_attribution.append(index)
            if kind == "native-entry":
                self.points.append((index, "native"))
                self.snapshot_rows["invocation-%d:entry" % number] = index
            elif kind in ("hand-accepted", "hand-rollback"):
                suffix = "after" if kind == "hand-accepted" else "rollback"
                key = "invocation-%d:clause-%s:" % (number, row["clause"])
                self.snapshot_rows[key + suffix] = index
                if suffix == "rollback":
                    self.snapshot_rows.setdefault(key + "after", index)
            elif kind == "checkpoint":
                if (row["rule"] in ("residual", "instruction-lookup", "requested-trigger")
                        and "trial" not in row):
                    self.missing_checkpoint_attribution = True
                if row.get("trial") is not False:
                    continue
                if row["rule"] == "residual":
                    self.residual_rows.append(index)
                elif row["rule"] == "instruction-lookup":
                    self.lookups.append(index)
                elif row["rule"] == "requested-trigger":
                    self.points.append((index, "checkpoint"))
        self.points.sort()
        marker = 0
        for index, kind in self.points:
            if kind == "checkpoint":
                marker += 1
                self.snapshot_rows["requested-trigger-%d" % marker] = index
        if self.residual_rows:
            self.snapshot_rows["residual"] = self.residual_rows[-1]
        final_ref = self.session["final_snapshot"]
        self.final = None
        if final_ref is not None:
            payload = Path(final_ref["path"]).read_bytes()
            if hashlib.sha256(payload).hexdigest() != final_ref["sha256"]:
                raise ValueError("The retained final snapshot hash changed.")
            self.final = json.loads(payload)
        self.header = self._header()

    def _row(self, index):
        return json.loads(self.paths[index].read_text())

    @property
    def snapshot_keys(self):
        return tuple(self.snapshot_rows)

    def get_snapshot(self, key):
        if key == "residual":
            value = self.residual
            return {name: value[name] for name in stable_capture(
                self._row(self.residual_rows[-1])["capture"])}
        return stable_capture(self._row(self.snapshot_rows[key])["capture"])

    def iter_points(self):
        for ordinal, (index, kind) in enumerate(self.points):
            if kind == "native":
                number = self.rows[index]["invocation"]
                rows = [self._row(i) for i in self.by_invocation[number]]
                point, = convert_entry_events(rows, self.request["entry_descriptors"],
                                              self.session_id)
                if any(i > index for i in self.missing_feedback_attribution):
                    point["hint_log"]["availability"] = "unavailable"
                    point["completeness"]["required_fields_complete"] = False
            else:
                point = stable_capture(self._row(index)["capture"])
                point.update(session_id=self.session_id,
                    trigger={"kind": self.request["stop"]["kind"], "rule": None,
                             "matches_stop": True, "entry": "Hooks.zesu_liAStep",
                             "branch": "typed checkpoint"},
                    hint_log={"availability": "complete",
                              "filter": ["typed requested-trigger checkpoint"],
                              "events": []}, hand_call=[], refusal=[])
            point["trigger"]["ordinal"] = ordinal
            yield point

    def iter_instruction_visits(self):
        for index in self.lookups:
            yield {"kind": "instruction-lookup",
                   **stable_capture(self._row(index)["capture"])}

    @property
    def residual(self):
        if not self.residual_rows:
            return None
        if self.final is None:
            raise ValueError("The inline residual has no final MCP capture.")
        value = stable_capture(self._row(self.residual_rows[-1])["capture"])
        outer = self.final["goals"]
        a, b = outer["notation"]["goals"], outer["no_notation"]["goals"]
        if len(a) != len(b):
            raise ValueError("The residual printers returned different groups.")
        value["current_goals"] = [{"goal": left["ty"],
            "goal_nonotation": right["ty"], "hyps": [
                {"names": x["names"], "type": x["ty"],
                 "type_nonotation": y["ty"], "body": x.get("def"),
                 "body_nonotation": y.get("def")}
                for x, y in zip(left["hyps"], right["hyps"])]}
            for left, right in zip(a, b)]
        if value["current_goals"]:
            value.update({key: value["current_goals"][0][key]
                          for key in ("goal", "goal_nonotation", "hyps")})
        value.update(session_id=self.session_id, trigger={"kind": "residual"},
            hand_call=[], refusal=[], hint_log={"availability": "complete",
                "filter": ["residual liShow and Show Proof"], "events": []},
            show_proof={"availability": "complete", "text": "\n".join(
                message["message"] for message in self.final["show_proof"]["messages"])})
        return value

    def _header(self):
        request, session = self.request, self.session
        ownership, closure = session["ownership"], session["closure_check"]
        counts = {name: sum(kind == "native" and request["entry_descriptors"][
            self.rows[index]["rule"]]["rule"] == name for index, kind in self.points)
            for name in request["selected_rules"]}
        if request["stop"]["kind"] == "residual":
            occurred = bool(self.residual_rows)
        elif request["stop"]["kind"] == "rule":
            occurred = counts.get(request["stop"]["value"], 0) > 0
        else:
            occurred = any(kind == "checkpoint" for _, kind in self.points) or any(
                row["kind"] == "hand-accepted" and row.get("clause") == "requested-trigger"
                for row in self.rows)
        reasons = []
        if self.missing_checkpoint_attribution:
            reasons.append("An observed checkpoint lacks explicit native/trial attribution.")
        if session["error"] is not None:
            reasons.append("The owned session failed. See the complete runtime evidence.")
        if not session["source_unchanged"]:
            reasons.append("The stable source changed during the session.")
        if not ownership["transport_closed_normally"] or ownership["owned_pet_exited"] is not True:
            reasons.append("The owned session did not close normally.")
        if not request.get("instrumentation", {}).get("entry_coverage_complete"):
            reasons.append("The preparation did not establish complete entry instrumentation.")
        if not request.get("instrumentation", {}).get("instruction_coverage_complete"):
            reasons.append("The preparation did not establish complete instruction lookup instrumentation.")
        if closure is None and not self.residual_rows:
            reasons.append("The complete residual capture is unavailable.")
        obligations = {"availability": "unavailable", "session": self.session_id,
            "counts": None, "undefined_evars": None,
            "evidence": "evidence/SESSION.json#/final_snapshot"}
        if self.final is not None and self.final.get("complete") is True:
            groups = self.final["goals"]["no_notation"]
            obligations["counts"] = {"goals": len(groups["goals"]),
                "stack": sum(len(left) + len(right) for left, right in groups["stack"]),
                "shelf": len(groups["shelf"]), "given_up": len(groups["given_up"])}
            if self.residual_rows:
                obligations["undefined_evars"] = sum(not entry["defined"] for entry in
                    self._row(self.residual_rows[-1])["capture"]["no_notation"]["evars"])
            elif closure is not None and self.final["evars"] == {"availability": "complete", "messages": []}:
                obligations["undefined_evars"] = 0
            if obligations["undefined_evars"] is not None:
                obligations["availability"] = "complete"
        return {"identity": {**request["scope"], "switches": {
                "requested": request["rule_set"], "actual_instances": session["actual_switches"]},
                "instrumentation": request["instrumentation"]},
            "session": {"id": self.session_id, "runtime": "evidence/SESSION.json#/ownership/pet"},
            "pet_start_tick": "evidence/SESSION.json#/ownership/pet/start_ticks",
            "verdict": {"status": "actual-success" if closure else "unresolved",
                "kind": "proof_closure" if closure else None, "session": self.session_id,
                "scope": "whole-proof" if closure else "session",
                "evidence": "#/completion/closure_check" if closure else None,
                "reason": "The kernel accepted Qed." if closure else
                          "The trace establishes no terminal success or unsatisfiability certificate."},
            "coverage": {"required_complete": not reasons, "entry_events": counts,
                "captured_events": counts, "missing_event_ids": [],
                "unobserved_regions": [] if not reasons else reasons,
                "requested_trigger": "occurred" if occurred else "not-occurred",
                "traversal": "proof-closed" if closure else "first-residual"},
            "completion": {"trace_complete": not reasons, "proof_closed": closure is not None,
                "reasons": reasons, "closure_check": closure, "final_obligations": obligations},
            "evidence": {"path": str(self.session_path),
                "sha256": hashlib.sha256(self.session_path.read_bytes()).hexdigest()},
            "owned_closure": ownership}
