"""Select actual native triggers from closed, immutable raw captures."""

import hashlib
import json
from pathlib import Path

from trace_block_projection_base import ProjectionView as AllEntryView
from trace_block_selection import classify


class ProjectionView(AllEntryView):
    def __init__(self, request, evidence_dir, *, guards_path=None):
        super().__init__(request, evidence_dir)
        guards_path = guards_path or Path(__file__).with_name("GUARDS.json")
        guards_bytes = Path(guards_path).read_bytes()
        self.guard_sha256 = hashlib.sha256(guards_bytes).hexdigest()
        if self.guard_sha256 != "2e67fe39db8d42db20a8223802eb8f34d404ff62ac4ea6e62e516292355b6f78":
            raise ValueError("The selection guard record differs from supplement040.")
        guards = json.loads(guards_bytes)["commands"]
        self.decisions = []
        selected = []
        self.attempted = dict.fromkeys(request["selected_rules"], 0)
        self.actual = dict.fromkeys(request["selected_rules"], 0)
        for index, kind in self.points:
            if kind != "native":
                continue
            entry = self._row(index)
            if entry.get("trial") is True:
                continue
            if entry.get("trial") is not False:
                raise ValueError("A native entry lacks explicit non-trial attribution.")
            descriptor = request["entry_descriptors"][entry["rule"]]
            rule = descriptor["rule"]
            if rule not in self.attempted:
                continue
            self.attempted[rule] += 1
            rows = [self._row(item) for item in self.by_invocation[entry["invocation"]]]
            decision, reason = classify(entry, rows, descriptor, guards)
            self.decisions.append({"event": index, "invocation": entry["invocation"],
                                   "client": entry["rule"], "rule": rule,
                                   "classification": decision, "reason": reason})
            if decision == "actual-trigger":
                self.actual[rule] += 1
                selected.append((index, "native"))
        self.raw_requested_checkpoint = any(kind == "checkpoint" for _, kind in self.points)
        self.points = selected
        retained = {self.rows[index]["invocation"] for index, _ in selected}
        self.snapshot_rows = {key: value for key, value in self.snapshot_rows.items()
            if key == "residual" or (key.startswith("invocation-")
                and int(key.split(":", 1)[0].removeprefix("invocation-")) in retained)}
        # The first native residual is the boundary. Never substitute a later one.
        self.multiple_residuals = len(self.residual_rows) > 1
        if self.residual_rows:
            self.residual_rows = self.residual_rows[:1]
            self.snapshot_rows["residual"] = self.residual_rows[0]
        self.header = self._selected_header()

    def _selected_header(self):
        value = self._header()
        coverage = value["coverage"]
        if self.request["stop"]["kind"] not in ("residual", "rule") and self.raw_requested_checkpoint:
            coverage["requested_trigger"] = "occurred"
        coverage.update(attempted_entries=self.attempted, actual_triggers=self.actual,
                        entry_events=self.actual, captured_events=self.actual,
                        requested_trigger_instruction_list=[], raw_event_index="raw/INDEX.json")
        value["instruction_visits"] = []
        unknown = [row for row in self.decisions if row["classification"] == "unknown"]
        if unknown:
            reason = "Some attempted entries have an unresolved trigger classification. See raw/INDEX.json."
            coverage["unobserved_regions"].append(reason)
            value["completion"]["reasons"].append(reason)
            coverage["required_complete"] = False
            value["completion"]["trace_complete"] = False
        if self.multiple_residuals:
            reason = "Several residual checkpoints prevent association of Show Proof with the first residual."
            coverage["unobserved_regions"].append(reason)
            value["completion"]["reasons"].append(reason)
            coverage["required_complete"] = False
            value["completion"]["trace_complete"] = False
        return value

    def iter_instruction_visits(self):
        return iter(())

    def write_raw_index(self, path):
        """Write an external index. The bundle seal binds this file's hash."""
        path = Path(path)
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists():
            raise FileExistsError(path)
        with path.open("x") as stream:
            stream.write('{"schema":1,"selection_policy":"039+040","guards_sha256":')
            json.dump(self.guard_sha256, stream)
            stream.write(',"session":')
            json.dump(self.session_id, stream)
            stream.write(',"events":[')
            for index, event in enumerate(self.event_seal):
                if index:
                    stream.write(",")
                json.dump(event, stream, ensure_ascii=False, separators=(",", ":"))
            stream.write('],"attempted_entries":[')
            for index, decision in enumerate(self.decisions):
                if index:
                    stream.write(",")
                json.dump({**decision, "event": self.event_seal[decision["event"]]}, stream,
                          ensure_ascii=False, separators=(",", ":"))
            stream.write('],"instruction_lookups":[')
            for index, event_index in enumerate(self.lookups):
                if index:
                    stream.write(",")
                json.dump(self.event_seal[event_index], stream, separators=(",", ":"))
            stream.write('],"requested_checkpoints":[')
            checkpoints = [index for index, row in enumerate(self.rows)
                if row["kind"] == "checkpoint" and row.get("rule") == "requested-trigger"
                and row.get("trial") is False]
            for index, event_index in enumerate(checkpoints):
                if index:
                    stream.write(",")
                json.dump(self.event_seal[event_index], stream, separators=(",", ":"))
            stream.write(']}\n')
        return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
