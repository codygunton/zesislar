#!/usr/bin/env python3
"""Write complete, deterministic native trace bundles from owned MCP captures.

The backend observes live rule entries. This module checks coverage and renders
its data. Synthetic renderer fixtures do not certify the live observer.
"""

import argparse
import copy
import hashlib
import importlib
import json
from pathlib import Path
import re
import sys
import subprocess

SCHEMA_VERSION = 1
POINT_KEYS = ("trigger", "goal", "goal_nonotation", "hyps", "evars",
              "hint_log", "hand_call", "refusal", "current_goals", "shelf",
              "given_up", "hidden_focus_frames", "completeness")
TOP_KEYS = ("identity", "instruction_visits", "coverage", "completion")
NAME = r"[A-Za-z_][A-Za-z0-9_]*"


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False,
                       allow_nan=False) + "\n").encode()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse_pc(value):
    if not re.fullmatch(r"(?:0[xX])?[0-9a-fA-F]+", value):
        raise argparse.ArgumentTypeError("The block must be a hexadecimal PC.")
    number = int(value, 16)
    if number >= 2 ** 64:
        raise argparse.ArgumentTypeError("The PC exceeds 64 bits.")
    return hex(number)


def parse_rules(value):
    rules = {}
    for item in value.split(","):
        match = re.fullmatch("(" + NAME + r")=(on|off)", item.strip())
        if not match:
            raise argparse.ArgumentTypeError("Use comma-separated NAME=on/off assignments.")
        name, setting = match.groups()
        if name in rules:
            raise argparse.ArgumentTypeError("The rule is assigned twice: " + name)
        rules[name] = setting == "on"
    return [{"name": name, "enabled": rules[name]} for name in sorted(rules)]


def parse_stop(value):
    if value.startswith("pc:"):
        return {"kind": "pc", "value": parse_pc(value[3:])}
    if value in ("jalr", "WriteMem", "FindMemMapsTo"):
        return {"kind": "instruction", "value": value}
    if value == "mem_mapsto_kind":
        return {"kind": "goal-head", "value": value}
    if re.fullmatch(r"LiTactic\s*\(normalize_instr_addr _\)", value):
        return {"kind": "goal-head", "value": "LiTactic(normalize_instr_addr _)"}
    if value == "residual":
        return {"kind": "residual", "value": None}
    if re.fullmatch("rule:" + NAME, value):
        return {"kind": "rule", "value": value[5:]}
    raise argparse.ArgumentTypeError("The stop trigger is not supported: " + value)


def pointer(*segments):
    return "/" + "/".join(str(segment).replace("~", "~0").replace("/", "~1")
                            for segment in segments)


from trace_block_text import StreamText
from collections.abc import Mapping, Sequence


def _sequence(value):
    return isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray))

def _full_text(value, label, errors):
    if isinstance(value, StreamText):
        if not value.complete_text():
            errors.append(label + " contains truncated or hidden text.")
    elif not isinstance(value, str):
        errors.append(label + " is unavailable.")
    elif "..." in value or "…" in value or value.strip() == "HIDDEN":
        errors.append(label + " contains truncated or hidden text.")


def _all_text(value, label, errors):
    """Check every text leaf without changing feedback structure or order."""
    if isinstance(value, (str, StreamText)):
        _full_text(value, label, errors)
    elif _sequence(value):
        for index, item in enumerate(value):
            _all_text(item, label + "/" + str(index), errors)
    elif isinstance(value, Mapping):
        for key, item in value.items():
            _all_text(item, label + "/" + str(key), errors)


def _snapshot_ref(value, label, errors, snapshots=None):
    if not isinstance(value, str) or not value:
        errors.append(label + " lacks its logical snapshot reference.")
        return None
    _full_text(value, label, errors)
    key = snapshot_key(value) if value.startswith("#") else value
    if key is None or (snapshots is not None and key not in snapshots):
        errors.append(label + " does not resolve into snapshots.")
        return None
    return key


def _feedback_messages(value, label, errors):
    if isinstance(value, (str, StreamText)):
        _full_text(value, label, errors)
        return [value] if value else []
    if _sequence(value):
        messages = []
        for index, item in enumerate(value):
            name = label + "/" + str(index)
            if isinstance(item, Mapping) and isinstance(item.get("message"), (str, StreamText)):
                messages.append(item["message"])
                _all_text(item, name, errors)
            else:
                errors.append(name + " lacks complete feedback text.")
        return messages
    errors.append(label + " lacks complete feedback text.")
    return []


def _hyps(value, label, errors):
    if not _sequence(value):
        errors.append(label + " is unavailable.")
        return
    for index, hyp in enumerate(value):
        name = label + "/" + str(index)
        if not isinstance(hyp, Mapping):
            errors.append(name + " is not a hypothesis record.")
            continue
        if (not _sequence(hyp.get("names")) or not hyp["names"]
                or not all(isinstance(n, str) and n for n in hyp["names"])):
            errors.append(name + " lacks exact local names.")
        for field in ("type", "type_nonotation"):
            _full_text(hyp.get(field), name + "/" + field, errors)
        if "body" not in hyp or "body_nonotation" not in hyp:
            errors.append(name + " lacks definition availability.")
        elif (hyp["body"] is None) != (hyp["body_nonotation"] is None):
            errors.append(name + " has different definition availability across printers.")
        elif hyp["body"] is not None:
            for field in ("body", "body_nonotation"):
                _full_text(hyp[field], name + "/" + field, errors)


def _goal(value, label, errors):
    if not isinstance(value, Mapping):
        errors.append(label + " is unavailable.")
        return
    _full_text(value.get("goal"), label + "/goal", errors)
    _full_text(value.get("goal_nonotation"), label + "/goal_nonotation", errors)
    _hyps(value.get("hyps"), label + "/hyps", errors)


def _capture_fields(value, label, errors):
    for group in ("current_goals", "shelf", "given_up"):
        goals = value.get(group)
        if not _sequence(goals):
            errors.append(label + "/" + group + " is unavailable.")
            continue
        for index, goal in enumerate(goals):
            _goal(goal, label + "/" + group + "/" + str(index), errors)
    current = value.get("current_goals")
    if _sequence(current) and current:
        _goal(value, label, errors)
        for field in ("goal", "goal_nonotation", "hyps"):
            if value.get(field) != current[0].get(field):
                errors.append(label + "/" + field + " differs from the primary current goal.")
    elif current == []:
        if value.get("goal") is not None or value.get("goal_nonotation") is not None:
            errors.append(label + " reports a primary goal for an empty current group.")
        if value.get("hyps") != []:
            errors.append(label + " reports a primary context for an empty current group.")
    evars = value.get("evars", {})
    if not isinstance(evars, Mapping) or evars.get("availability") != "complete":
        errors.append(label + " lacks the complete live Evd map.")
    else:
        entries = evars.get("entries")
        if not _sequence(entries):
            errors.append(label + " lacks live Evd entries.")
        else:
            seen = set()
            for index, entry in enumerate(entries):
                key = label + "/evars/entries/" + str(index)
                if not isinstance(entry, Mapping):
                    errors.append(key + " is not an Evd record.")
                    continue
                identifier = entry.get("id")
                if not isinstance(identifier, (int, str)) or identifier in seen:
                    errors.append(key + " lacks a unique exact Evd identifier.")
                seen.add(identifier)
                if entry.get("status") not in ("defined", "undefined"):
                    errors.append(key + " lacks an Evd status.")
                for field in ("type", "type_nonotation"):
                    _full_text(entry.get(field), key + "/" + field, errors)
                _hyps(entry.get("context"), key + "/context", errors)
                for field in ("body", "body_nonotation"):
                    if entry.get("status") == "defined":
                        _full_text(entry.get(field), key + "/" + field, errors)
                    elif field not in entry or entry[field] is not None:
                        errors.append(key + " lacks an explicit undefined body.")
        _full_text(evars.get("show_existentials"), label + "/evars/show_existentials", errors)


def _point(value, label, errors, residual=False, snapshots=None, session_id=None):
    if not isinstance(value, Mapping):
        errors.append(label + " is unavailable.")
        return
    for key in POINT_KEYS:
        if key not in value:
            errors.append(label + " lacks " + key + ".")
    trigger = value.get("trigger")
    if not isinstance(trigger, Mapping) or not trigger.get("kind"):
        errors.append(label + " lacks an actual trigger identity.")
    _capture_fields(value, label, errors)
    logs = value.get("hint_log", {})
    if (not isinstance(logs, Mapping) or logs.get("availability") != "complete"
            or not _sequence(logs.get("filter"))
            or not _sequence(logs.get("events"))):
        errors.append(label + " lacks complete filtered hint logs.")
    _all_text(logs, label + "/hint_log", errors)
    trials = value.get("hand_call")
    refusals = value.get("refusal")
    if not _sequence(refusals):
        errors.append(label + " lacks refusal availability.")
        refusals = []
    for index, refusal in enumerate(refusals):
        name = label + "/refusal/" + str(index)
        if not isinstance(refusal, Mapping):
            errors.append(name + " lacks a refusal record.")
            continue
        _full_text(refusal.get("message"), name + "/message", errors)
        _all_text(refusal, name, errors)
        trial_index = refusal.get("hand_call_index")
        if (type(trial_index) is not int or not _sequence(trials)
                or not 0 <= trial_index < len(trials)
                or not isinstance(trials[trial_index], Mapping)
                or trials[trial_index].get("outcome") != "refused"):
            errors.append(name + " lacks a matching refused trial index.")
    if not _sequence(trials) or (isinstance(trigger, Mapping)
            and trigger.get("kind") == "rule-entry" and not trials):
        errors.append(label + " lacks hand-call observations.")
    elif _sequence(trials):
        for index, trial in enumerate(trials):
            name = label + "/hand_call/" + str(index)
            if not isinstance(trial, Mapping):
                errors.append(name + " lacks a trial record.")
                continue
            if trial.get("outcome") not in ("accepted", "refused") or trial.get("rollback_equal") is not True:
                errors.append(name + " lacks exact trial rollback.")
            if not isinstance(trial.get("command"), str) or not trial["command"]:
                errors.append(name + " lacks its command.")
            for field in ("before", "after_trial", "rollback"):
                _snapshot_ref(trial.get(field), name + "/" + field, errors, snapshots)
            messages = _feedback_messages(trial.get("feedback"), name + "/feedback", errors)
            _all_text(trial, name, errors)
            if trial.get("outcome") == "refused":
                message = trial.get("message", messages[-1] if messages else None)
                _full_text(message, name + "/message", errors)
                if not message:
                    errors.append(name + " lacks the exact refusal message.")
                matching = [r for r in refusals if isinstance(r, Mapping)
                            and type(r.get("hand_call_index")) is int
                            and r["hand_call_index"] == index]
                if (len(matching) != 1 or matching[0].get("message") != message
                        or matching[0].get("clause") != trial.get("clause")):
                    errors.append(name + " lacks its matching refusal message and index.")
    hidden = value.get("hidden_focus_frames", {})
    if (not isinstance(hidden, Mapping) or hidden.get("availability") not in ("complete", "unavailable")
            or (hidden.get("availability") == "unavailable" and not hidden.get("reason"))):
        errors.append(label + " lacks the hidden-frame API limit.")
    if value.get("completeness", {}).get("required_fields_complete") is not True:
        errors.append(label + " reports incomplete required fields.")
    if session_id is not None and value.get("session_id") != session_id:
        errors.append(label + " has a different session identity.")
    if _sequence(trials):
        for index, trial in enumerate(trials):
            if not isinstance(trial, Mapping):
                continue
            name = label + "/hand_call/" + str(index)
            commands = trial.get("commands")
            if not _sequence(commands) or not commands:
                errors.append(name + " lacks ordered command records.")
                continue
            if len(commands) != 1:
                errors.append(name + " contains unsupported composite command records.")
            for command_index, command in enumerate(commands):
                location = name + "/commands/" + str(command_index)
                if not isinstance(command, Mapping):
                    errors.append(location + " lacks its command record.")
                    continue
                _full_text(command.get("command"), location + "/command", errors)
                if len(commands) == 1 and command.get("command") != trial.get("command"):
                    errors.append(location + " differs from the recorded trial command.")
                if command.get("outcome") not in ("accepted", "refused"):
                    errors.append(location + " lacks its actual outcome.")
                if command.get("outcome") == "refused":
                    _full_text(command.get("refusal"), location + "/refusal", errors)
                    message = trial.get("message")
                    if message is None:
                        messages = _feedback_messages(trial.get("feedback"), name + "/feedback", errors)
                        message = messages[-1] if messages else None
                    if command_index == len(commands) - 1 and command.get("refusal") != message:
                        errors.append(location + " differs from the trial refusal.")
                elif "refusal" not in command or command["refusal"] is not None:
                    errors.append(location + " lacks an explicit empty refusal.")
                for field in ("before", "after"):
                    reference = command.get(field)
                    key = snapshot_key(reference)
                    if key is None or (snapshots is not None and key not in snapshots):
                        errors.append(location + "/" + field + " does not resolve into snapshots.")
            if isinstance(commands[-1], Mapping) and commands[-1].get("outcome") != trial.get("outcome"):
                errors.append(name + " has a different final command outcome.")
            before = _snapshot_ref(trial.get("before"), name + "/before", errors, snapshots)
            after = _snapshot_ref(trial.get("after_trial"), name + "/after_trial", errors, snapshots)
            rollback = _snapshot_ref(trial.get("rollback"), name + "/rollback", errors, snapshots)
            if isinstance(commands[0], Mapping) and snapshot_key(commands[0].get("before")) != before:
                errors.append(name + " has a command-before pointer outside its entry snapshot.")
            if isinstance(commands[-1], Mapping) and snapshot_key(commands[-1].get("after")) != after:
                errors.append(name + " has a command-after pointer outside its trial snapshot.")
            for previous, following in zip(commands, commands[1:]):
                if not isinstance(previous, Mapping) or not isinstance(following, Mapping):
                    continue
                if snapshot_key(previous.get("after")) != snapshot_key(following.get("before")):
                    errors.append(name + " has a discontinuous command snapshot chain.")
                if previous.get("outcome") != "accepted":
                    errors.append(name + " continues after a refused command.")
            if snapshots is not None and before in snapshots and rollback in snapshots:
                if snapshots[before] != snapshots[rollback]:
                    errors.append(name + " has different entry and rollback snapshots.")
                fields = ("goal", "goal_nonotation", "hyps", "current_goals", "shelf", "given_up", "evars")
                if residual and trial.get("scope") == "residual-leaf":
                    fields = tuple(field for field in fields if field != "current_goals")
                    goals = snapshots[before].get("current_goals", [])
                    current = value.get("current_goals", [])
                    selected = trial.get("selected_goal_id")
                    if (type(selected) is not int or not goals or not current
                            or goals[0].get("id") != selected or current[0].get("id") != selected
                            or trial.get("execution") != "SDK-discarded" or trial.get("native_entry") is not False):
                        errors.append(name + " lacks its exact discarded residual leaf.")
                if any(snapshots[before].get(field) != value.get(field) for field in fields):
                    errors.append(name + " has an entry snapshot different from its rule point.")

    if residual:
        proof = value.get("show_proof", {})
        if not isinstance(proof, Mapping) or proof.get("availability") != "complete":
            errors.append(label + " lacks residual Show Proof.")
        else:
            _full_text(proof.get("text"), label + "/show_proof/text", errors)


def snapshot_key(reference):
    if not isinstance(reference, str) or not reference.startswith("#/snapshots/"):
        return None
    segment = reference[len("#/snapshots/"):]
    if not segment or "/" in segment or re.search(r"~(?![01])", segment):
        return None
    return segment.replace("~1", "/").replace("~0", "~")


def logical_session_id(request):
    inputs = {key: request[key] for key in ("block_pc", "rule_set", "stop", "scope") if key in request}
    return "trace-session-" + hashlib.sha256(json_bytes(inputs)).hexdigest()


def empty_final_obligations(trace):
    record = trace["completion"].get("final_obligations", {})
    return (isinstance(record, Mapping) and record.get("availability") == "complete"
            and record.get("session") == trace["session"]["id"]
            and isinstance(record.get("counts"), Mapping)
            and set(record["counts"]) == {"goals", "stack", "shelf", "given_up"}
            and all(type(value) is int and value == 0 for value in record["counts"].values())
            and type(record.get("undefined_evars")) is int and record["undefined_evars"] == 0
            and (record.get("evidence") == "evidence/SESSION.json#/final_snapshot"
                 or (record.get("evidence") == "evidence/SESSION.json#/final_obligations"
                     and record.get("method") == "kernel-accepted-Qed")))


def observed_verdict(trace):
    """Credit actual success only. A tactic refusal is not an unsatisfiability proof."""
    unresolved = {"status": "unresolved", "kind": None, "session": trace["session"]["id"],
                  "evidence": None, "scope": "session",
                  "reason": "No terminal named-rule evidence, accepted Qed, or unsatisfiability certificate was established."}
    if not trace["completion"]["trace_complete"]:
        return dict(unresolved, reason="The required trace capture remains incomplete.")
    if trace["completion"].get("proof_closed") and empty_final_obligations(trace):
        return {"status": "actual-success", "kind": "proof_closure", "session": trace["session"]["id"],
                "evidence": "#/completion/closure_check",
                "scope": "whole-proof", "reason": "The owned session accepted Qed."}
    for i, point in enumerate(trace["points"]):
        if point.get("trigger", {}).get("kind") != "rule-entry":
            continue
        for j, trial in enumerate(point["hand_call"]):
            if trial.get("clause") != "whole-rule" or trial.get("outcome") != "accepted":
                continue
            commands = trial.get("commands", [])
            if not commands:
                continue
            before_ref, after_ref = commands[0].get("before"), commands[-1].get("after")
            before = trace["snapshots"].get(snapshot_key(before_ref), {})
            after = trace["snapshots"].get(snapshot_key(after_ref), {})
            goals = before.get("current_goals", [])
            entry_ids = [goal.get("id") for goal in goals]
            if not entry_ids or any(type(identifier) not in (int, str) for identifier in entry_ids):
                continue
            if any(snapshot.get("evars", {}).get("availability") != "complete" for snapshot in (before, after)):
                continue
            before_entries = before["evars"].get("entries", [])
            after_entries = after["evars"].get("entries", [])
            before_map = {entry["id"]: entry for entry in before_entries}
            after_map = {entry["id"]: entry for entry in after_entries}
            if any(before_map.get(identifier, {}).get("status") != "undefined"
                   or after_map.get(identifier, {}).get("status") != "defined" for identifier in entry_ids):
                continue
            before_undefined = [entry["id"] for entry in before_entries if entry["status"] == "undefined"]
            after_undefined = [entry["id"] for entry in after_entries if entry["status"] == "undefined"]
            if not set(after_undefined) <= set(before_undefined):
                continue
            remaining = [goal.get("id") for group in ("current_goals", "shelf", "given_up")
                         for goal in after.get(group, [])]
            if any(type(identifier) not in (int, str) for identifier in remaining) or set(entry_ids) & set(remaining):
                continue
            return {"status": "actual-success", "kind": "rule_success", "session": trace["session"]["id"],
                    "scope": "named-rule",
                    "evidence": "#" + pointer("points", i, "hand_call", j),
                    "reason": "The trial defined every entry goal and introduced no remaining undefined evar.",
                    "terminal_check": {"before": before_ref, "after": after_ref,
                        "entry_goal_evars": entry_ids, "before_undefined_evars": before_undefined,
                        "after_undefined_evars": after_undefined}}
    return unresolved


def build_trace(request, result, *, streaming=False):
    """Preserve required capture data. Reject missing internal observations."""
    trace = {"schema_version": SCHEMA_VERSION,
             "request": copy.deepcopy({k: request[k] for k in
                 ("block_pc", "rule_set", "stop", "scope") if k in request}),
             "points": [], "residual": None,
             "runtime_evidence": "evidence/SESSION.json",
             "session": {"id": logical_session_id(request), "runtime": "evidence/SESSION.json#/ownership/pet"},
             "pet_start_tick": "evidence/SESSION.json#/ownership/pet/start_ticks",
             "snapshots": copy.deepcopy(result.get("snapshots", {}))}
    for key in TOP_KEYS:
        trace[key] = copy.deepcopy(result.get(key, {} if key != "instruction_visits" else []))
    def point_record(index, point):
        record = {key: point[key] if streaming else copy.deepcopy(point[key])
                  for key in POINT_KEYS if key in point}
        record["id"] = "point-%04d" % index
        record["session_id"] = point.get("session_id", trace["session"]["id"])
        return record

    if streaming:
        from trace_block_stream import ReplayList
        trace["points"] = ReplayList(lambda: (
            point_record(index, point) for index, point in enumerate(result.get("points", []))))
    else:
        trace["points"] = [point_record(index, point)
                           for index, point in enumerate(result.get("points", []))]
    if isinstance(result.get("residual"), Mapping):
        trace["residual"] = {key: copy.deepcopy(result["residual"][key])
                             for key in POINT_KEYS + ("show_proof",)
                             if key in result["residual"]}
    if isinstance(trace["residual"], Mapping):
        trace["residual"]["session_id"] = result["residual"].get("session_id", trace["session"]["id"])
    errors = []
    snapshots = trace["snapshots"]
    if not isinstance(snapshots, Mapping):
        errors.append("The actual snapshots map is unavailable.")
        snapshots = trace["snapshots"] = {}
    for key, snapshot in snapshots.items():
        label = pointer("snapshots", key)
        if not isinstance(snapshot, Mapping):
            errors.append(label + " is unavailable.")
            continue
        if isinstance(snapshot, dict):
            snapshot.setdefault("session_id", trace["session"]["id"])
        if snapshot.get("session_id") != trace["session"]["id"]:
            errors.append(label + " has a different session identity.")
        _capture_fields(snapshot, label, errors)
    identity = trace["identity"]
    if not isinstance(identity, Mapping):
        errors.append("Source identity is unavailable.")
    else:
        for field, size in (("root", 40), ("source_sha256", 64), ("statement_sha256", 64)):
            if not re.fullmatch(r"[0-9a-f]{%d}" % size, str(identity.get(field, ""))):
                errors.append("Source identity lacks " + field + ".")
    scope = request.get("scope")
    if not isinstance(scope, Mapping):
        errors.append("The request lacks its exact source scope.")
    elif isinstance(identity, Mapping):
        for field in ("root", "source", "source_sha256", "statement_sha256"):
            if field not in scope or identity.get(field) != scope[field]:
                errors.append("Source identity differs from request.scope: " + field + ".")
        if identity.get("prefix") != scope.get("prefix"):
            errors.append("Source identity differs from request.scope: prefix.")
    for index, point in enumerate(trace["points"]):
        _point(point, "/points/" + str(index), errors, snapshots=snapshots, session_id=trace["session"]["id"])
    coverage = trace["coverage"]
    if not isinstance(coverage, Mapping):
        errors.append("Required coverage is unavailable.")
        coverage = trace["coverage"] = {}
    if coverage.get("required_complete") is not True:
        errors.append("Internal entry coverage is incomplete.")
    for field in ("missing_event_ids", "unobserved_regions"):
        if coverage.get(field) != []:
            errors.append("Coverage contains missing observations: " + field + ".")
    if (not isinstance(coverage.get("entry_events"), Mapping)
            or coverage.get("entry_events") != coverage.get("captured_events")):
        errors.append("Entry events and captured events do not match.")
    counts = coverage.get("captured_events")
    if isinstance(counts, Mapping):
        actual = {}
        for point in trace["points"]:
            trigger = point.get("trigger", {})
            if isinstance(trigger, Mapping) and trigger.get("kind") == "rule-entry":
                rule = trigger.get("rule")
                if not isinstance(rule, str) or not rule:
                    errors.append("A rule entry lacks its rule name.")
                else:
                    actual[rule] = actual.get(rule, 0) + 1
        if (any(type(count) is not int or count < 0 for count in counts.values())
                or {key: count for key, count in counts.items() if count} != actual):
            errors.append("Captured event counts differ from the retained points.")
    if coverage.get("requested_trigger") not in ("occurred", "not-occurred"):
        errors.append("The requested trigger is unobserved.")
    if not _sequence(coverage.get("requested_trigger_instruction_list")):
        errors.append("The complete instruction list is unavailable.")
    if coverage.get("requested_trigger_instruction_list") != trace["instruction_visits"]:
        errors.append("The requested-trigger instruction list differs from the traversal.")
    if any(field in coverage for field in ("attempted_entries", "actual_triggers", "raw_event_index")):
        attempted, actual = coverage.get("attempted_entries"), coverage.get("actual_triggers")
        selected_rules = set(request.get("selected_rules", [row["name"] for row in request.get("rule_set", [])]))
        if (not isinstance(attempted, Mapping) or not isinstance(actual, Mapping)
                or set(attempted) != selected_rules or set(actual) != selected_rules
                or any(type(value) is not int or value < 0 for value in attempted.values())
                or any(type(value) is not int or value < 0 for value in actual.values())):
            errors.append("Selected coverage lacks exact attempted-entry and actual-trigger counts.")
        elif (any(actual[key] > attempted[key] for key in actual)
                or actual != coverage.get("captured_events") or actual != coverage.get("entry_events")):
            errors.append("Attempted entries, actual triggers, and captured events disagree.")
        if coverage.get("raw_event_index") != "raw/INDEX.json":
            errors.append("Selected coverage lacks the external raw event index.")
        if trace["instruction_visits"] != [] or coverage.get("requested_trigger_instruction_list") != []:
            errors.append("Selected traces must retain instruction lookups only in the raw index.")
        expected_snapshots = {"residual"} if trace["residual"] is not None else set()
        for point in trace["points"]:
            if point.get("trigger", {}).get("kind") != "rule-entry":
                errors.append("A selected trace contains a point outside an actual rule trigger.")
            for trial in point.get("hand_call", []):
                for field in ("before", "after_trial", "rollback"):
                    reference = trial.get(field)
                    key = snapshot_key(reference) if isinstance(reference, str) and reference.startswith("#") else reference
                    if isinstance(key, str):
                        expected_snapshots.add(key)
        if trace["residual"] is not None:
            for trial in trace["residual"].get("hand_call", []):
                for field in ("before", "after_trial", "rollback"):
                    reference = trial.get(field)
                    key = snapshot_key(reference) if isinstance(reference, str) and reference.startswith("#") else reference
                    if isinstance(key, str):
                        expected_snapshots.add(key)
        if set(snapshots) != expected_snapshots:
            errors.append("Selected snapshots contain missing or unrelated raw observations.")
    completion = trace["completion"]
    if isinstance(completion, Mapping):
        completion = trace["completion"] = {key: completion[key] for key in
            ("trace_complete", "proof_closed", "reasons", "closure_check", "final_obligations") if key in completion}
    if not isinstance(completion, Mapping):
        completion = trace["completion"] = {}
    if completion.get("proof_closed") is True:
        check = completion.get("closure_check", {})
        if (not isinstance(check, Mapping) or check.get("command") != "Qed."
                or check.get("accepted") is not True or check.get("unresolved_evars") is not False):
            errors.append("Proof closure lacks a successful Qed record.")
            completion["proof_closed"] = False
        if not empty_final_obligations(trace):
            errors.append("Proof closure lacks complete empty final obligations.")
            completion["proof_closed"] = False
        if trace["residual"] is not None or coverage.get("traversal") != "proof-closed":
            errors.append("The proof-closure record contradicts the traversal.")
    else:
        _point(trace["residual"], "/residual", errors, residual=True, snapshots=snapshots, session_id=trace["session"]["id"])
        if coverage.get("traversal") != "first-residual":
            errors.append("Traversal did not reach the first residual or closure.")
    reasons = completion.get("reasons", [])
    if not _sequence(reasons):
        reasons = ["Backend completion reasons are malformed."]
    completion["reasons"] = []
    for collection in (reasons, errors):
        for reason in collection:
            if reason not in completion["reasons"]:
                completion["reasons"].append(reason)
    completion["trace_complete"] = (completion.get("trace_complete") is True
                                      and not completion["reasons"])
    trace["verdict"] = observed_verdict(trace)
    supplied = result.get("verdict")
    verdict_errors = []
    if supplied is not None:
        if isinstance(supplied, Mapping) and supplied.get("session") != trace["session"]["id"]:
            verdict_errors.append("The supplied verdict has a different or unavailable session identity.")
        if isinstance(supplied, Mapping) and (supplied.get("kind") == "refutation" or supplied.get("certificate") is not None):
            verdict_errors.append("The supplied refutation claim has no supported certificate validator.")
        if not isinstance(supplied, Mapping) or supplied.get("status") not in ("actual-success", "unresolved"):
            verdict_errors.append("The supplied terminal claim has no supported certificate validator.")
        elif supplied["status"] == "actual-success":
            derived = trace["verdict"]
            if (derived["status"] != "actual-success" or supplied.get("evidence") != derived["evidence"]
                    or supplied.get("scope") != derived["scope"] or supplied.get("kind") != derived["kind"]
                    or supplied.get("session") != derived["session"]):
                verdict_errors.append("The supplied success claim lacks matching terminal evidence.")
        elif supplied.get("evidence") is not None or supplied.get("kind") is not None:
            verdict_errors.append("The unresolved supplied verdict contains an unsupported terminal claim.")
    if verdict_errors:
        completion["reasons"].extend(verdict_errors)
        completion["trace_complete"] = False
        trace["verdict"] = observed_verdict(trace)
    return trace


def _fence(text):
    text = str(text)
    runs = [len(match.group()) for match in re.finditer(r"`+", text)]
    fence = "`" * max(3, max(runs, default=0) + 1)
    return fence + "\n" + text + ("" if text.endswith("\n") else "\n") + fence + "\n"


def render_markdown(trace):
    """Render every stable field without truncating terms or reordering lists."""
    lines = ["# Native trace\n", "Trace completeness: " + str(trace["completion"]["trace_complete"]).lower() + ".\n",
             "Proof closure: " + str(trace["completion"].get("proof_closed", False)).lower() + ".\n"]
    for key in ("identity", "session", "pet_start_tick", "request", "coverage", "instruction_visits", "snapshots", "completion", "verdict"):
        lines += ["## " + key + "\n", _fence(json_bytes(trace[key]).decode())]
    records = [("points/" + str(i), p) for i, p in enumerate(trace["points"])]
    if trace["residual"] is not None:
        records.append(("residual", trace["residual"]))
    for location, point in records:
        lines.append("## " + location + "\n")
        segments = location.split("/")
        for key in ("id", "session_id") + POINT_KEYS + (("show_proof",) if location == "residual" else ()):
            if key not in point:
                continue
            citation = "TRACE.json#" + pointer(*segments, key)
            lines.append("### " + key + "\n\n" + citation + "\n")
            value = point[key]
            lines.append(_fence(value if isinstance(value, str) else json_bytes(value).decode()))
    if trace["residual"] is None:
        lines.append("## residual\n\nNo residual capture is present. See the completion record.\n")
    return "\n".join(lines)


def write_bundle(out_dir, trace):
    """Write both immutable outputs after checking every existing target."""
    out_dir = Path(out_dir)
    outputs = {"TRACE.json": json_bytes(trace),
               "TRACE.md": render_markdown(trace).encode()}
    for name, payload in outputs.items():
        path = out_dir / name
        if path.exists() and path.read_bytes() != payload:
            raise ValueError("The output already contains different bytes: " + name)
    out_dir.mkdir(parents=True, exist_ok=True)
    for name, payload in outputs.items():
        path = out_dir / name
        if not path.exists():
            with path.open("xb") as stream:
                stream.write(payload)
    return {name: hashlib.sha256(payload).hexdigest() for name, payload in outputs.items()}


def resolve_request(request):
    """Bind the original declaration and exact prefix without splitting tactics."""
    workspace = Path(request["workspace"]).resolve()
    source = request.get("source")
    if source:
        source = Path(source)
        source = (workspace / source).resolve() if not source.is_absolute() else source.resolve()
    else:
        filename = "Block" + request["block_pc"][2:] + ".v"
        candidates = sorted((workspace / "ZesuSsz" / "Proofs").rglob(filename))
        if len(candidates) != 1:
            raise ValueError("The block source is missing or ambiguous. Supply --source.")
        source = candidates[0].resolve()
    if not source.is_relative_to(workspace):
        raise ValueError("The source leaves the declared workspace.")
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from residual.modules import parse_module
    proofs = parse_module(source)
    theorem = request.get("theorem")
    selected = [p for p in proofs if p.name == theorem] if theorem else [
        p for p in proofs if p.name == "DesignedBoundary_" + request["block_pc"][2:]]
    if len(selected) != 1 or selected[0].inline:
        raise ValueError("The theorem is missing, ambiguous, or lacks a separate Proof line.")
    proof = selected[0]
    data = source.read_bytes()
    lines = data.decode("utf-8").splitlines(keepends=True)
    declaration = "".join(lines[proof.declaration_line:proof.proof_line])
    prefix = request.get("prefix_file")
    prefix_text = ""
    prefix_binding = None
    if prefix:
        prefix = Path(prefix)
        prefix = (workspace / prefix).resolve() if not prefix.is_absolute() else prefix.resolve()
        if not prefix.is_relative_to(workspace):
            raise ValueError("The retained prefix leaves the declared workspace.")
        prefix_text = prefix.read_bytes().decode("utf-8")
        prefix_binding = {"path": prefix.relative_to(workspace).as_posix(), "sha256": sha256(prefix)}
    root = subprocess.check_output(["git", "-C", str(workspace), "rev-parse", "HEAD"], text=True).strip()
    return dict(request, source=str(source), theorem=proof.name,
                prefix_file=str(prefix) if prefix else None, prefix_text=prefix_text,
                declaration=declaration,
                source_prefix="".join(lines[:proof.proof_line + 1]),
                scope={"root": root, "source": source.relative_to(workspace).as_posix(),
                       "source_sha256": hashlib.sha256(data).hexdigest(),
                       "statement_sha256": hashlib.sha256(declaration.encode()).hexdigest(),
                       "prefix": prefix_binding})


def make_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--block", required=True, type=parse_pc)
    parser.add_argument("--rules", required=True, type=parse_rules)
    parser.add_argument("--stop", required=True, type=parse_stop)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--workspace", type=Path, default=Path.cwd())
    parser.add_argument("--source", type=Path)
    parser.add_argument("--theorem")
    parser.add_argument("--prefix-file", type=Path)
    parser.add_argument("--writer")
    parser.add_argument("--surface-policy", choices=("bounded-kernel-v1", "filtered-chunks-v1"),
                        default="bounded-kernel-v1")
    return parser


def main(argv=None, backend=None):
    parser = make_parser()
    args = parser.parse_args(argv)
    if args.stop["kind"] == "rule" and args.stop["value"] not in {r["name"] for r in args.rules}:
        parser.error("The rule trigger is absent from the selected rule set.")
    if args.out.exists() and (not args.out.is_dir() or any(args.out.iterdir())):
        parser.error("Use an empty output directory for a new capture.")
    backend = backend or importlib.import_module("trace_block_mcp")
    request = {"schema_version": SCHEMA_VERSION, "workspace": str(args.workspace.resolve()),
               "source": str(args.source) if args.source else None,
               "theorem": args.theorem, "prefix_file": str(args.prefix_file) if args.prefix_file else None,
               "block_pc": args.block, "rule_set": args.rules, "stop": args.stop,
               "capture_surface_policy": args.surface_policy,
               **({"writer_id": args.writer} if args.writer is not None else {})}
    try:
        request = resolve_request(request)
        request = backend.prepare_request(request, args.out)
        from trace_block_capture import capture_bundle
        trace = capture_bundle(request, args.out, backend)
    except (ValueError, OSError) as error:
        print("Trace capture failed: " + str(error), file=sys.stderr)
        return 1
    return 0 if trace["completion"]["trace_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
