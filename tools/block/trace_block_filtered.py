"""Bind switch-independent guards and project lightweight entry counters."""

import hashlib
import json

from trace_block_chunks import MAX_RECORD_BYTES


def _sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def typed_guards():
    """Return exact observation tests without bounds, switches or witnesses."""
    full = "(bv_or (bv_and (bv_add _ (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0))"
    reduced = "(bv_or (bv_and _ (BV 64 18446744073709551614)) (BV 64 0))"
    fault = "bv_extract 0 1 (bv_shiftr " + full + " (BV 64 1)) = BV 1 1"
    expressions = {
        "MemoryAccess.Hooks": "lazymatch goal with | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => constr:(true) | _ => constr:(false) end",
        "MemoryAccess.FindInContext": "lazymatch goal with | |- FindInContext (FindMemMapsTo _) _ => constr:(true) | _ => constr:(false) end",
        "ReturnRoute.normalize": (
            "lazymatch goal with "
            "| |- LiTactic (normalize_instr_addr (bv_unsigned " + full + ")) => constr:(true) "
            "| |- LiTactic (normalize_instr_addr (bv_unsigned " + reduced + ")) => constr:(true) "
            "| _ => constr:(false) end"),
        "ReturnRoute.fault": "lazymatch goal with |- SimplAnd (" + fault + ") False => constr:(true) | _ => constr:(false) end",
        "ReturnRoute.implication": (
            "lazymatch goal with |- SimplImpl ?predicate _ => "
            "lazymatch predicate with " + fault + " => constr:(true) | _ => constr:(false) end "
            "| _ => constr:(false) end"),
        "Hooks.zesu_conjunct_head_if_enabled": (
            "lazymatch goal with | _ : @ZesuEntryIntroApplied _ _ _ _, "
            "_ : ZesuEntryIntroHeads _ |- envs_entails _ _ => constr:(true) "
            "| _ => constr:(false) end"),
    }
    def wrap(client, expression):
        prefix = ("idtac" if client.startswith("MemoryAccess.") else
                  "zesu_expose_environment_alias" if client.startswith("Hooks.") else "unLET")
        return ("(fun () => trace_block_ltac1_guard (fun () => ltac1:(" + prefix
                + ")) ltac1val:(fun _ => " + expression + "))")
    return {client: wrap(client, expression) for client, expression in expressions.items()}



def bind_descriptors(descriptors):
    """Bind every exact guard before a capture can start."""
    guards = typed_guards()
    result = {}
    for client, descriptor in sorted(descriptors.items()):
        if client not in guards:
            raise ValueError("The observer client has no reviewed typed guard: " + client)
        expected = ("MemoryAccess" if client.startswith("MemoryAccess.") else
                    "ConjunctMatch" if client.startswith("Hooks.") else "ReturnRoute")
        if descriptor.get("rule") != expected:
            raise ValueError("The observer client has a different rule binding.")
        guard = {"command": guards[client], "sha256": _sha(guards[client]),
                 "semantics": "switch-independent-discarded"}
        result[client] = dict(descriptor, typed_guard=guard)
    return result


def guard_manifest(descriptors):
    bound = bind_descriptors(descriptors)
    value = {"schema": 2, "clients": {client: row["typed_guard"] for client, row in bound.items()}}
    payload = (json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n").encode()
    if len(payload) > MAX_RECORD_BYTES:
        raise ValueError("The guard manifest exceeds the serialized byte limit.")
    return value, payload


class CounterProjection:
    """Count native guard decisions independently of rule switch assignments.

    Callers supply only native guard records from one sealed process stream.
    Trial records and outcome records require separate indexes.
    """

    def __init__(self, descriptors, process):
        if (not isinstance(process, dict) or set(process) != {"pid", "start_ticks"}
                or any(type(value) is not int or value <= 0 for value in process.values())):
            raise ValueError("The counter process identity is invalid.")
        self.process = dict(process)
        self.seen = set()
        self.trigger_keys = set()
        self.descriptors = bind_descriptors(descriptors)
        rules = sorted({row["rule"] for row in self.descriptors.values()})
        self.attempted = dict.fromkeys(rules, 0)
        self.actual = dict.fromkeys(rules, 0)
        self.unknown = dict.fromkeys(rules, 0)
        self.last_sequence = -1

    def add(self, row):
        if not isinstance(row, dict):
            raise ValueError("A guard counter record is invalid.")
        if row.get("kind") != "guard-counter" or row.get("trial") is not False:
            raise ValueError("The record is not a native guard counter.")
        invocation = row.get("invocation")
        if type(invocation) is not int or invocation <= 0:
            raise ValueError("The counter invocation identity is invalid.")
        key = (row.get("client"), invocation)
        if key in self.seen:
            raise ValueError("The projection repeats a native invocation identity.")
        sequence = row.get("sequence")
        if type(sequence) is not int or sequence <= self.last_sequence:
            raise ValueError("Guard counter records are not in stream order.")
        descriptor = self.descriptors.get(row.get("client"))
        if descriptor is None:
            raise ValueError("A guard counter has an unregistered client.")
        if row.get("rule") != descriptor["rule"]:
            raise ValueError("A guard counter has a different rule binding.")
        classification = row.get("classification")
        if classification not in ("actual-trigger", "non-trigger", "unknown"):
            raise ValueError("A guard counter has an unsupported classification.")
        # A missing guard binding is unknown. It never proves a negative shape.
        if row.get("guard_hash") != descriptor["typed_guard"]["sha256"]:
            classification = "unknown"
        before, after = row.get("fresh_evar_before"), row.get("fresh_evar_after")
        if type(before) is not int or type(after) is not int or min(before, after) < 0:
            raise ValueError("A guard counter lacks exact fresh-evar counters.")
        if before != after:
            raise ValueError("A typed guard changed the fresh-evar counter.")
        self.seen.add(key)
        self.last_sequence = sequence
        rule = descriptor["rule"]
        self.attempted[rule] += 1
        if classification == "actual-trigger":
            self.actual[rule] += 1
            self.trigger_keys.add(key)
        elif classification == "unknown":
            self.unknown[rule] += 1
        return classification

    def coverage(self, captures):
        if not isinstance(captures, list):
            raise ValueError("The projection requires exact capture identities.")
        keys = set()
        captured = dict.fromkeys(self.actual, 0)
        for capture in captures:
            if not isinstance(capture, dict) or set(capture) != {"process", "client", "invocation"}:
                raise ValueError("A capture identity is invalid.")
            if capture["process"] != self.process:
                raise ValueError("A capture belongs to a different process.")
            if type(capture["invocation"]) is not int or capture["invocation"] <= 0:
                raise ValueError("A capture invocation identity is invalid.")
            key = (capture["client"], capture["invocation"])
            if key in keys:
                raise ValueError("The projection repeats a capture identity.")
            if key not in self.trigger_keys:
                raise ValueError("The projection contains an unrecorded trigger capture.")
            keys.add(key)
            captured[self.descriptors[capture["client"]]["rule"]] += 1
        complete = keys == self.trigger_keys and not any(self.unknown.values())
        return {"attempted_entries": dict(self.attempted), "actual_triggers": dict(self.actual),
                "unknown_guards": dict(self.unknown), "entry_events": dict(self.actual),
                "captured_events": captured, "required_complete": complete}
