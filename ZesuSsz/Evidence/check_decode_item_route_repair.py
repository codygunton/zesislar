"""Check linked native certificates for the route-repair and array-store classes."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
INDEX = ROOT / "ZesuSsz/Evidence/route_repair/INDEX.json"
SITES = ["6960", "697c", "69e8", "6a08", "6a38", "6aa8", "6ad8", "6a24", "6ac4"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bound_file(reference, root=ROOT):
    path = Path(reference["path"])
    if not path.is_absolute():
        path = root / path
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == reference["sha256"],
            "A bound file changed: " + str(path))
    return path.resolve(), data


def declaration(source, name):
    match = re.search(r"\bLemma " + re.escape(name) + r"\b", source)
    require(match is not None, "The exact native theorem is missing: " + name)
    return source[match.start():].split("\nProof.", 1)[0].strip()


def response(call):
    raw = call["raw_response"]
    structured = raw.get("structuredContent")
    if structured is not None:
        return structured
    for item in raw.get("content", []):
        if item.get("type") == "text":
            try:
                return json.loads(item["text"])
            except json.JSONDecodeError:
                pass
    raise ValueError("The raw tool response contains no structured result.")


def closed_groups(data):
    actual_groups(data)
    require(all(data[key] == [] for key in data), "An actual native group remains open.")


def actual_groups(data):
    require(isinstance(data, dict) and set(data) == {"goals", "stack", "shelf", "given_up"},
            "The export does not contain all four actual groups.")
    require(all(type(value) is list for value in data.values()),
            "Each actual group must be an array, including empty groups.")
    require(all(type(frame) is list and len(frame) == 2 and
                all(type(side) is list for side in frame) for frame in data["stack"]),
            "A focus frame must contain two arrays.")


def inventory(index, root=ROOT):
    require([case["block"] for case in index["cases"]] == SITES,
            "The acceptance inventory must contain the exact nine sites.")
    for case in index["cases"]:
        _, statement = bound_file(case["native_statement"], root)
        _, source = bound_file(case["native_source"], root)
        require(declaration(source.decode(), case["native_theorem"]) ==
                statement.decode().strip(), "The captured native statement changed.")
        bound_file(case["capture"], root)
    bound_file(index["checked_module_source"], root)
    bound_file(index["control_module"], root)
    bound_file(index["reviewed_terminal_package"], root)



def bound_json(reference, root=ROOT):
    path, data = bound_file(reference, root)
    return path, json.loads(data)


def same_path(left, right, root=ROOT):
    def absolute(value):
        value = Path(value)
        return (value if value.is_absolute() else root / value).resolve()
    return absolute(left) == absolute(right)


def import_modules(source):
    # Coq comments can contain nested comments and fake Require commands.
    clean, depth, position = [], 0, 0
    while position < len(source):
        pair = source[position:position + 2]
        if pair == "(*":
            depth += 1
            position += 2
        elif pair == "*)" and depth:
            depth -= 1
            position += 2
        else:
            clean.append(" " if depth else source[position])
            position += 1
    require(depth == 0, "A source has an unfinished comment.")
    pattern = r"(?:\bFrom\s+([\w.]+)\s+)?\bRequire\s+(?:(?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s|$)"
    modules = []
    for prefix, names in re.findall(pattern, "".join(clean)):
        modules.extend((prefix + "." if prefix else "") + name for name in names.split())
    return modules


def sessions(bundle, root=ROOT):
    records = bundle.get("sessions")
    require(type(records) is list and records, "Owned session records are required.")
    result = {}
    for record in records:
        identity = record["id"]
        require(type(identity) is str and identity and identity not in result,
                "Session identities must be unique.")
        require(same_path(record["workspace"], root, root) and
                record["verification_root"] == bundle["verification_root"],
                "A session has a different workspace or verification root.")
        _, calls = bound_json(record["raw_calls"], root)
        require(type(calls) is list, "A session transcript must be an array.")
        _, closure = bound_json(record["closure"], root)
        require(closure["session_id"] == identity and closure["owner"] == record["owner"],
                "The closure belongs to a different owned transport.")
        owner = record["owner"]
        require(type(owner) is dict and set(owner) == {"pid", "start_ticks"} and
                all(type(value) is int and value > 0 for value in owner.values()),
                "The controller must identify its owned server PID and start ticks.")
        require(closure.get("transport_closed_normally") is True and
                closure.get("server_exit_verified") is True and
                type(closure.get("cleanup_signals_sent")) is int and
                closure["cleanup_signals_sent"] == 0 and
                type(closure.get("termination_fallback_calls")) is int and
                closure["termination_fallback_calls"] == 0,
                "The owned transport lacks explicit normal closure evidence.")
        pet = closure.get("pet")
        require((pet is None and closure.get("standalone_Pet_absent") is True) or
                (type(pet) is dict and type(pet.get("pid")) is int and pet["pid"] > 0 and
                 type(pet.get("start_ticks")) is int and pet["start_ticks"] > 0 and
                 closure.get("Pet_exit_verified") is True),
                "The owned Pet lacks explicit identity and closure evidence.")
        result[identity] = {"metadata": record, "calls": calls, "used": False}
    return result


def tool_call(session, position, tool):
    require(type(position) is int and 0 <= position < len(session["calls"]),
            "A tool reference is outside its owned transcript.")
    call = session["calls"][position]
    require(call.get("session_id") == session["metadata"]["id"] and
            call.get("controller_owner") == session["metadata"]["owner"],
            "The call has a different controller session or owned server.")
    require(call.get("tool") == tool and response(call).get("success") is True,
            "The referenced tool call did not succeed: " + tool)
    require(type(call.get("request_UTC")) is str and call["request_UTC"] and
            type(call.get("elapsed_seconds")) in (int, float) and call["elapsed_seconds"] >= 0,
            "The controller request timing is missing.")
    if "result" in call:
        require(call["result"] == response(call), "The parsed and raw tool results differ.")
    session["used"] = True
    return call, response(call)


def exported(session, position, state, source, theorem, attribution_reference, root):
    call, result = tool_call(session, position, "rocq_complete_goals")
    require(call["arguments"].get("from_state") == state and result.get("state_id") == state,
            "The export belongs to a different state.")
    _, attribution = bound_json(attribution_reference, root)
    require(attribution == {"method": "controller_complete_export", "session_id": session["metadata"]["id"],
            "call": position, "state_id": state, "workspace": str(root.resolve()), "theorem": theorem,
            "source": {"path": str(source), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()},
            "export": {"path": result["path"], "sha256": result["sha256"]}},
            "The controller export attribution has a different source, theorem, workspace, or state.")
    # The production exporter omits these fields. Never add them to its raw response.
    optional = {"groups_are_actual": True, "truncated": False, "theorem": theorem,
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    require(all(key not in result or result[key] == value for key, value in optional.items()),
            "An optional raw export identity contradicts the linked proof.")
    for key, path in (("source", source), ("workspace", root)):
        if key in result:
            require(same_path(result[key], path, root), "An optional raw export path contradicts the linked proof.")
    _, groups_bytes = bound_file({"path": result["path"], "sha256": result["sha256"]}, root)
    require(result.get("bytes") == len(groups_bytes), "The exported byte count differs.")
    groups = json.loads(groups_bytes)
    actual_groups(groups)
    for counter, key in (("active_goals", "goals"), ("stack_entries", "stack"),
                         ("shelved_goals", "shelf"), ("given_up_goals", "given_up")):
        require(type(result.get(counter)) is int and result[counter] == len(groups[key]),
                "An export counter differs from its actual group.")
    require(result.get("stack_frame_goal_counts") ==
            [{"left": len(frame[0]), "right": len(frame[1])} for frame in groups["stack"]],
            "The export focus counters differ from its actual frames.")
    return result, groups


def proof_trace(record, source, theorem, session_map, root, activation=None):
    trace = record["proof_trace"]
    session = session_map[trace["session_id"]]
    tool_call(session, trace["health_call"], "rocq_health")
    start_call, start = tool_call(session, trace["start_call"], "rocq_start")
    require(start_call["arguments"].get("theorem") == theorem and
            same_path(start_call["arguments"].get("file", ""), source, root) and
            same_path(start_call["arguments"].get("workspace", ""), root, root),
            "The proof started with a different source, theorem, or workspace.")
    state = start["state_id"]
    last = trace["start_call"]
    require(trace["health_call"] < last, "Health must precede the proof start.")
    if activation is not None:
        require(set(trace["activation_calls"]) == set(activation), "The activation checks are incomplete.")
        for command, position in trace["activation_calls"].items():
            call, _ = tool_call(session, position, "rocq_query")
            require(position > last and call["arguments"].get("command") == command and
                    call.get("context_state_id") == state,
                    "An activation query has a different command or controller state context.")
            for key in ("from_state", "state_id", "at_state"):
                if key in call["arguments"]:
                    require(call["arguments"][key] == state, "An activation query uses a different state.")
        last = max(trace["activation_calls"].values())
    snapshots = trace["exports"]
    attributions = trace["export_attributions"]
    steps = trace["steps"]
    require(type(steps) is list and steps and type(snapshots) is list and
            len(snapshots) == len(steps) + 1 and type(attributions) is list and
            len(attributions) == len(snapshots), "Every advancing step needs attributed before and after exports.")
    require(snapshots[0] > last, "The initial export must follow the start and activation checks.")
    _, groups = exported(session, snapshots[0], state, source, theorem, attributions[0], root)
    last = snapshots[0]
    operations = []
    for number, position in enumerate(steps):
        require(last < position < snapshots[number + 1], "The proof trace order changed.")
        call, result = tool_call(session, position, "rocq_check")
        require(call["arguments"].get("from_state") == state and
                result.get("from_state_id") == state and
                type(result.get("commands_run")) is int and result["commands_run"] > 0,
                "An advancing response is not linked to the preceding state.")
        state = result["state_id"]
        require(type(state) is int, "The advancing state identity is missing.")
        operations.append(call["arguments"].get("body", "").strip())
        _, groups = exported(session, snapshots[number + 1], state, source, theorem, attributions[number + 1], root)
        last = snapshots[number + 1]
    if activation is not None:
        require(trace["native_operation_call"] in steps and
                session["calls"][trace["native_operation_call"]]["arguments"].get("body", "").strip()
                in ("zesu_block.", "try zesu_block."),
                "The referenced native operation is not an explicit zesu_block request.")
    closed_groups(groups)
    qed_call, qed = tool_call(session, trace["qed_call"], "rocq_check")
    require(trace["qed_call"] > last and qed_call["arguments"].get("body", "").strip() == "Qed." and
            qed_call["arguments"].get("from_state") == state and qed.get("from_state_id") == state and
            qed.get("proof_finished") is True and qed.get("commands_run") == 1,
            "Qed did not close the exact final exported state.")
    return operations


def certificate(record, source, theorem, expected, session_map, seal_reference, root):
    compile_record = record["compilation"]
    session = session_map[compile_record["session_id"]]
    tool_call(session, compile_record["health_call"], "rocq_health")
    call, _ = tool_call(session, compile_record["call"], "rocq_compile_file")
    require(compile_record["health_call"] < compile_record["call"] and
            same_path(call["arguments"].get("file", ""), source, root) and
            same_path(call["arguments"].get("workspace", ""), root, root),
            "The compilation has a different source or workspace.")
    require(call["arguments"].get("mode", "full") == "full",
            "A certificate requires full compilation, not a declaration-only pass.")
    object_path, _ = bound_file(record["compiled_object"], root)
    require(object_path.suffix == ".vo" and object_path.stem == source.stem,
            "The retained object has a different source stem.")
    _, attribution = bound_json(compile_record["object_attribution"], root)
    require(attribution == {"method": "controller_post_compile_hash", "session_id": compile_record["session_id"],
            "call": compile_record["call"], "workspace": str(root.resolve()),
            "source": record["proof_source"], "object": record["compiled_object"],
            "input_index": seal_reference}, "The controller object attribution differs from the compilation.")
    verify_record = record["verification"]
    session = session_map[verify_record["session_id"]]
    tool_call(session, verify_record["health_call"], "rocq_health")
    call, result = tool_call(session, verify_record["call"], "rocq_verify")
    require(verify_record["health_call"] < verify_record["call"] and
            same_path(call["arguments"].get("workspace", ""), root, root) and
            call["arguments"].get("proof") == source.read_text() and
            call["arguments"].get("problem_name") == theorem and
            declaration(call["arguments"].get("problem_statement", ""), theorem) == expected and
            result.get("assumptions") == [] and
            result.get("verification_method") in ("module_m", "shared_defs"),
            "The exact statement lacks an empty-assumption certificate.")
    return result["verification_method"]


def input_provenance(bundle, proof_sources, root):
    _, seal = bound_json(bundle["input_index"], root)
    require(seal.get("root") == bundle["verification_root"] and
            same_path(seal.get("workspace", ""), root, root), "The input seal has a different root or workspace.")
    inputs = seal.get("inputs")
    require(type(inputs) is dict and inputs, "The complete input closure is required.")
    for path, digest in inputs.items():
        bound_file({"path": path, "sha256": digest}, root)
    def included(reference):
        path, _ = bound_file(reference, root)
        require(inputs.get(str(path.resolve())) == reference["sha256"],
                "A relevant input is absent from the seal: " + str(path))
        return path
    delta = bundle["candidate_delta"]
    require({"base_root", "source_overlays"}.issubset(delta) and
            set(delta).issubset({"base_root", "source_overlays", "frozen_generation"}) and
            type(delta["base_root"]) is str and re.fullmatch(r"[0-9a-f]{40}", delta["base_root"]) and
            type(delta["source_overlays"]) is list and bundle["switch_source"] in delta["source_overlays"],
            "The frozen base and candidate source overlays must be explicit.")
    overlays = {}
    for reference in delta["source_overlays"]:
        path = included(reference)
        require(path not in overlays, "A source overlay appears twice.")
        require(reference.get("kind", "semantic_change") in ("semantic_change", "frozen_generated_input"),
                "A source overlay has an unknown provenance kind.")
        overlays[path] = reference
    generated = [reference for reference in overlays.values()
                 if reference.get("kind") == "frozen_generated_input"]
    if generated:
        generation = delta.get("frozen_generation")
        require(type(generation) is dict and set(generation) == {"manifest", "source_index"},
                "Frozen generated inputs need their original manifest and source index.")
        included(generation["manifest"])
        included(generation["source_index"])

    def source_provenance(path):
        path = path.resolve()
        if path in overlays:
            return  # Candidate bytes are explicit hash-bound overlays, not base bytes.
        try:
            relative = path.relative_to(root.resolve())
        except ValueError:
            return  # External libraries remain covered by the artifact closure.
        try:
            blob = subprocess.check_output(["git", "-C", str(root), "show",
                                            delta["base_root"] + ":" + str(relative)], stderr=subprocess.DEVNULL)
        except subprocess.CalledProcessError as error:
            raise ValueError("A local dependency is neither base-bound nor an explicit overlay: " + str(path)) from error
        require(path.read_bytes() == blob, "A changed source is absent from candidate overlays: " + str(path))

    included(bundle["switch_source"])
    roles = seal["roles"]
    require(set(roles) == {"hooks", "finish", "approved", "hints", "plugins", "mapping", "findlib", "recipe"},
            "The seal lacks required activation, plugin, mapping, or recipe roles.")
    exact = {"hooks": "ZesuSsz/Automation/Hooks.v", "finish": "ZesuSsz/Automation/Finish.v",
             "approved": "ZesuSsz/Automation/Approved.v", "hints": "ZesuSsz/Compliance/DecodeItemHints.v"}
    for role, relative in exact.items():
        path = included(roles[role])
        require(same_path(path, root / relative, root), "An activation role points to a different source.")
        source_provenance(path)
    require(type(roles["plugins"]) is list and roles["plugins"], "Plugin artifact identities are required.")
    for reference in roles["plugins"]:
        included(reference)
    for role in ("mapping", "findlib", "recipe"):
        included(roles[role])
    modules = seal["modules"]
    require(type(modules) is dict and modules, "The loaded module closure is required.")
    queue, seen = [], set()
    for source in proof_sources:
        included({"path": str(source), "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
        queue.extend(import_modules(source.read_text()))
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        require(module in modules, "An imported module is missing from the artifact closure: " + module)
        entry = modules[module]
        source = included(entry["source"])
        source_provenance(source)
        compiled = included(entry["object"])
        require(compiled.suffix == ".vo", "A loaded module lacks a compiled artifact.")
        queue.extend(import_modules(source.read_text()))
    return seen


def native_case(case, record, index, root=ROOT, session_map=None, seal_reference=None):
    source_path, source_bytes = bound_file(record["proof_source"], root)
    source = source_bytes.decode()
    _, expected = bound_file(case["native_statement"], root)
    require(declaration(source, case["native_theorem"]) == expected.decode().strip(),
            "The repair changed the exact native closure statement.")
    _, original_bytes = bound_file(case["native_source"], root)
    marker = "Lemma " + case["native_theorem"]
    switch_line = "Require Import " + index["repair_identity"]["module"] + "."
    require(source.split(marker, 1)[0].replace(switch_line + "\n", "") ==
            original_bytes.decode().split(marker, 1)[0],
            "The repair changed the entry definition or declaration environment.")
    require(set(index["ON_imports"]).issubset(import_modules(source)), "A required ON import is missing.")
    identity = index["repair_identity"]
    commands = ["Check (_ : " + identity["class"] + ").", "Print " + identity["instance"] + "."]
    operations = proof_trace(record, source_path, case["native_theorem"], session_map, root, commands)
    method = certificate(record, source_path, case["native_theorem"], expected.decode().strip(),
                         session_map, seal_reference, root)
    return {"block": case["block"], "actual_groups": [0, 0, 0, 0], "method": method,
            "assumptions": [], "native_requests": operations,
            "object_attribution": "controller_post_compile_hash"}


def acceptance(index, bundle, root=ROOT):
    inventory(index, root)
    require(bundle.get("version") == 2, "The linked version-2 evidence bundle is required.")
    require(bundle["repair_identity"] == {key: index["repair_identity"][key]
            for key in ("module", "class", "instance")}, "The repair switch identity differs.")
    require([row["block"] for row in bundle.get("native_cases", [])] == SITES,
            "Actual native certificates are required for all nine sites.")
    switch_path, switch_bytes = bound_file(bundle["switch_source"], root)
    require(same_path(switch_path, root / (index["repair_identity"]["module"].replace(".", "/") + ".v"), root),
            "The switch source is not the reserved production module.")
    require(index["repair_identity"]["instance"] in switch_bytes.decode() and
            index["repair_identity"]["class"] in switch_bytes.decode(), "The reserved switch identity is missing.")
    require([row["theorem"] for row in bundle["rejections"]] == index["reject_controls"],
            "Both exact S119 control certificates are required.")
    records = bundle["native_cases"] + bundle["rejections"]
    proof_sources = [bound_file(row["proof_source"], root)[0] for row in records]
    modules = input_provenance(bundle, proof_sources, root)
    session_map = sessions(bundle, root)
    results = [native_case(case, record, index, root, session_map, bundle["input_index"])
               for case, record in zip(index["cases"], bundle["native_cases"])]
    _, controls = bound_file(index["control_module"], root)
    for record in bundle["rejections"]:
        source, data = bound_file(record["proof_source"], root)
        theorem = record["theorem"]
        expected = declaration(controls.decode(), theorem)
        require(declaration(data.decode(), theorem) == expected, "An S119 control statement changed.")
        proof_trace(record, source, theorem, session_map, root)
        certificate(record, source, theorem, expected, session_map, bundle["input_index"], root)
    require(all(record["used"] for record in session_map.values()), "An unrelated session was supplied.")
    return results



ARRAY_STORE_INDEX = ROOT / "ZesuSsz/Evidence/array_store/INDEX.json"
ARRAY_STORE_SITES = ["6a40", "6a78", "69b0", "6ae0", "698c", "6b08"]
ARRAY_STORE_CONTROLS = ["S152a", "S152b"]
ARRAY_STORE_IDENTITY = {
    "module": "ZesuSsz.Automation.Switches.ArrayStoreSelection",
    "class": "ZesuStepArrayStoreSelection",
    "instance": "zesu_switch_array_store_selection",
}

def array_store_schema(index):
    require(index.get("version") == 1, "The array-store index version must be one.")
    require([case.get("block") for case in index.get("cases", [])] == ARRAY_STORE_SITES,
                   "The array-store inventory must contain all six exact sites.")
    require([case.get("id") for case in index.get("controls", [])] == ARRAY_STORE_CONTROLS,
                   "Both S152 correct-selection controls are required.")
    identity = index.get("repair_identity")
    require(isinstance(identity, dict), "The switch identity is required.")
    require(identity.get("status") in ("placeholder", "reserved"),
                   "The switch reservation status is invalid.")
    if identity["status"] == "reserved":
        require({key: identity.get(key) for key in ARRAY_STORE_IDENTITY} == ARRAY_STORE_IDENTITY,
                       "The switch differs from the reserved array-store identity.")
    else:
        require(all(identity.get(key) is None for key in ARRAY_STORE_IDENTITY),
                       "A placeholder must not name an accepting switch.")
    return index


def array_store_missing(index):
    array_store_schema(index)
    result = []
    if index["repair_identity"]["status"] == "placeholder":
        result.append("reserved switch identity")
    for case in index["cases"]:
        for key in ("native_theorem", "native_statement", "native_source", "capture",
                    "source_root", "capture_scope", "capture_provenance"):
            if case.get(key) is None:
                result.append(case["block"] + ": " + key)
    for control in index["controls"]:
        if control.get("eligible_as_exact_native_selection_control") is not True:
            result.append(control["id"] + ": exact selection eligibility")
        for key in ("theorem", "source", "statement", "reviewed_certificate"):
            if control.get(key) is None:
                result.append(control["id"] + ": " + key)
    return result


def array_store_capture_inventory(index, root=ROOT):
    array_store_schema(index)
    for key in ("reservation", "reviewed_locator_package", "reviewed_locator_audit"):
        if key in index:
            bound_file(index[key], root)
    for record in index.get("separate_review_reports", []):
        bound_file(record["report"], root)
    for support in index.get("supporting_certificates", []):
        require(support.get("eligible_as_exact_native_selection_control") is False,
                       "Supporting facts must remain non-eligible selection controls.")
        bound_file(support["report"], root)
        for row in support["declarations"]:
            _, source = bound_file(row["source"], root)
            _, statement = bound_file(row["statement"], root)
            require(declaration(source.decode(), row["theorem"]) ==
                           statement.decode().strip(), "A supporting declaration changed.")
    for case in index["cases"]:
        require(all(case.get(key) is not None for key in
                       ("native_statement", "native_source", "capture", "capture_provenance")),
                       "An exact capture identity is missing.")
        _, statement = bound_file(case["native_statement"], root)
        _, source = bound_file(case["native_source"], root)
        require(declaration(source.decode(), case["native_theorem"]) ==
                       statement.decode().strip(), "An exact native statement changed.")
        if "compiled_native_source" in case:
            _, compiled_source = bound_file(case["compiled_native_source"], root)
            require(declaration(compiled_source.decode(), case["native_theorem"]) ==
                           statement.decode().strip(), "The compiled native declaration changed.")
        if "native_evidence" in case:
            bound_file(case["native_evidence"], root)
        bound_file(case["capture"], root)
        bound_file(case["capture_provenance"], root)
        require(case.get("retained_captures"), "The retained capture list is required.")
        for reference in case["retained_captures"]:
            bound_file(reference, root)
        require(isinstance(case["capture_scope"], dict) and case["capture_scope"],
                       "The exact captured scope is required.")
        require(isinstance(case["source_root"], str) and
                       re.fullmatch(r"[0-9a-f]{40}", case["source_root"]),
                       "The exact frozen source root is required.")
        for role in ("approved", "hints"):
            bound_file(case["capture_scope"][role], root)


def array_store_inventory(index, root=ROOT):
    pending = array_store_missing(index)
    require(not pending, "Acceptance dependencies are missing: " + ", ".join(pending))
    array_store_capture_inventory(index, root)
    for control in index["controls"]:
        _, source = bound_file(control["source"], root)
        _, statement = bound_file(control["statement"], root)
        require(declaration(source.decode(), control["theorem"]) ==
                       statement.decode().strip(), "An S152 control statement changed.")
        bound_file(control["reviewed_certificate"], root)


def array_store_acceptance(index, bundle, root=ROOT):
    array_store_inventory(index, root)
    require(bundle.get("version") == 2, "The linked version-two bundle is required.")
    require(bundle.get("repair_identity") == ARRAY_STORE_IDENTITY,
                   "The array-store switch identity differs.")
    cases = bundle.get("native_cases", [])
    controls = bundle.get("rejections", [])
    require([row.get("block") for row in cases] == ARRAY_STORE_SITES,
                   "All six actual native certificates are required.")
    require([row.get("control_id") for row in controls] == ARRAY_STORE_CONTROLS,
                   "Both exact S152 correct-selection certificates are required.")
    switch, switch_bytes = bound_file(bundle["switch_source"], root)
    require(same_path(switch, root / (ARRAY_STORE_IDENTITY["module"].replace(".", "/") + ".v"), root),
                   "The candidate source is not the reserved switch module.")
    require(all(ARRAY_STORE_IDENTITY[key] in switch_bytes.decode() for key in ("class", "instance")),
                   "The candidate lacks its reserved activation identity.")
    sources = [bound_file(row["proof_source"], root)[0] for row in cases + controls]
    input_provenance(bundle, sources, root)
    _, seal = bound_json(bundle["input_index"], root)
    session_map = sessions(bundle, root)
    results = []
    for case, record in zip(index["cases"], cases):
        expected = {key: case[key] for key in
                    ("capture", "native_source", "source_root", "capture_scope", "capture_provenance", "retained_captures")}
        require(record.get("captured_state_provenance") == expected,
                       "A native result belongs to a different captured state or scope.")
        for role in ("approved", "hints"):
            require(seal["roles"][role]["sha256"] == case["capture_scope"][role]["sha256"],
                           "The candidate changed the captured approved scope or hints.")
        results.append(native_case(case, record, index, root, session_map, bundle["input_index"]))
    for control, record in zip(index["controls"], controls):
        require(record.get("reviewed_certificate") == control["reviewed_certificate"],
                       "An S152 rejection control has a different reviewed certificate.")
        require(record.get("theorem") == control["theorem"],
                       "An S152 rejection control names a different theorem.")
        source, data = bound_file(record["proof_source"], root)
        _, statement = bound_file(control["statement"], root)
        expected = statement.decode().strip()
        require(declaration(data.decode(), control["theorem"]) == expected,
                       "An S152 correct-selection declaration changed.")
        proof_trace(record, source, control["theorem"], session_map, root)
        certificate(record, source, control["theorem"], expected,
                           session_map, bundle["input_index"], root)
    require(all(session["used"] for session in session_map.values()),
                   "An unrelated owned session was supplied.")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path,
                        help="The hash-bound actual ON native proof bundle.")
    parser.add_argument("--array-store", action="store_true",
                        help="Check the separate six-site array-store acceptance class.")
    parser.add_argument("--index", type=Path)
    parser.add_argument("--check-schema", action="store_true")
    parser.add_argument("--check-captures", action="store_true")
    parser.add_argument("--check-inventory", action="store_true",
                        help="Check identities only. This does not accept the repair.")
    args = parser.parse_args()
    index_path = args.index or (ARRAY_STORE_INDEX if args.array_store else INDEX)
    index = json.loads(index_path.read_text())
    if args.array_store:
        if args.check_schema:
            print(json.dumps({"schema_checked": True, "accepted": False,
                              "pending": array_store_missing(index)}, indent=2))
            return 0
        if args.check_captures:
            array_store_capture_inventory(index)
            print("Six frozen capture sets checked. Native acceptance did not run.")
            return 0
        if args.check_inventory:
            array_store_inventory(index)
            print("Six capture identities checked. Native acceptance did not run.")
            return 0
        require(args.results is not None, "The six-native linked proof bundle is required.")
        result = array_store_acceptance(index, json.loads(args.results.read_text()))
        print(json.dumps({"accepted": True, "native_cases": result, "S152_rejections": 2}, indent=2))
        return 0
    require(not args.check_schema and not args.check_captures,
            "Schema and capture checks require the array-store class.")
    if args.check_inventory:
        inventory(index)
        print("Nine capture identities checked. Native acceptance did not run.")
        return 0
    require(args.results is not None, "The actual nine-native proof bundle is required.")
    result = acceptance(index, json.loads(args.results.read_text()))
    print(json.dumps({"accepted": True, "native_cases": result, "S119_rejections": 2}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
