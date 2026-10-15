"""Verify a retained session and its transitive raw evidence before sealing."""

import hashlib
import json
from pathlib import Path
import re

from trace_block import logical_session_id
from trace_block_event_identity import read_event_identity


def file_sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def checked_reference(reference):
    if (not isinstance(reference, dict) or not isinstance(reference.get("path"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", str(reference.get("sha256", "")))):
        raise ValueError("A raw evidence reference is malformed.")
    path = Path(reference["path"])
    if file_sha256(path) != reference["sha256"]:
        raise ValueError("A raw evidence reference changed: " + str(path))
    return path


def verify_raw_evidence(raw, trace, request_path, *, expected_session_sha256,
                        expected_request_sha256, allow_historical_no_manifest=False,
                        raw_index_path=None, expected_raw_index_sha256=None,
                        raw_seal_path=None, expected_raw_seal_sha256=None, storage_records=None):
    """Bind the logical session to the accepted start and every raw event."""
    raw = Path(raw).resolve(strict=True)
    request_path = Path(request_path).resolve(strict=True)
    if file_sha256(request_path) != expected_request_sha256:
        raise ValueError("The retained request hash changed.")
    session_path = checked_reference({"path": str(raw / "SESSION.json"),
                                      "sha256": expected_session_sha256})
    request = json.loads(request_path.read_text())
    session = json.loads(session_path.read_text())
    session_id = logical_session_id(request)
    if trace.get("session", {}).get("id") != session_id:
        raise ValueError("The trace session differs from the retained request.")
    expected_request = {key: request[key] for key in
                        ("block_pc", "rule_set", "stop", "scope") if key in request}
    if trace.get("request") != expected_request:
        raise ValueError("The trace request differs from the retained request.")
    operations = session.get("operations")
    if not isinstance(operations, list):
        raise ValueError("The raw session has no operation list.")
    starts = [operation for operation in operations if operation.get("tool") == "rocq_trace_start"]
    if len(starts) != 1:
        raise ValueError("The raw session must bind one actual proof start.")
    start = starts[0]
    expected_start = {"workspace": request.get("workspace"), "file": request.get("source"),
                      "theorem": request.get("theorem")}
    if any(not value for value in expected_start.values()) or start.get("arguments") != expected_start:
        raise ValueError("The raw proof start differs from the retained request.")
    for operation in operations:
        checked_reference(operation)
    start_result = json.loads(Path(start["path"]).read_text()).get("structuredContent", {})
    if (start_result.get("success") is not True
            or start_result.get("file") != request["source"]
            or start_result.get("theorem") != request["theorem"]):
        raise ValueError("The retained proof start was not accepted for this source.")
    if session.get("final_snapshot") is not None:
        checked_reference(session["final_snapshot"])
    if session.get("projection_source_session") is not None:
        checked_reference(session["projection_source_session"])
    manifest_path = raw / "RUN-MANIFEST.json"
    manifest_hash = None
    if not manifest_path.is_file() and not allow_historical_no_manifest:
        raise ValueError("The raw session lacks its run manifest.")
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        if (manifest.get("revisions") != session.get("revisions")
                or manifest.get("prepared_instrumentation") != request.get("instrumentation")):
            raise ValueError("The run manifest differs from the request or session.")
        manifest_hash = file_sha256(manifest_path)
    owner = session.get("ownership", {})
    pet = owner.get("pet", {})
    selected = trace.get("coverage", {}).get("raw_event_index") is not None
    external_index = None
    root_record = None
    storage_record = None
    if selected:
        if raw_index_path is None or raw_seal_path is None:
            raise ValueError("Selected output requires the external raw index and complete raw seal.")
        index_path = checked_reference({"path": str(raw_index_path), "sha256": expected_raw_index_sha256})
        root_seal_path = checked_reference({"path": str(raw_seal_path), "sha256": expected_raw_seal_sha256})
        external_index = json.loads(index_path.read_text())
        if external_index.get("session") != session_id:
            raise ValueError("The raw index has a different logical session.")
        root_record = verify_root_seal(raw, session_id, root_seal_path)
        from trace_block_storage import verify_storage_records
        storage_record = verify_storage_records(Path(root_record["root"]), storage_records)
        events = external_index.get("events")
        old_seal = raw / "EVENT-SEAL.json"
        if old_seal.is_file() and json.loads(old_seal.read_text()).get("streams") != events:
            raise ValueError("The existing raw event seal differs from the complete external index.")
        old_index = raw / "EVENT-INDEX.json"
        if old_index.is_file() and json.loads(old_index.read_text()).get("process") != pet:
            raise ValueError("The existing raw event index has a different Pet identity.")
    else:
        for name in ("EVENT-INDEX.json", "EVENT-SEAL.json"):
            if not (raw / name).is_file():
                raise ValueError("The raw evidence lacks " + name + ".")
        index = json.loads((raw / "EVENT-INDEX.json").read_text())
        if index.get("process") != pet:
            raise ValueError("The event index has a different Pet identity.")
        seal = json.loads((raw / "EVENT-SEAL.json").read_text())
        events = seal.get("streams")
    if not isinstance(events, list):
        raise ValueError("The raw event seal has no stream list.")
    names = set()
    native_entries = []
    filtered = selected and external_index.get("selection_policy") == "source-filtered-v1"
    native_identities = set()
    for event in events:
        name = event.get("path") if isinstance(event, dict) else None
        if not isinstance(name, str) or not re.fullmatch(
                r"events/process-" + str(pet.get("pid")) + r"/event-[0-9]+\.json", name):
            raise ValueError("The event seal contains an invalid owned-event path.")
        if name in names:
            raise ValueError("The event seal contains a duplicate event path.")
        names.add(name)
        checked_reference({**event, "path": str(raw / name)})
        if selected and not filtered:
            identity = read_event_identity(raw / name)
            if identity["kind"] != "native-entry":
                continue
            client, invocation = identity.get("rule"), identity.get("invocation")
            if (not isinstance(client, str) or type(invocation) is not int or invocation < 1
                    or type(identity.get("trial")) is not bool):
                raise ValueError("A raw native entry has invalid identity or trial attribution.")
            if identity["trial"]:
                continue
            descriptor = request.get("entry_descriptors", {}).get(client)
            if not isinstance(descriptor, dict) or not isinstance(descriptor.get("rule"), str):
                raise ValueError("A raw native entry has no client descriptor.")
            if descriptor["rule"] not in request.get("selected_rules",
                    [row["name"] for row in request["rule_set"]]):
                continue
            key = (client, invocation)
            if key in native_identities:
                raise ValueError("The raw native stream contains a duplicate entry identity.")
            native_identities.add(key)
            native_entries.append({"rule": descriptor["rule"], "client": client,
                                   "invocation": invocation,
                                   "event": {"path": name, "sha256": event["sha256"]}})
    actual = {str(path.relative_to(raw)) for path in
              (raw / "events" / ("process-%s" % pet.get("pid"))).glob("event-*.json")}
    if names != actual:
        raise ValueError("The raw owned stream differs from its event seal.")
    filtered_verification = None
    if filtered:
        if not isinstance(request.get("observer_runtime"), dict):
            raise ValueError("A filtered index requires the bound observer runtime.")
        from trace_block_filtered_closure import verify_kernel_closure
        verify_kernel_closure(session, request, evidence_dir=raw)
        if trace.get("completion", {}).get("closure_check") != session.get("closure_check"):
            raise ValueError("The filtered trace has a different closure operation.")
        from trace_block_filtered_seal import verify_filtered_index
        filtered_verification = verify_filtered_index(raw, request, external_index, trace, pet)
        native_entries = filtered_verification["captured_entries"]
    elif selected:
        if request.get("observer_runtime") is not None:
            raise ValueError("A filtered request cannot use the legacy selection policy.")
        native_entries.sort(key=lambda row: row["event"]["path"])
        verify_selected_index(trace, request, external_index, native_entries)
    return {"session": session_id, "request": {"path": str(request_path),
            "sha256": expected_request_sha256}, "raw_session_sha256": expected_session_sha256,
            "accepted_start": {"path": start["path"], "sha256": start["sha256"]},
            "verified_operations": len(operations), "verified_events": len(events),
            "verified_native_entries": native_entries if selected else None,
            "filtered_verification": filtered_verification,
            "run_manifest_sha256": manifest_hash,
            "external_raw_index": None if not selected else
                {"path": str(index_path.resolve()), "sha256": expected_raw_index_sha256},
            "complete_raw_seal": root_record, "storage": storage_record,
            "run_manifest_limit": None if manifest_hash else
                "This historical control has no run manifest. The accepted start and raw request bind its session."}


def verify_root_seal(raw, session_id, path):
    """Verify every file and process stream in the monitor's immutable root."""
    record = json.loads(Path(path).read_text())
    root = Path(record["root"]).resolve(strict=True)
    if raw.resolve() != root / "evidence" or record.get("session_id") != session_id:
        raise ValueError("The complete raw seal has a different root or session.")
    files = record.get("files")
    if not isinstance(files, list):
        raise ValueError("The complete raw seal has no file list.")
    expected = set()
    for reference in files:
        name = reference.get("path") if isinstance(reference, dict) else None
        if (not isinstance(name, str) or not name or Path(name).is_absolute()
                or ".." in Path(name).parts or name in expected):
            raise ValueError("The complete raw seal has an invalid file path.")
        expected.add(name)
        source = checked_reference({**reference, "path": str(root / name)})
        if type(reference.get("bytes")) is not int or reference["bytes"] != source.stat().st_size:
            raise ValueError("A complete raw-seal file has a different size.")
    actual = {str(source.relative_to(root)) for source in root.rglob("*") if source.is_file()}
    if actual != expected:
        raise ValueError("The complete raw file set differs from its seal.")
    return {"path": str(Path(path).resolve()), "sha256": file_sha256(path),
            "root": str(root), "verified_files": len(files)}


def verify_selected_index(trace, request, index, native_entries):
    """Associate every retained trigger with the complete raw classification."""
    attempted = dict.fromkeys(request.get("selected_rules", [row["name"] for row in request["rule_set"]]), 0)
    actual = dict.fromkeys(attempted, 0)
    rows = index.get("attempted_entries")
    if not isinstance(rows, list):
        raise ValueError("The raw index lacks attempted-entry classifications.")
    raw_entries = {row["event"]["path"]: row for row in native_entries}
    row_entries = []
    selected = []
    unknown = False
    identities = set()
    event_rows = index.get("events")
    if (not isinstance(event_rows, list)
            or any(not isinstance(row, dict) or not isinstance(row.get("path"), str)
                   or not isinstance(row.get("sha256"), str) for row in event_rows)):
        raise ValueError("The external raw index has a malformed event list.")
    events = {row["path"]: row["sha256"] for row in event_rows}
    for row in rows:
        if not isinstance(row, dict) or row.get("rule") not in attempted:
            raise ValueError("A raw attempted entry has an unselected rule.")
        rule, client, invocation = row["rule"], row.get("client"), row.get("invocation")
        identity = (client, invocation)
        if (not isinstance(client, str) or type(invocation) is not int
                or identity in identities):
            raise ValueError("A raw attempted entry has an invalid or duplicate identity.")
        identities.add(identity)
        event = row.get("event", {})
        if (not isinstance(event, dict) or event.get("path") not in events
                or events[event["path"]] != event.get("sha256")):
            raise ValueError("A raw classification has no matching event hash.")
        descriptor = request.get("entry_descriptors", {}).get(client)
        if not isinstance(descriptor, dict) or descriptor.get("rule") != rule:
            raise ValueError("A raw classification has a different client descriptor.")
        native = {"rule": rule, "client": client, "invocation": invocation,
                  "event": {"path": event["path"], "sha256": event["sha256"]}}
        if native != raw_entries.get(event["path"]):
            raise ValueError("A raw classification differs from its sealed native entry.")
        row_entries.append(native)
        attempted[rule] += 1
        decision = row.get("classification")
        if decision == "actual-trigger":
            actual[rule] += 1
            selected.append((rule, client, invocation))
        elif decision == "unknown":
            unknown = True
        elif decision != "non-trigger":
            raise ValueError("A raw attempted entry has an unsupported classification.")
    if row_entries != native_entries:
        raise ValueError("The classification rows do not cover the complete raw native-entry set in order.")
    coverage = trace["coverage"]
    if attempted != coverage.get("attempted_entries") or actual != coverage.get("actual_triggers"):
        raise ValueError("Raw attempted and actual counts differ from selected coverage.")
    retained = [(point.get("trigger", {}).get("rule"), point.get("trigger", {}).get("client"),
                 point.get("trigger", {}).get("invocation")) for point in trace["points"]]
    if retained != selected:
        raise ValueError("The retained points differ from the actual raw triggers.")
    if unknown and trace.get("completion", {}).get("trace_complete") is True:
        raise ValueError("Unknown raw trigger classifications cannot establish completeness.")
