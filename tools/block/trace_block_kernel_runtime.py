"""Bind the separate bounded-kernel observer before its owned transport starts."""
from __future__ import annotations

import hashlib
import json
import os
import shutil
from pathlib import Path
from trace_block_raw_budget import copy_file, write_bytes

POLICY = "bounded-kernel-v1"


def bounded_kernel(request):
    runtime = request.get("observer_runtime")
    if not isinstance(runtime, dict) or "surface_policy" not in runtime:
        return False
    if runtime["surface_policy"] != POLICY:
        raise ValueError("The observer surface policy is unsupported.")
    return True


def snapshot_command(request, selector="1:"):
    name = "trace_bounded_snapshot" if bounded_kernel(request) else "trace_block_snapshot"
    return (selector + " " if selector else "") + 'ltac2:(' + name + ' "residual").'


def checked_reference(value, *, workspace=None):
    if not isinstance(value, dict) or set(value) != {"path", "sha256", "bytes"}:
        raise ValueError("The kernel runtime reference is invalid.")
    name, digest, size = value["path"], value["sha256"], value["bytes"]
    if not isinstance(name, str) or not Path(name).is_absolute():
        raise ValueError("A kernel source reference must use an absolute path.")
    if (not isinstance(digest, str) or len(digest) != 64
            or any(char not in "0123456789abcdef" for char in digest)
            or type(size) is not int or size < 0):
        raise ValueError("A kernel source reference has an invalid hash or size.")
    path = Path(name).resolve()
    if workspace is not None and not path.is_relative_to(workspace):
        raise ValueError("A kernel runtime source leaves its workspace.")
    if not path.is_file() or path.stat().st_size != size:
        raise ValueError("A kernel runtime artifact has the wrong size.")
    with path.open("rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if actual != digest:
        raise ValueError("A kernel runtime artifact has the wrong hash.")
    return {"path": str(path), "sha256": digest, "bytes": size}


def _relative_reference(path, root):
    return {"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size}


def prepare_kernel_environment(request, evidence_dir):
    if not bounded_kernel(request):
        return {}, None
    workspace = Path(request["workspace"]).resolve()
    evidence_dir = Path(evidence_dir).resolve()
    runtime = request["observer_runtime"]
    reader = checked_reference(runtime["kernel_reader"], workspace=workspace)
    toolchain = checked_reference(runtime["kernel_toolchain"], workspace=workspace)
    value = json.loads(Path(toolchain["path"]).read_text())
    if value.get("schema") != 1 or not isinstance(value.get("artifacts"), list):
        raise ValueError("The kernel toolchain inventory is invalid.")
    artifacts = [checked_reference(row) for row in value["artifacts"]]
    by_path = {row["path"]: row for row in artifacts}
    if len(by_path) != len(artifacts):
        raise ValueError("The kernel toolchain inventory repeats a path.")
    if toolchain["path"] in by_path:
        raise ValueError("The kernel toolchain inventory must not reference itself.")
    required = [runtime["plugin"], runtime["bridge"], runtime["kernel_reader"], request["chunk_writer"]]
    if runtime.get("raw_policy") == "trigger-selected-raw-v2":
        required.append(runtime["raw_budget_writer"])
    for item in required:
        name = str(Path(item["path"]).resolve())
        if name not in by_path or by_path[name]["sha256"] != item["sha256"]:
            raise ValueError("The kernel toolchain omits a requested runtime artifact.")
    for name in ("coqc", "ocamlc", "pet"):
        path = str((Path("/home/cody/islaris/_opam/bin") / name).resolve())
        if path not in by_path:
            raise ValueError("The kernel toolchain omits a pinned runtime executable.")
    directory = evidence_dir / "kernel-runtime"
    directory.mkdir()
    reader_copy = directory / "kernel_reader.exe"
    toolchain_copy = directory / "TOOLCHAIN.json"
    copy_file(reader["path"], reader_copy)
    copy_file(toolchain["path"], toolchain_copy)
    if hashlib.sha256(reader_copy.read_bytes()).hexdigest() != reader["sha256"]:
        raise ValueError("The copied kernel reader hash differs.")
    if hashlib.sha256(toolchain_copy.read_bytes()).hexdigest() != toolchain["sha256"]:
        raise ValueError("The copied kernel toolchain hash differs.")
    if not os.access(reader_copy, os.X_OK):
        raise ValueError("The copied kernel reader is not executable.")
    reader_ref = _relative_reference(reader_copy, evidence_dir)
    toolchain_ref = _relative_reference(toolchain_copy, evidence_dir)
    manifest_path = directory / "MANIFEST.json"
    write_bytes(manifest_path, (json.dumps({"schema": 1, "reader": reader_ref,
                                        "toolchain_ref": toolchain_ref}, indent=2) + "\n").encode(), control=True)
    binding = {"surface_policy": POLICY, "source_reader": reader, "source_toolchain": toolchain,
               "reader": reader_ref, "toolchain_ref": toolchain_ref,
               "manifest": _relative_reference(manifest_path, evidence_dir), "artifacts": artifacts}
    return {"ZESU_TRACE_KERNEL_MANIFEST": str(manifest_path)}, binding


def loaded_kernel_runtime(binding, identity):
    if binding is None:
        return None
    by_path = {row["path"]: row for row in binding["artifacts"]}
    process = Path("/proc") / str(identity["pid"])
    fields = (process / "stat").read_text().rsplit(")", 1)[1].split()
    if int(fields[19]) != identity["start_ticks"]:
        raise ValueError("The kernel observation has a different Pet identity.")
    executable = str((process / "exe").resolve())
    if executable not in by_path:
        raise ValueError("The actual Pet executable has no prelaunch inventory binding.")
    checked_reference(by_path[executable])
    rows = []
    for line in (process / "maps").read_text().splitlines():
        parts = line.split(maxsplit=5)
        if len(parts) != 6 or not parts[5].startswith("/"):
            continue
        path = Path(parts[5]).resolve()
        if str(path) not in by_path:
            if path.suffix == ".cmxs":
                raise ValueError("A loaded Rocq plugin has no prelaunch inventory binding: " + str(path))
            continue
        stat = path.stat()
        major, minor = (int(value, 16) for value in parts[3].split(":"))
        if stat.st_ino != int(parts[4]) or os.major(stat.st_dev) != major or os.minor(stat.st_dev) != minor:
            raise ValueError("A loaded kernel runtime artifact changed its file identity.")
        expected = by_path[str(path)]
        actual = checked_reference(expected)
        rows.append({**actual, "device": stat.st_dev, "inode": stat.st_ino, "maps": line})
    return {"pet": identity, "executable": by_path[executable], "mappings": rows,
            "availability": "observed" if rows else "unavailable"}


STATUS_QUERY = "Ltac2 Eval trace_bounded_status ()."


def status_command(closed):
    return STATUS_QUERY if closed else "Abort. " + STATUS_QUERY


def parse_observer_status(result):
    if not isinstance(result, dict) or result.get("accepted") is not True:
        raise ValueError("The observer status query refused.")
    path = result.get("path")
    digest = result.get("sha256")
    if (not isinstance(path, str) or not Path(path).is_absolute()
            or not isinstance(digest, str) or len(digest) != 64
            or any(char not in "0123456789abcdef" for char in digest)):
        raise ValueError("The observer status reference is invalid.")
    with Path(path).open("rb") as stream:
        payload = stream.read(2 * 1024 * 1024 + 1)
    if len(payload) > 2 * 1024 * 1024 or hashlib.sha256(payload).hexdigest() != digest:
        raise ValueError("The observer status bytes differ from their reference.")
    return parse_observer_status_payload(json.loads(payload))


def parse_observer_status_payload(raw):
    """Validate a response payload that the caller binds to exact evidence bytes."""
    if not isinstance(raw, dict):
        raise ValueError("The observer status payload is invalid.")
    if raw.get("accepted") is not True:
        raise ValueError("The retained observer status query refused.")
    if raw.get("retained_state_hash_unchanged") is not True:
        raise ValueError("The observer status query has no retained state-hash check.")
    check = raw.get("retained_state_check", {})
    if (check.get("method") != "Pet.state_hash" or type(check.get("before")) is not int
            or check.get("before") != check.get("after")):
        raise ValueError("The observer status query changed its public state hash.")
    prefixes = ('- : string =\n"', '- : string = "')
    messages = [(row["message"], prefix) for row in raw.get("feedback", [])
                if isinstance(row, dict) and isinstance(row.get("message"), str)
                for prefix in prefixes if row["message"].startswith(prefix)]
    if len(messages) != 1 or not messages[0][0].endswith('"'):
        raise ValueError("The observer status response is not unique.")
    message, prefix = messages[0]
    status = json.loads(message[len(prefix):-1])
    keys = {"schema", "complete", "diagnostic_errors", "unrecorded_errors", "hand_trials",
            "first_error", "first_unrecorded_error"}
    if isinstance(status, dict) and "raw_budget" in status:
        keys.add("raw_budget")
        budget = status["raw_budget"]
        if (not isinstance(budget, dict) or set(budget) != {"schema", "limit_bytes", "limit_reached", "ledger"}
                or budget["schema"] != 1 or type(budget["limit_bytes"]) is not int
                or not 8192 < budget["limit_bytes"] <= 2000000000
                or type(budget["limit_reached"]) is not bool or budget["ledger"] != "evidence/RAW-BUDGET.json"):
            raise ValueError("The observer raw budget is invalid.")
    if isinstance(status, dict) and "selected_feedback" in status:
        keys.add("selected_feedback")
        logs = status["selected_feedback"]
        if (not isinstance(logs, dict) or set(logs) != {"emitted", "omitted", "complete", "first_error"}
                or any(type(logs[key]) is not int or logs[key] < 0 for key in ("emitted", "omitted"))
                or type(logs["complete"]) is not bool or logs["complete"] != (logs["omitted"] == 0)
                or (logs["first_error"] is not None if logs["omitted"] == 0 else
                    not isinstance(logs["first_error"], str) or not logs["first_error"])):
            raise ValueError("The selected feedback status is invalid.")
    if not isinstance(status, dict) or set(status) != keys or status["schema"] != 1:
        raise ValueError("The observer status schema is invalid.")
    if type(status["complete"]) is not bool:
        raise ValueError("The observer completeness flag is invalid.")
    for name in ("diagnostic_errors", "unrecorded_errors"):
        if type(status[name]) is not int or status[name] < 0:
            raise ValueError("The observer error count is invalid.")
    if status.get("selected_feedback", {}).get("omitted", 0) > status["diagnostic_errors"]:
        raise ValueError("The selected feedback omissions exceed diagnostic errors.")
    hand = status["hand_trials"]
    if (not isinstance(hand, dict) or set(hand) != {"started", "accepted", "refused", "rolled_back"}
            or any(type(value) is not int or value < 0 for value in hand.values())
            or hand["accepted"] + hand["refused"] > hand["started"]
            or hand["rolled_back"] > hand["started"]):
        raise ValueError("The observer hand-trial counts are invalid.")
    if status["complete"] != (status["diagnostic_errors"] == 0 and status["unrecorded_errors"] == 0
                               and not status.get("raw_budget", {}).get("limit_reached", False)
                               and status.get("selected_feedback", {}).get("complete", True)):
        raise ValueError("The observer completeness flag contradicts its error counts.")
    for name, counter, fields in (
            ("first_error", "diagnostic_errors", {"phase", "error"}),
            ("first_unrecorded_error", "unrecorded_errors", {"phase", "capture_error", "logging_error"})):
        value = status[name]
        if status[counter] == 0:
            if value is not None:
                raise ValueError("The observer error detail contradicts its count.")
        elif (not isinstance(value, dict) or set(value) != fields
              or any(not isinstance(item, str) or not item for item in value.values())):
            raise ValueError("The observer error detail is invalid.")
    return status


def observation_complete(binding, loaded, error, unchanged, status, status_error, ownership):
    return bool(binding is not None and isinstance(loaded, dict)
                and loaded.get("availability") == "observed"
                and error is None and unchanged is True and status_error is None
                and isinstance(status, dict) and isinstance(status.get("status"), dict)
                and status["status"].get("complete") is True
                and ownership.get("transport_closed_normally") is True
                and ownership.get("owned_pet_exited") is True)
