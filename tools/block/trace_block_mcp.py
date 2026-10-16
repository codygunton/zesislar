#!/usr/bin/env python3
"""Capture proof states through an owned MCP server.

The entry observer must supply internal events separately. Returned MCP states
cannot establish internal coverage. Missing entry evidence makes a run incomplete.
"""

import asyncio
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys


GROUPS = ("goals", "stack", "shelf", "given_up")
PRINTING_DEPTH = 10000

# Only these rules currently have reviewed entry instrumentation descriptors.
RULE_SWITCHES = {"ReturnRoute": "ZesuStepReturnRoute",
                 "ConjunctMatch": "ZesuStepConjunctMatch",
                 "MemoryAccess": "ZesuStepMemoryAccess",
                 "FinishFacts": "ZesuStepFinishFacts"}


RULE_DECLARATIONS = {
    "ReturnRoute": "ZesuSsz.Automation.ReturnRoute.ZesuStepReturnRoute",
    "ConjunctMatch": "ZesuSsz.Automation.ConjunctMatch.ZesuStepConjunctMatch",
    "MemoryAccess": "ZesuSsz.Automation.MemoryAccess.ZesuStepMemoryAccess",
    "FinishFacts": "ZesuSsz.Automation.FinishFacts.ZesuStepFinishFacts",
}


def rule_declaration(name):
    if name not in RULE_DECLARATIONS:
        raise ValueError("The selected switch declaration is unsupported: " + name)
    return RULE_DECLARATIONS[name]


def rule_name_for_switch(switch):
    for name, declaration in RULE_SWITCHES.items():
        if switch == declaration:
            return name
    raise ValueError("The switch has no entry observer: " + switch)



def save_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = (json.dumps(value, sort_keys=True, ensure_ascii=False,
                          separators=(",", ":")) + "\n").encode()
    if path.exists() and path.read_bytes() != payload:
        raise ValueError("The evidence path already contains different bytes: " + str(path))
    path.write_bytes(payload)
    return {"path": str(path.resolve()),
            "sha256": hashlib.sha256(payload).hexdigest()}


def _paired_context(notation, plain):
    if [row["names"] for row in notation] != [row["names"] for row in plain]:
        raise ValueError("The two printers returned different context names.")
    return [{"names": left["names"], "type": left["type"],
             "type_nonotation": right["type"], "body": left["body"],
             "body_nonotation": right["body"]}
            for left, right in zip(notation, plain)]


def stable_capture(capture):
    """Convert both complete printer copies without changing identifiers."""
    notation, plain = capture["notation"], capture["no_notation"]
    def goals(name):
        left, right = notation[name], plain[name]
        if [row["evar"] for row in left] != [row["evar"] for row in right]:
            raise ValueError("The two printers returned different goal identifiers.")
        return [{"id": a["evar"], "goal": a["conclusion"],
                 "goal_nonotation": b["conclusion"],
                 "hyps": _paired_context(a["hyps"], b["hyps"])}
                for a, b in zip(left, right)]
    current = goals("goals")
    left, right = notation["evars"], plain["evars"]
    if [row["evar"] for row in left] != [row["evar"] for row in right]:
        raise ValueError("The two printers returned different Evd identifiers.")
    entries = []
    for a, b in zip(left, right):
        if a["defined"] != b["defined"]:
            raise ValueError("The two printers returned different Evd status.")
        entry = {"id": a["evar"], "name": a["name"],
                 "status": "defined" if a["defined"] else "undefined",
                 "type": a["type"], "type_nonotation": b["type"],
                 "context": _paired_context(a["hyps"], b["hyps"]),
                 "body": a["body"], "body_nonotation": b["body"],
                 "filter": a["filter"]}
        if a["defined"]:
            entry["type_source"] = a["type_source"]
        else:
            entry["candidates"] = a["candidates"]
            entry["candidates_nonotation"] = b["candidates"]
        entries.append(entry)
    return {"goal": current[0]["goal"] if current else None,
            "goal_nonotation": current[0]["goal_nonotation"] if current else None,
            "hyps": current[0]["hyps"] if current else [],
            "current_goals": current, "shelf": goals("shelf"),
            "given_up": goals("given_up"),
            "evars": {"availability": "complete", "entries": entries,
                      "show_existentials": plain["show_existentials"],
                      "metadata_limit": "Entry contexts, types, bodies, status, filters and candidates are retained. Universe constraints, source locations, relevance and abstraction metadata are not serialized."},
            "hidden_focus_frames": notation["hidden_stack"],
            "completeness": {"required_fields_complete": True}}


def convert_entry_events(rows, descriptors, session_id="session-control"):
    """Retain native entries separately from their discarded hand trials.

    Runtime event paths never enter the stable output. Snapshot references use
    logical event identifiers. The evidence seal retains the raw event files.
    """
    points = []
    for offset, row in enumerate(rows):
        if row["kind"] != "native-entry":
            continue
        number = row["invocation"]
        descriptor = descriptors[row["rule"]]
        point = stable_capture(row["capture"])
        point["session_id"] = session_id
        point["trigger"] = {"kind": "rule-entry", "rule": descriptor["rule"],
                            "client": row["rule"], "invocation": number,
                            "branch_status": []}
        point["hint_log"] = {
            "availability": "complete", "filter": descriptor["log_filter"],
            "selection": "Keep Debug messages from this native invocation and messages that contain a listed class or hint name. Keep liShow feedback as a separate discarded hand trial.",
            "events": []}
        point["hand_call"], point["refusal"] = [], []
        pending, messages = {}, []
        for event_index, event in enumerate(rows[offset + 1:], offset + 1):
            kind = event["kind"]
            if kind == "feedback":
                if "invocation" not in event:
                    point["hint_log"]["availability"] = "unavailable"
                    point["completeness"]["required_fields_complete"] = False
                    continue
                if event["invocation"] != number:
                    continue
                message = {"level": event["level"], "message": event["message"]}
                if event.get("trial"):
                    messages.append(message)
                    if event.get("clause") == "liShow":
                        point["hint_log"]["events"].append({**message,
                            "origin": "discarded-hand-trial", "clause": "liShow"})
                elif event["level"] == "debug" or any(
                        text in event["message"] for text in descriptor["log_filter"]):
                    point["hint_log"]["events"].append({**message, "origin": "native-invocation"})
                continue
            if event.get("invocation") != number:
                continue
            if kind == "hand-accepted":
                pending[event["clause"]] = (event_index, event)
            elif kind == "hand-rollback":
                clause = event["clause"]
                accepted = pending.pop(clause, None)
                # A refused tactic has no surviving partial Proofview state.
                # The next hand-refused event records its restored error state.
                record = {"command": descriptor["commands"][clause], "clause": clause,
                          "outcome": "accepted" if accepted else "refused",
                          "rollback_equal": event["exact"],
                          "before": "invocation-%d:entry" % number,
                          "after_trial": "invocation-%d:clause-%s:after" % (number, clause),
                          "rollback": "invocation-%d:clause-%s:rollback" % (number, clause),
                          "feedback": list(messages)}
                if not accepted:
                    record["after_trial_status"] = "Failure restores the entry state before its exception handler. No discarded partial state is inferred."
                messages = []
                point["hand_call"].append(record)
            elif kind == "hand-refused":
                trial = point["hand_call"][-1]
                if trial["clause"] != event["clause"] or trial["outcome"] != "refused":
                    raise ValueError("A refusal has no matching hand trial.")
                trial["message"] = event["refusal"]
                point["refusal"].append({"hand_call_index": len(point["hand_call"]) - 1,
                                          "clause": event["clause"], "message": event["refusal"]})
            elif kind in ("native-local-success", "native-backtracked", "native-exhausted"):
                status = {"kind": kind}
                if "refusal" in event:
                    status["message"] = event["refusal"]
                if "parent_branch_survival" in event:
                    status["parent_branch_survival"] = event["parent_branch_survival"]
                point["trigger"]["branch_status"].append(status)
        for trial in point["hand_call"]:
            def reference(identifier):
                return "#/snapshots/" + identifier.replace("~", "~0").replace("/", "~1")
            trial["commands"] = [{"command": trial["command"],
                                  "before": reference(trial["before"]),
                                  "after": reference(trial["after_trial"]),
                                  "outcome": trial["outcome"],
                                  "refusal": trial.get("message")}]
        points.append(point)
    return points


def groups_iter(value):
    yield value["goals"]
    for left, right in value["stack"]:
        yield left
        yield right
    yield value["shelf"]
    yield value["given_up"]


def check_complete(value):
    """Reject truncated terms. Preserve all context names and definitions."""
    for group in groups_iter(value):
        for goal in group:
            terms = [goal["ty"]]
            for hyp in goal["hyps"]:
                terms.append(hyp["ty"])
                if hyp.get("def") is not None:
                    terms.append(hyp["def"])
            if any("..." in term or "…" in term for term in terms):
                raise ValueError("A proof term contains printer ellipsis.")
            if any(hyp.get("def", "").strip() == "HIDDEN"
                   for hyp in goal["hyps"] if hyp.get("def") is not None):
                raise ValueError("A local definition remains hidden.")


def check_group_identity(before, after):
    left, right = list(groups_iter(before)), list(groups_iter(after))
    if len(left) != len(right):
        raise ValueError("The observation changed the focus stack.")
    for old, new in zip(left, right):
        if len(old) != len(new):
            raise ValueError("The observation changed a goal group.")
        for original, observed in zip(old, new):
            if original.get("info") != observed.get("info"):
                raise ValueError("The observation changed a goal identity.")
            if [h["names"] for h in original["hyps"]] != [
                    h["names"] for h in observed["hyps"]]:
                raise ValueError("The observation changed the ordered context.")


def feedback(state):
    return [{"level": level, "message": message}
            for level, message in (state.feedback or []) if message]


def _snapshot(pet, state, include_proof, allow_outside=False):
    original = pet.complete_goals(state, timeout=None)
    if original is None:
        if allow_outside:
            return {"availability": "outside-proof"}
        raise ValueError("Pet returned no proof scope.")
    original = original.to_json()
    options = ("Set Printing All. Set Printing Notations. "
               "Set Printing Depth 10000. Set Printing Width 1000000.")
    notation_state = pet.run(state, options, timeout=None)
    notation = pet.complete_goals(notation_state, timeout=None).to_json()
    plain_state = pet.run(notation_state,
                          "Unset Printing Notations.", timeout=None)
    plain = pet.complete_goals(plain_state, timeout=None).to_json()
    errors = []
    for value in (notation, plain):
        try:
            check_group_identity(original, value)
            check_complete(value)
        except ValueError as error:
            errors.append(str(error))
    evars = pet.run(plain_state, "Show Existentials.", timeout=None)
    proof = (feedback(pet.run(plain_state, "Show Proof.", timeout=None))
             if include_proof else None)
    retained = pet.complete_goals(state, timeout=None).to_json()
    if retained != original:
        errors.append("The snapshot changed the retained state.")
    for message in feedback(evars) + (proof or []):
        if "..." in message["message"] or "…" in message["message"]:
            errors.append("The evar or proof output contains printer ellipsis.")
    return {"goals": {"notation": notation, "no_notation": plain},
            "evars": {"availability": "complete", "messages": feedback(evars)},
            "show_proof": {"availability": "complete" if include_proof
                           else "not-required", "messages": proof},
            "printing_depth": PRINTING_DEPTH,
            "options": options + " Unset Printing Notations.",
            "option_feedback": feedback(notation_state) + feedback(plain_state),
            "retained_state_unchanged": retained == original,
            "complete": not errors, "errors": errors}


async def _with_pet(function, context):
    """Use the SDK ownership lock without adding an operation deadline.

    The admitted process scope supplies the memory fence. This wrapper neither
    kills Pet nor retries an operation after a transport failure.
    """
    from rocq_mcp import server
    if context is None:
        return {"success": False, "error": "The tool needs an owned MCP context."}
    lifespan = context.lifespan_context

    def execute():
        with server._pet_lock:
            pet = server._ensure_pet(lifespan)
            return function(pet)

    async with server._get_pet_semaphore():
        try:
            return await asyncio.to_thread(execute)
        except Exception as error:
            return {"success": False, "reason": type(error).__name__,
                    "error": str(error), "automatic_restart": False}


def server_main():
    from fastmcp import Context
    from rocq_mcp import server
    from rocq_mcp import interactive
    # FastMCP resolves annotations against module globals.
    globals()["Context"] = Context
    directory = Path(os.environ["ZESU_TRACE_EVIDENCE_DIR"]).resolve()
    counter = 0

    def store(value, bounded=False):
        nonlocal counter
        counter += 1
        if bounded:
            from trace_block_mcp_chunks import store as store_chunks
            return store_chunks(directory, counter, value)
        return save_json(directory / ("capture-%06d.json" % counter), value)

    def resolve(state_id, context):
        entry, base, error = interactive._resolve_check_base_state(state_id)
        if error:
            raise ValueError(str(error))
        stale = interactive._check_staleness(entry, context.lifespan_context)
        if stale:
            raise ValueError(str(stale))
        return entry, base

    @server.mcp.tool
    async def rocq_trace_owner() -> dict:
        pid = os.getpid()
        fields = (Path("/proc") / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
        return {"success": True, "server_pid": pid,
                "server_start_ticks": int(fields[19])}

    @server.mcp.tool
    async def rocq_trace_start(workspace: str, file: str, theorem: str,
                               ctx: Context = None) -> dict:
        def start(pet):
            resolved = server._resolve_file_in_workspace(file, workspace)
            return interactive._build_theorem_start_result(
                pet, file=file, resolved_file=resolved, theorem=theorem,
                workspace=workspace, lifespan_state=ctx.lifespan_context)
        return await _with_pet(start, ctx)

    @server.mcp.tool
    async def rocq_trace_snapshot(from_state: int, include_proof: bool = False,
                                  ctx: Context = None) -> dict:
        def capture(pet):
            entry, _ = resolve(from_state, ctx)
            snapshot = _snapshot(pet, entry.state, include_proof)
            reference = store(snapshot)
            return {"success": snapshot["complete"], "errors": snapshot["errors"],
                    **reference}
        return await _with_pet(capture, ctx)

    @server.mcp.tool
    async def rocq_trace_run(from_state: int, command: str, trial: bool = False,
                            debug: bool = False, capture_mode: str = "legacy", ctx: Context = None) -> dict:
        def execute(pet):
            entry, base = resolve(from_state, ctx)
            forbidden = interactive._check_forbidden_commands(command)
            if forbidden:
                raise ValueError(forbidden)
            if capture_mode not in ("legacy", "bounded"):
                raise ValueError("The MCP capture mode is unsupported.")
            bounded = capture_mode == "bounded"
            if bounded and debug:
                raise ValueError("Bounded capture requires scoped plugin logging.")
            original = (pet.state_hash(entry.state, timeout=None) if bounded else
                        pet.complete_goals(entry.state, timeout=None).to_json())
            state = entry.state
            option_log = []
            if debug:
                state = pet.run(state, "Set Typeclasses Debug. "
                                "Set Typeclasses Debug Verbosity 2.", timeout=None)
                option_log = feedback(state)
            try:
                if bounded:
                    from pytanque import Opts
                    after = pet.run(state, command, opts=Opts(memo=False, hash=True), timeout=None)
                else:
                    after = pet.run(state, command, timeout=None)
                result = {"accepted": True, "message": None,
                          "feedback": feedback(after), "option_feedback": option_log,
                          "after": ({"availability": "metadata-only", "proof_finished": after.proof_finished}
                                    if bounded else _snapshot(pet, after, False, allow_outside=True))}
            except Exception as error:
                result = {"accepted": False, "message": str(error),
                          "error_type": type(error).__name__,
                          "option_feedback": option_log}
                after = None
            retained = (pet.state_hash(entry.state, timeout=None) if bounded else
                        pet.complete_goals(entry.state, timeout=None).to_json())
            key = "retained_state_hash_unchanged" if bounded else "rollback_exact"
            result[key] = retained == original
            if bounded:
                result["retained_state_check"] = {"method": "Pet.state_hash", "before": original,
                                                  "after": retained}
            if not result[key]:
                raise ValueError("The discarded operation changed its source state.")
            evidence = store(result, bounded=bounded)
            if trial or after is None:
                return {"success": True, "accepted": result["accepted"],
                        "state_id": base, **evidence}
            state_id = interactive._state_add(
                state=after, file=entry.file, theorem=entry.theorem,
                workspace=entry.workspace, parent_id=base, tactic=command,
                step=entry.step + 1, file_mtime=entry.file_mtime,
                resolved_file=entry.resolved_file, vo_epoch=entry.vo_epoch)
            return {"success": True, "accepted": True,
                    "state_id": state_id, **evidence}
        return await _with_pet(execute, ctx)

    server.main()


def _identity_alive(identity):
    if identity is None:
        return False
    try:
        fields = (Path("/proc") / str(identity["pid"]) / "stat").read_text().rsplit(")", 1)[1].split()
        return int(fields[19]) == identity["start_ticks"]
    except (FileNotFoundError, ProcessLookupError):
        return False


from trace_block_kernel_runtime import (bounded_kernel, loaded_kernel_runtime,
                                        prepare_kernel_environment, snapshot_command, parse_observer_status, status_command, observation_complete)


def filtered_environment(request):
    """Validate the exact filtered runtime before the MCP server starts."""
    runtime = request.get("observer_runtime")
    if runtime is None:
        return {}
    from trace_block_prepare import guard_manifest_environment
    expected = {"plugin", "bridge", "coqpath"}
    if bounded_kernel(request):
        expected |= {"surface_policy", "kernel_reader", "kernel_toolchain"}
    if not isinstance(runtime, dict) or set(runtime) != expected:
        raise ValueError("The filtered observer runtime binding is invalid.")
    workspace = Path(request["workspace"]).resolve()
    coqpath = Path(runtime["coqpath"]).resolve()
    if not coqpath.is_dir() or not coqpath.is_relative_to(workspace):
        raise ValueError("The filtered bridge search path leaves its workspace.")
    for role in ("plugin", "bridge"):
        reference = runtime[role]
        if not isinstance(reference, dict) or set(reference) != {"path", "sha256"}:
            raise ValueError("The filtered " + role + " binding is invalid.")
        path = Path(reference["path"]).resolve()
        if not path.is_file() or not path.is_relative_to(workspace):
            raise ValueError("The filtered " + role + " leaves its workspace.")
        if hashlib.sha256(path.read_bytes()).hexdigest() != reference["sha256"]:
            raise ValueError("The filtered " + role + " hash differs from its binding.")
    logical = "P0Bounded" if bounded_kernel(request) else "P0Filtered"
    if Path(runtime["bridge"]["path"]).resolve() != (coqpath / logical / "TraceObserver.vo").resolve():
        raise ValueError("The filtered bridge does not match its logical search path.")
    if bounded_kernel(request):
        from trace_block_bounded_prepare import bounded_guard_manifest_environment
        environment = bounded_guard_manifest_environment(workspace, request["entry_descriptors"],
                                                         request.get("guard_manifest"))
    else:
        environment = guard_manifest_environment(workspace, request["entry_descriptors"],
                                                 request.get("guard_manifest"))
    environment["COQPATH"] = str(coqpath)
    return environment


def mapped_observer(request, identity):
    """Bind mapped file identities while the owned Pet remains alive."""
    runtime = request.get("observer_runtime")
    if runtime is None:
        return {"availability": "not-requested"}
    rows = []
    for line in (Path("/proc") / str(identity["pid"]) / "maps").read_text().splitlines():
        fields = line.split(maxsplit=5)
        if len(fields) != 6 or ("bounded_trace_plugin.cmxs" if bounded_kernel(request) else "filtered_trace_plugin.cmxs") not in fields[5]:
            continue
        row = {"maps": line, "path": fields[5], "sha256": None,
               "file_identity_matches_maps": False}
        try:
            path = Path(fields[5]); stat = path.stat()
            major, minor = (int(value, 16) for value in fields[3].split(":"))
            same = (stat.st_ino == int(fields[4]) and os.major(stat.st_dev) == major
                    and os.minor(stat.st_dev) == minor)
            row.update(device=stat.st_dev, inode=stat.st_ino, file_identity_matches_maps=same)
            if same:
                row["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError as error:
            row["unavailable_reason"] = str(error)
        row["matches_requested_plugin"] = row["sha256"] == runtime["plugin"]["sha256"]
        rows.append(row)
    return {"availability": "observed" if rows else "unavailable", "pet": identity,
            "observed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "mappings": rows, "limit": None if rows else
            "The public process maps do not expose the filtered plugin."}


def validated_residual_trials(request):
    trials = request.get("residual_trials", [])
    if not isinstance(trials, list):
        raise ValueError("residual_trials must be a list.")
    if trials and request.get("observer_runtime") is None:
        raise ValueError("Residual trials require the bounded filtered runtime.")
    names = set()
    for row in trials:
        if not isinstance(row, dict) or row.get("rule") != "FinishFacts":
            raise ValueError("The residual trial rule is unsupported.")
        name, command = row.get("name"), row.get("command")
        if not isinstance(name, str) or not name or name in names:
            raise ValueError("Residual trial names must be nonempty and unique.")
        names.add(name)
        if not isinstance(command, str) or not command.strip().endswith("."):
            raise ValueError("A residual trial needs its exact complete command.")
        if hashlib.sha256(command.encode()).hexdigest() != row.get("command_sha256"):
            raise ValueError("The residual trial command hash differs.")
        if row.get("exposure") not in ("exposed", "not-exposed"):
            raise ValueError("The residual trial needs explicit exposure metadata.")
        sources = row.get("sources")
        if not isinstance(sources, list) or not sources:
            raise ValueError("A residual trial needs source bindings.")
        for source in sources:
            path = Path(source["path"])
            if hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
                raise ValueError("The residual trial source hash differs: " + str(path))
    return trials


def selected_residual_identity(evidence_dir, reference, index_path, capture_reader=None):
    if capture_reader is None:
        from trace_block_lazy_capture import LazyCapture
        capture_reader = LazyCapture
    event_path = Path(reference["path"])
    if hashlib.sha256(event_path.read_bytes()).hexdigest() != reference["sha256"]:
        raise ValueError("The residual event hash differs.")
    event = json.loads(event_path.read_text())
    logical = "event-%08d/capture" % event["sequence"]
    with capture_reader(evidence_dir, event["capture"], logical, index_path) as captured:
        notation = captured.root["notation"]["goals"]
        plain = captured.root["no_notation"]["goals"]
        if len(notation) != 1 or len(plain) != 1:
            raise ValueError("The selected residual capture does not contain one focused leaf.")
        goal = notation[0]["evar"]
        if type(goal) is not int or goal <= 0 or plain[0]["evar"] != goal:
            raise ValueError("The residual goal identities differ.")
        return {"command": '1: ltac2:(trace_block_snapshot "residual").',
                "selector": {"kind": "focused-index", "value": 1},
                "selected_goal_id": goal, "event": reference,
                "captured_current_goals": 1,
                "scope": "first-focused-leaf",
                "hidden_peer_goals": {"availability": "unavailable",
                    "reason": "This selected Proofview capture does not expose hidden focus frames."},
                "shelf_count": len(captured.root["notation"]["shelf"]),
                "given_up_count": len(captured.root["notation"]["given_up"])}


async def _run(request, out_dir, *, capture_only=False):
    from trace_block_prepare import writer_identity
    writer = writer_identity(request)
    residual_trials = validated_residual_trials(request)
    if os.environ.get("ZESU_WRITER_ID") != writer:
        raise ValueError("The admitted writer differs from the request owner.")
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client
    workspace = Path(request["workspace"]).resolve()
    source = Path(request["source"]).resolve()
    if not source.is_relative_to(workspace):
        raise ValueError("The stable source must be inside the declared workspace.")
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    out_dir = Path(out_dir).resolve()
    evidence_dir = out_dir / "evidence"
    evidence_dir.mkdir(parents=True, exist_ok=True)
    event_dir = evidence_dir / "events"
    event_dir.mkdir(exist_ok=True)
    if any(event_dir.iterdir()):
        raise ValueError("The native event directory must be empty before startup.")
    env = dict(os.environ)
    findlib_path = Path(request["build_dir"]) / "coqc-ocamlpath.json"
    findlib = json.loads(findlib_path.read_text())
    if Path(findlib["workspace"]).resolve() != workspace:
        raise ValueError("The private findlib record belongs to another workspace.")
    env.update(OCAMLPATH=findlib["OCAMLPATH"], OPAM_SWITCH_PREFIX="/home/cody/islaris/_opam",
               PATH="/home/cody/islaris/_opam/bin:" + env["PATH"])
    env.update(ZESU_TRACE_EVIDENCE_DIR=str(evidence_dir), ROCQ_DUNE_BUILD="0",
               ROCQ_COQC_BINARY=str(Path(__file__).resolve().with_name("trace_block_coqc.sh")),
               ZESU_TRACE_EVENT_DIR=str(event_dir), ROCQ_MAX_PET_RSS_MB="65536")
    required = {"ZESU_DIAGNOSTIC_PROBE": "1", "ZESU_PROOF_CPU_LIMIT": "unlimited",
                "ZESU_PRIMARY_CPU_LIMIT": "none", "ZESU_SCRATCH_WALL_SECONDS": "none",
                "ZESU_SCRATCH_MEMORY_GIB": "64", "ZESU_MODULE_LIMIT_GIB": "64"}
    for name, expected in required.items():
        if env.get(name) != expected:
            raise ValueError("The probe environment requires %s=%s." % (name, expected))
    if resource.getrlimit(resource.RLIMIT_CPU)[0] != resource.RLIM_INFINITY:
        raise ValueError("The admitted probe must have an unlimited CPU limit.")
    control_group = Path("/proc/self/cgroup").read_text()
    cgroup_path = next((line.split(":", 2)[2] for line in control_group.splitlines()
                        if line.startswith("0::")), None)
    if cgroup_path is None:
        raise ValueError("The admitted controller has no cgroup-v2 record.")
    memory_file = Path("/sys/fs/cgroup") / cgroup_path.lstrip("/") / "memory.max"
    memory_limit = memory_file.read_text().strip()
    if memory_limit != str(64 * 1024 ** 3):
        raise ValueError("The MCP controller does not have the declared 64 GiB cgroup fence: " + memory_limit)
    admission = {"writer_id": writer, "cgroup": control_group, "memory_max": memory_limit,
                 "limits": Path("/proc/self/limits").read_text(),
                 "findlib_record_sha256": hashlib.sha256(findlib_path.read_bytes()).hexdigest()}
    env.update(filtered_environment(request))
    kernel_environment, kernel_binding = prepare_kernel_environment(request, evidence_dir)
    env.update(kernel_environment)
    if request.get("observer_runtime") is not None:
        writer_reference = request.get("chunk_writer")
        if not isinstance(writer_reference, dict) or set(writer_reference) != {"path", "sha256"}:
            raise ValueError("The bounded MCP writer binding is unavailable.")
        writer_path = Path(writer_reference["path"]).resolve()
        if not writer_path.is_file() or not writer_path.is_relative_to(workspace):
            raise ValueError("The bounded MCP writer leaves its workspace.")
        if hashlib.sha256(writer_path.read_bytes()).hexdigest() != writer_reference["sha256"]:
            raise ValueError("The bounded MCP writer hash differs from its binding.")
        env["ZESU_TRACE_CHUNK_WRITER"] = str(writer_path)
    artifact = Path(request["build_dir"]) / "install/default/lib/zesu-signature-gates/trace-observer/trace_block_plugin.cmxs"
    revision_paths = [Path(__file__).resolve(), Path(__file__).with_name("trace_block.py"),
                      Path(__file__).with_name("trace_block_prepare.py"),
                      Path(__file__).with_name("trace_block_coqc.sh"),
                      artifact, workspace / "ZesuSsz/Evidence/TraceObserver.v"]
    if request.get("observer_runtime") is not None:
        runtime = request["observer_runtime"]
        revision_paths = [Path(__file__).resolve(), Path(__file__).with_name("trace_block_coqc.sh"),
                          Path(runtime["plugin"]["path"]), Path(runtime["bridge"]["path"]),
                          Path(request["guard_manifest"]["path"])]
        revision_paths += [Path(__file__).with_name(name) for name in (
            "trace_block.py", "trace_block_prepare.py", "trace_block_filtered.py",
            "trace_block_chunks.py", "trace_block_lazy_capture.py", "trace_block_text.py",
            "trace_block_filtered_events.py", "trace_block_mcp_chunks.py",
            "trace_block_package.py")]
        revision_paths.append(Path(request["chunk_writer"]["path"]))
    if kernel_binding is not None:
        revision_paths += [Path(__file__).with_name(name) for name in (
            "trace_block_kernel_runtime.py", "trace_block_bounded_prepare.py",
            "trace_block_bounded_package.py", "trace_block_event_ranges.py")]
        revision_paths += [Path(kernel_binding[key]["path"]) for key in ("source_reader", "source_toolchain")]
        revision_paths += [Path(row["path"]) for row in kernel_binding["artifacts"]]
    revisions = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                 for path in revision_paths}
    for trial in residual_trials:
        for source_reference in trial["sources"]:
            revisions[source_reference["path"]] = source_reference["sha256"]
    used_backend = evidence_dir / "BACKEND-USED.py"
    if used_backend.exists():
        raise ValueError("The native backend snapshot already exists.")
    used_backend.write_bytes(Path(__file__).read_bytes())
    save_json(evidence_dir / "RUN-MANIFEST.json", {"revisions": revisions,
               "prepared_instrumentation": request["instrumentation"], "admission": admission,
               **({"kernel_runtime": kernel_binding} if kernel_binding is not None else {})})
    operations, points = [], []
    residual_trial_records = []
    pet_identity = owner = state_id = None
    transport_closed = False
    error = None
    closure = final = residual_event = final_obligations = residual_selection = None
    actual_switches = []
    kernel_loaded = None
    observer_status = observer_status_error = None
    range_recorder = None
    if kernel_binding is not None:
        from trace_block_event_ranges import EventRanges
        range_recorder = EventRanges(evidence_dir, request["chunk_writer"]["path"],
                                     "/home/cody/islaris/_opam/bin/pet")

    async def call(client, name, arguments):
        started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
        print("MCP-REQUEST", name, started_utc, flush=True)
        index = len(operations)
        before = range_recorder.begin(index) if range_recorder is not None else None
        try:
            response = await client.call_tool(name, arguments)
        except Exception as caught:
            if range_recorder is not None:
                event_range = range_recorder.finish(index, before)
                operations.append({"tool": name, "arguments": arguments,
                    "started_utc": started_utc,
                    "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    "exception": {"type": type(caught).__name__, "message": str(caught)},
                    "event_range": event_range})
            raise
        if range_recorder is not None:
            range_recorder.adopt_owner(response.model_dump(mode="json"))
            event_range = range_recorder.finish(index, before)
        ref = save_json(evidence_dir / ("operation-%06d.json" % index),
                        response.model_dump(mode="json"))
        operations.append({"tool": name, "arguments": arguments,
                           "started_utc": started_utc,
                           "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), **ref,
                           **({"event_range": event_range} if range_recorder is not None else {})})
        result = response.structuredContent
        if kernel_binding is not None and response.isError:
            raise RuntimeError("%s returned an SDK error envelope." % name)
        if not isinstance(result, dict) or not result.get("success", result.get("ok", False)):
            raise RuntimeError("%s rejected: %s" % (name, result))
        return result

    async def snapshot(client, event, proof=False):
        ref = await call(client, "rocq_trace_snapshot",
                         {"from_state": state_id, "include_proof": proof})
        value = json.loads(Path(ref["path"]).read_text())
        point = {"event": event, "capture": value, "evidence": ref}
        points.append(point)
        return point

    async def operation(client, command, trial=False, debug=False):
        return await call(client, "rocq_trace_run", {
            "from_state": state_id, "command": command,
            "trial": trial, "debug": debug,
            "capture_mode": "bounded" if request.get("observer_runtime") is not None else "legacy"})

    try:
        params = StdioServerParameters(command=sys.executable,
                                      args=[str(Path(__file__).resolve()), "--server"],
                                      env=env, cwd=str(workspace))
        async with stdio_client(params) as streams:
            async with ClientSession(*streams) as client:
                try:
                    await client.initialize()
                    await call(client, "rocq_health", {})
                    owner = await call(client, "rocq_trace_owner", {})
                    started = await call(client, "rocq_trace_start", {
                        "workspace": str(workspace), "file": str(source),
                        "theorem": request["theorem"]})
                    state_id = started["state_id"]
                    health = await call(client, "rocq_health", {})
                    pid = health["pet"]["pid"]
                    fields = (Path("/proc") / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
                    if int(fields[1]) != owner["server_pid"]:
                        raise ValueError("Pet does not belong to the owned server.")
                    pet_identity = {"pid": pid, "start_ticks": int(fields[19])}
                    save_json(evidence_dir / "LOADED-OBSERVER.json", mapped_observer(request, pet_identity))
                    if kernel_binding is not None:
                        kernel_loaded = loaded_kernel_runtime(kernel_binding, pet_identity)
                        save_json(evidence_dir / "LOADED-KERNEL-RUNTIME.json", kernel_loaded)
                    all_mode = "Unset Printing All. " if request.get("observer_runtime") is not None else "Set Printing All. "
                    options = all_mode + "Set Printing Notations. Set Printing Depth 10000. Set Printing Width 1000000. "
                    if request.get("observer_runtime") is None:
                        options += "Set Typeclasses Debug. Set Typeclasses Debug Verbosity 2. "
                    printing = await operation(client, options + "Print Options.")
                    if not printing["accepted"]:
                        raise ValueError("The complete printer options were rejected.")
                    state_id = printing["state_id"]
                    for assignment in request["rule_set"]:
                        name = assignment["name"]
                        declaration = rule_declaration(name)
                        known = await operation(client,
                            'let switch := constr:(' + declaration + ') in idtac "P0-SWITCH-TYPE" switch.', trial=True)
                        if not known["accepted"]:
                            raise ValueError("The selected switch declaration is unavailable: " + declaration)
                        resolved = await operation(client,
                            'let evidence := constr:(_ : ' + declaration + ') in idtac "P0-ACTUAL-INSTANCE" evidence.', trial=True)
                        printed = await operation(client, "Print Instances " + declaration + ".", trial=True)
                        raw_resolution = json.loads(Path(resolved["path"]).read_text())
                        raw_instances = json.loads(Path(printed["path"]).read_text())
                        actual_switches.append({"class": declaration, "enabled": resolved["accepted"],
                            "selected_evidence": raw_resolution.get("feedback", []),
                            "instances": raw_instances.get("feedback", [])})
                        if resolved["accepted"] != assignment["enabled"]:
                            raise ValueError("The actual switch activation differs from the request: " + name)
                    for command in request["prefix_commands"]:
                        result = await operation(client, command)
                        if not result["accepted"]:
                            raise RuntimeError("The retained prefix refused: " + command)
                        state_id = result["state_id"]
                    # The unchanged block driver includes the real finisher.
                    # Internal observers capture entries inside this operation.
                    if request.get("observer_runtime") is None:
                        await snapshot(client, {"kind": "initial"})
                    result = await operation(client, request["native_command"],
                                             debug=request.get("observer_runtime") is None)
                    if result["accepted"]:
                        state_id = result["state_id"]
                    else:
                        error = {"type": "native-command-refusal", "evidence": result}
                    if request.get("observer_runtime") is not None:
                        # A failed Qed leaves its persistent source state available.
                        qed = await operation(client, "Qed.")
                        if qed["accepted"]:
                            qed_reference = {key: operations[-1][key] for key in ("path", "sha256")}
                            closure = {"command": "Qed.", "accepted": True,
                                       "unresolved_evars": False, "operation": qed_reference}
                            final_obligations = {"availability": "complete",
                                "counts": {"goals": 0, "stack": 0, "shelf": 0, "given_up": 0},
                                "undefined_evars": 0, "evidence": qed_reference,
                                "method": "kernel-accepted-Qed"}
                            state_id = qed["state_id"]
                        else:
                            checkpoint = await operation(client,
                                snapshot_command(request))
                            if not checkpoint["accepted"]:
                                raise ValueError("The bounded residual checkpoint refused.")
                            state_id = checkpoint["state_id"]
                            matches = []
                            for path in sorted((event_dir / ("process-%d" % pet_identity["pid"])).glob("event-*.json")):
                                row = json.loads(path.read_text())
                                if row.get("kind") == "checkpoint" and row.get("rule") == "residual":
                                    matches.append({"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
                            if len(matches) != 1:
                                raise ValueError("The first bounded residual event is not unique.")
                            residual_event = matches[0]
                            residual_selection = selected_residual_identity(evidence_dir, residual_event,
                                out_dir.parent / "residual-selection.sqlite")
                            if kernel_binding is not None:
                                residual_selection["command"] = snapshot_command(request)
                    else:
                        final = await snapshot(client, {"kind": "residual"}, proof=True)
                        active = final["capture"]["goals"]["notation"]
                        closure = None
                        if not any(list(group) for group in groups_iter(active)):
                            qed = await operation(client, "Qed.")
                            if qed["accepted"]:
                                closure = {"command": "Qed.", "accepted": True,
                                           "unresolved_evars": False}
                                state_id = qed["state_id"]
                            else:
                                error = {"type": "Qed-refusal", "evidence": qed}
                        if closure is None:
                            checkpoint = await operation(client,
                                'ltac2:(trace_block_snapshot "residual").')
                            if checkpoint["accepted"]:
                                state_id = checkpoint["state_id"]
                            else:
                                error = {"type": "residual-evar-capture-refusal", "evidence": checkpoint}
                    if closure is None:
                        process_events = event_dir / ("process-%d" % pet_identity["pid"])
                        def event_paths():
                            return set(process_events.glob("event-*.json"))
                        def new_full_captures(previous):
                            references = []
                            for path in sorted(event_paths() - previous):
                                row = json.loads(path.read_text())
                                if row.get("kind") == "checkpoint" and row.get("rule") == "residual":
                                    if row.get("capture", {}).get("encoding") != "json-chunks-v1":
                                        raise ValueError("The residual trial checkpoint has no full chunked capture.")
                                    references.append({"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
                            return references
                        full_checkpoint = snapshot_command(request, "all:")
                        for index, trial in enumerate(residual_trials):
                            before_events = event_paths()
                            before = await operation(client, full_checkpoint)
                            if not before["accepted"]:
                                raise ValueError("A residual before checkpoint refused.")
                            before_references = new_full_captures(before_events)
                            if not before_references:
                                raise ValueError("The residual trial has no full before checkpoint.")
                            state_id = before["state_id"]
                            before_state = state_id
                            trial_events = event_paths()
                            command = trial["command"] + " " + full_checkpoint
                            result = await operation(client, command, trial=True)
                            after_references = new_full_captures(trial_events)
                            response = json.loads(Path(result["path"]).read_text())
                            if response.get("retained_state_hash_unchanged") is not True:
                                raise ValueError("A residual trial lacks retained public-state hash equality.")
                            rollback_events = event_paths()
                            rollback = await operation(client, full_checkpoint)
                            if not rollback["accepted"]:
                                raise ValueError("A residual rollback checkpoint refused.")
                            rollback_references = new_full_captures(rollback_events)
                            if not rollback_references:
                                raise ValueError("The residual trial has no full rollback checkpoint.")
                            state_id = rollback["state_id"]
                            residual_trial_records.append({"name": trial["name"], "rule": trial["rule"],
                                "command": trial["command"], "executed_command": command,
                                "command_sha256": trial["command_sha256"], "sources": trial["sources"],
                                "execution": "SDK-discarded", "native_entry": False,
                                "refusal_exposure": trial["exposure"], "before_state_id": before_state,
                                "before": before_references, "result": result,
                                "after": after_references if result["accepted"] else [],
                                "after_availability": "captured" if result["accepted"] and after_references else "not-retained",
                                "rollback": rollback_references,
                                "snapshot_join": "New full residual events emitted during each exact operation.",
                                "state_check": response.get("retained_state_check"),
                                "limit": "Plugin checkpoint trial fields remain literal. The enclosing SDK trial establishes discarded provenance."})
                        await operation(client, "Abort.")
                except Exception as caught:
                    error = {"type": type(caught).__name__, "message": str(caught)}
                finally:
                    if kernel_binding is not None and state_id is not None:
                        try:
                            status_result = await operation(client, status_command(closure is not None), trial=True)
                            status_value = parse_observer_status(status_result)
                            observer_status = {"status": status_value,
                                "operation": {key: operations[-1][key] for key in ("path", "sha256")}}
                        except Exception as caught:
                            observer_status_error = {"type": type(caught).__name__, "message": str(caught)}
                    try:
                        await call(client, "rocq_health", {})
                    except Exception as caught:
                        if error is None:
                            error = {"type": type(caught).__name__, "message": str(caught)}
        transport_closed = True
    except Exception as caught:
        error = {"type": type(caught).__name__, "message": str(caught)}
    for _ in range(30):
        if not _identity_alive(pet_identity):
            break
        await asyncio.sleep(0.1)
    unchanged = hashlib.sha256(source.read_bytes()).hexdigest() == source_hash
    changed_revisions = [name for name, digest in revisions.items()
                         if not Path(name).is_file() or hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest]
    unchanged = unchanged and not changed_revisions
    ownership = {"writer_id": writer, "server": owner, "pet": pet_identity,
                 "transport_closed_normally": transport_closed,
                 "owned_pet_exited": (not _identity_alive(pet_identity)) if pet_identity else None,
                 "controller_signals_sent": 0}
    operation_ranges = range_recorder.finalize() if range_recorder is not None else None
    observation_ok = observation_complete(kernel_binding, kernel_loaded, error,
        unchanged, observer_status, observer_status_error, ownership) and bool(
            operation_ranges and operation_ranges["complete"])
    runtime = save_json(evidence_dir / "SESSION.json", {
        "operations": operations, "ownership": ownership, "admission": admission,
        "source_unchanged": unchanged, "changed_revisions": changed_revisions,
        "revisions": revisions, "error": error, "actual_switches": actual_switches,
        "closure_check": closure, "final_snapshot": final["evidence"] if final else None,
        "residual_event": residual_event, "residual_selection": residual_selection,
        "residual_trials": residual_trial_records,
        "final_obligations": final_obligations,
        "final_state_id": state_id,
        "completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        **({"kernel_runtime": kernel_binding, "loaded_kernel_runtime": kernel_loaded,
             "observer_status": observer_status, "observer_status_error": observer_status_error,
             "operation_ranges": operation_ranges, "observation_complete": observation_ok}
           if kernel_binding is not None else {})})
    if capture_only:
        request_path = evidence_dir / "REQUEST.json"
        return {"schema_version": 1, "projection": "not-run",
                "request": {"path": str(request_path), "sha256": hashlib.sha256(request_path.read_bytes()).hexdigest()},
                "session": runtime, "owned_closure": ownership,
                "source_unchanged": unchanged, "error": error,
                **({"observation_complete": observation_ok}
                   if kernel_binding is not None else {})}
    if kernel_binding is not None:
        raise ValueError("The bounded-kernel capture requires its separate lazy projection.")
    return project_session(request, evidence_dir)


def project_session(request, evidence_dir):
    """Project preserved captures without starting or replaying a proof."""
    evidence_dir = Path(evidence_dir)
    session_path = evidence_dir / "SESSION.json"
    session = json.loads(session_path.read_text())
    ownership = session["ownership"]
    pet_identity = ownership["pet"]
    event_dir = evidence_dir / "events"
    artifact = Path(request["build_dir"]) / "install/default/lib/zesu-signature-gates/trace-observer/trace_block_plugin.cmxs"
    revisions, error = session["revisions"], session["error"]
    unchanged = session["source_unchanged"]
    transport_closed = ownership["transport_closed_normally"]
    actual_switches, closure = session["actual_switches"], session["closure_check"]
    final = None
    if session["final_snapshot"] is not None:
        reference = session["final_snapshot"]
        snapshot_file = Path(reference["path"])
        if hashlib.sha256(snapshot_file.read_bytes()).hexdigest() != reference["sha256"]:
            raise ValueError("The retained final snapshot hash changed.")
        final = {"capture": json.loads(snapshot_file.read_text())}
    runtime = {"path": str(session_path), "sha256": hashlib.sha256(session_path.read_bytes()).hexdigest()}
    rows = []
    if pet_identity is not None:
        process_events = event_dir / ("process-%d" % pet_identity["pid"])
        rows = [json.loads(path.read_text()) for path in sorted(process_events.glob("event-*.json"))]
    save_json(evidence_dir / "EVENT-SEAL.json", {
        "streams": [{"path": str(path.relative_to(evidence_dir)),
                     "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                    for path in sorted(event_dir.rglob("event-*.json"))]})
    event_index = {}
    for index, row in enumerate(rows):
        if row["kind"] == "native-entry":
            event_index["invocation-%d:entry" % row["invocation"]] = index
        elif row["kind"] in ("hand-accepted", "hand-rollback"):
            suffix = "after" if row["kind"] == "hand-accepted" else "rollback"
            key = "invocation-%d:clause-%s:" % (row["invocation"], row["clause"])
            event_index[key + suffix] = index
            if suffix == "rollback":
                event_index.setdefault(key + "after", index)
    save_json(evidence_dir / "EVENT-INDEX.json", {
        "process": pet_identity, "snapshot_ids": event_index,
        "ordering": "Zero-based indices in the owned Pet stream, sorted by event filename."})
    descriptors = request["entry_descriptors"]
    from trace_block import logical_session_id
    session_id = logical_session_id(request)
    native_points = convert_entry_events(rows, descriptors, session_id)
    snapshots = {name: stable_capture(rows[index]["capture"])
                 for name, index in event_index.items()}
    missing_checkpoint_attribution = any(row["kind"] == "checkpoint" and "trial" not in row
        and row["rule"] in ("residual", "instruction-lookup", "requested-trigger") for row in rows)
    checkpoints = [row for row in rows if row["kind"] == "checkpoint"
                   and row["rule"] == "residual" and row.get("trial") is False]
    visits = [{"kind": "instruction-lookup", **stable_capture(row["capture"])}
              for row in rows if row["kind"] == "checkpoint"
              and row["rule"] == "instruction-lookup" and row.get("trial") is False]
    residual = None
    if checkpoints:
        residual = stable_capture(checkpoints[-1]["capture"])
        # This export and the inline checkpoint observe the same retained state.
        # The public MCP export supplies all current outer groups, not hidden
        # lexical frames from an earlier entry.
        outer = final["capture"]["goals"]
        def outer_goals(group):
            a, b = outer["notation"][group], outer["no_notation"][group]
            if len(a) != len(b):
                raise ValueError("The outer printer copies have different groups.")
            return [{"goal": left["ty"], "goal_nonotation": right["ty"],
                     "hyps": [{"names": x["names"], "type": x["ty"],
                               "type_nonotation": y["ty"], "body": x.get("def"),
                               "body_nonotation": y.get("def")}
                              for x, y in zip(left["hyps"], right["hyps"])]}
                    for left, right in zip(a, b)]
        residual["current_goals"] = outer_goals("goals")
        if residual["current_goals"]:
            residual.update({key: residual["current_goals"][0][key]
                             for key in ("goal", "goal_nonotation", "hyps")})
        residual.update(session_id=session_id, trigger={"kind": "residual"}, hand_call=[], refusal=[],
                        hint_log={"availability": "complete", "filter": ["residual liShow and Show Proof"],
                                  "events": []},
                        show_proof={"availability": "complete",
                            "text": "\n".join(message["message"] for message in
                                             final["capture"]["show_proof"]["messages"])})
    if residual is not None:
        snapshots["residual"] = {key: residual[key] for key in stable_capture(checkpoints[-1]["capture"])}
    positions = [index for index, row in enumerate(rows) if row["kind"] == "native-entry"]
    ordered = list(zip(positions, native_points))
    marked = 0
    for index, row in enumerate(rows):
        if row["kind"] != "checkpoint" or row["rule"] != "requested-trigger" or row.get("trial") is not False:
            continue
        marked += 1
        point = stable_capture(row["capture"])
        point.update(session_id=session_id,
                     trigger={"kind": request["stop"]["kind"], "rule": None,
                              "matches_stop": True, "entry": "Hooks.zesu_liAStep", "branch": "typed checkpoint"},
                     hint_log={"availability": "complete", "filter": ["typed requested-trigger checkpoint"], "events": []},
                     hand_call=[], refusal=[])
        ordered.append((index, point))
        snapshots["requested-trigger-%d" % marked] = stable_capture(row["capture"])
    native_points = [point for _, point in sorted(ordered, key=lambda item: item[0])]
    for index, point in enumerate(native_points):
        point["trigger"]["ordinal"] = index
    final_obligations = {"availability": "unavailable", "session": session_id,
                         "counts": None, "undefined_evars": None,
                         "evidence": "evidence/SESSION.json#/final_snapshot"}
    if final is not None and final["capture"].get("complete") is True:
        groups = final["capture"]["goals"]["no_notation"]
        final_obligations["counts"] = {
            "goals": len(groups["goals"]),
            "stack": sum(len(left) + len(right) for left, right in groups["stack"]),
            "shelf": len(groups["shelf"]), "given_up": len(groups["given_up"])}
        if checkpoints:
            final_obligations["undefined_evars"] = sum(
                not entry["defined"] for entry in checkpoints[-1]["capture"]["no_notation"]["evars"])
        elif closure is not None and final["capture"]["evars"] == {
                "availability": "complete", "messages": []}:
            final_obligations["undefined_evars"] = 0
        if final_obligations["undefined_evars"] is not None:
            final_obligations["availability"] = "complete"
    counts = {name: sum(point["trigger"]["rule"] == name for point in native_points)
              for name in request["selected_rules"]}
    if request["stop"]["kind"] == "residual":
        occurred = residual is not None
    elif request["stop"]["kind"] == "rule":
        occurred = counts.get(request["stop"]["value"], 0) > 0
    else:
        occurred = (any(row["kind"] == "checkpoint" and row["rule"] == "requested-trigger"
                         and row.get("trial") is False for row in rows)
                    or any(trial["clause"] == "requested-trigger" and trial["outcome"] == "accepted"
                           for point in native_points for trial in point["hand_call"]))
    reasons = []
    if missing_checkpoint_attribution:
        reasons.append("An observed checkpoint lacks explicit native/trial attribution.")
    if error is not None:
        reasons.append("The owned session failed. See the complete runtime evidence.")
    if not unchanged:
        reasons.append("The stable source changed during the session.")
    if not transport_closed or ownership["owned_pet_exited"] is not True:
        reasons.append("The owned session did not close normally.")
    if not request.get("instrumentation", {}).get("entry_coverage_complete"):
        reasons.append("The preparation did not establish complete entry instrumentation.")
    if not request.get("instrumentation", {}).get("instruction_coverage_complete"):
        reasons.append("The preparation did not establish complete instruction lookup instrumentation.")
    if closure is None and residual is None:
        reasons.append("The complete residual capture is unavailable.")
    return {"identity": {**request["scope"], "switches": {"requested": request["rule_set"], "actual_instances": actual_switches},
                         "instrumentation": request["instrumentation"]},
            "session": {"id": session_id, "runtime": "evidence/SESSION.json#/ownership/pet"},
            "pet_start_tick": "evidence/SESSION.json#/ownership/pet/start_ticks",
            "snapshots": snapshots,
            "verdict": {"status": "actual-success" if closure else "unresolved",
                        "kind": "proof_closure" if closure else None,
                        "session": session_id,
                        "evidence": "#/completion/closure_check" if closure else None,
                        "scope": "whole-proof" if closure else "session",
                        "reason": "The kernel accepted Qed." if closure else
                                  "The trace establishes no terminal success or unsatisfiability certificate."},
            "points": native_points, "residual": residual,
            "coverage": {"required_complete": not reasons, "entry_events": counts,
                         "captured_events": counts, "missing_event_ids": [],
                         "unobserved_regions": [] if not reasons else reasons,
                         "requested_trigger": "occurred" if occurred else "not-occurred",
                         "requested_trigger_instruction_list": visits,
                         "traversal": "proof-closed" if closure else "first-residual"},
            "instruction_visits": visits,
            "completion": {"trace_complete": not reasons, "proof_closed": closure is not None,
                           "reasons": reasons, "closure_check": closure,
                           "final_obligations": final_obligations},
            "evidence": runtime, "owned_closure": ownership}


def prepare_request(request, out_dir):
    """Prepare an isolated source scope before the admitted MCP traversal."""
    from trace_block_prepare import prepare_request as prepare, writer_identity
    request = dict(request, writer_id=writer_identity(request))
    selected = [row["name"] for row in request["rule_set"]
                if row["name"] in RULE_SWITCHES]
    unsupported = [row["name"] for row in request["rule_set"]
                   if row["name"] not in RULE_SWITCHES]
    if unsupported:
        raise ValueError("The selected rules have no entry observer: " + ", ".join(unsupported))
    if not selected:
        raise ValueError("The request selects no supported entry observer.")
    result = prepare(request, out_dir)
    result["selected_rules"] = selected
    for field in ("entry_descriptors", "native_command", "instrumentation", "build_dir"):
        if field not in result:
            raise ValueError("The prepared request lacks " + field + ".")
    result["instrumentation"]["backend_sha256"] = hashlib.sha256(
        Path(__file__).read_bytes()).hexdigest()
    for name in ("trace_block.py", "trace_block_prepare.py"):
        result["instrumentation"][name + "_sha256"] = hashlib.sha256(
            Path(__file__).with_name(name).read_bytes()).hexdigest()
    return result


def _admit(request, out_dir, *, capture_only=False):
    """Admit a separate MCP controller through the existing probe guard.

    Compiler admission in the caller never substitutes for this admission.
    The caller's exit watcher covers this child and its final return status.
    """
    from trace_block_prepare import writer_identity
    writer = writer_identity(request)
    request = dict(request, writer_id=writer)
    workspace = Path(request["workspace"]).resolve()
    directory = Path(out_dir).resolve() / "evidence"
    directory.mkdir(parents=True, exist_ok=True)
    request_file = directory / "REQUEST.json"
    result_file = directory / ("CAPTURE.json" if capture_only else "BACKEND.json")
    save_json(request_file, request)
    python = (sys.executable if importlib.util.find_spec("mcp") is not None
              else os.environ.get("ZESU_MCP_PYTHON"))
    if not python or not Path(python).is_file():
        raise ValueError("Set ZESU_MCP_PYTHON to the pinned MCP Python.")
    environment = dict(os.environ)
    environment.pop("ZESU_IN_GATE", None)
    environment.update(ZESU_DIAGNOSTIC_PROBE="1", ZESU_PROBE_ISSUE="10",
                       ZESU_PROOF_CPU_LIMIT="unlimited", ZESU_PRIMARY_CPU_LIMIT="none",
                       ZESU_SCRATCH_WALL_SECONDS="none", ZESU_SCRATCH_MEMORY_GIB="64",
                       ZESU_MODULE_LIMIT_GIB="64", ZESU_GATE_MODULE_LIMIT_GIB="32",
                       ZESU_WRITER_ID=writer)
    command = [str(workspace / "tools/resource_guard.sh"), "scope", writer,
               "--cpu", "unlimited", "--", python, str(Path(__file__).resolve()),
               "--capture-client" if capture_only else "--client", str(request_file), str(result_file)]
    save_json(directory / "ADMISSION-REQUEST.json", {"command": command,
               "environment": {key: value for key, value in environment.items()
                               if key.startswith(("ZESU_", "ROCQ_"))}})
    process = subprocess.run(command, env=environment, cwd=workspace)
    if not result_file.is_file():
        raise ValueError("The admitted MCP controller returned no result. Exit status: "
                         + str(process.returncode))
    result = json.loads(result_file.read_text())
    if process.returncode and capture_only:
        result["admission_exit_status"] = process.returncode
    elif process.returncode:
        result.setdefault("completion", {}).setdefault("reasons", []).append(
            "The admitted MCP controller exited with status " + str(process.returncode))
        result["completion"]["trace_complete"] = False
    return result


def run(request, out_dir):
    """Run the retained legacy projection route."""
    return _admit(request, out_dir)


def run_capture(request, out_dir):
    """Capture raw evidence without materializing a projected BACKEND result."""
    return _admit(request, out_dir, capture_only=True)


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[1] == "--project":
        request_file, result_file = map(Path, sys.argv[2:])
        save_json(result_file, project_session(json.loads(request_file.read_text()), result_file.parent))
    elif len(sys.argv) == 4 and sys.argv[1] == "--capture-client":
        request_file, result_file = map(Path, sys.argv[2:])
        save_json(result_file, asyncio.run(_run(json.loads(request_file.read_text()), result_file.parent.parent,
                                              capture_only=True)))
    elif len(sys.argv) == 4 and sys.argv[1] == "--client":
        request_file, result_file = map(Path, sys.argv[2:])
        save_json(result_file, asyncio.run(_run(json.loads(request_file.read_text()), result_file.parent.parent)))
    elif sys.argv[1:] == ["--server"]:
        server_main()
    else:
        raise SystemExit("Import run(request, out_dir), or use --server under MCP.")
