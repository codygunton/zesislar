"""Validate all native entry declarations before any primary proof request."""
import argparse
import asyncio
from contextlib import asynccontextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

from call_journal import ToolJournal
from complete_goals_mcp import check_kernel_groups
from launch_imports import require_modules, validate_launch_imports
from setup_fallback import load_slice


NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
GROUPS = ("goals", "stack", "shelf", "given_up")


def file_reference(path):
    path = Path(path)
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"path": str(path), "sha256": digest, "bytes": path.stat().st_size}


def checked_file(binding, workspace=None):
    if not isinstance(binding, dict) or set(binding) != {"path", "sha256", "bytes"}:
        raise ValueError("The entry file needs an exact path, SHA256, and byte count.")
    if (not isinstance(binding["path"], str) or not Path(binding["path"]).is_absolute()
            or not isinstance(binding["sha256"], str)
            or re.fullmatch(r"[0-9a-f]{64}", binding["sha256"]) is None
            or type(binding["bytes"]) is not int or binding["bytes"] < 0):
        raise ValueError("The entry file binding has an invalid type or value.")
    path = Path(binding["path"]).resolve(strict=True)
    if workspace is not None and not path.is_relative_to(workspace):
        raise ValueError("The entry file leaves its workspace.")
    if not path.is_file() or file_reference(binding["path"]) != binding:
        raise ValueError("The entry file differs from its binding.")
    stat = path.stat()
    return {"binding": binding, "resolved": str(path),
            "identity": [stat.st_dev, stat.st_ino, stat.st_size,
                         stat.st_mtime_ns, stat.st_ctime_ns]}


def unchanged_file(checked):
    if checked_file(checked["binding"]) != checked:
        raise ValueError("An entry input changed during preflight.")


def prepare_entries(entries, workspace, function):
    """Check every source and artifact map before starting an MCP session."""
    workspace = Path(workspace).resolve(strict=True)
    if not isinstance(entries, list) or not entries:
        raise ValueError("The entry preflight needs at least one selected declaration.")
    prepared, names = [], set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"id", "source", "theorem", "artifacts"}:
            raise ValueError("The entry preflight row has invalid fields.")
        name, theorem = entry["id"], entry["theorem"]
        if (not isinstance(name, str) or re.fullmatch(r"[A-Za-z0-9_-]+", name) is None
                or name in names or not isinstance(theorem, str) or NAME.fullmatch(theorem) is None):
            raise ValueError("The entry preflight needs unique IDs and exact theorem names.")
        names.add(name)
        source = checked_file(entry["source"], workspace)
        text = Path(source["resolved"]).read_text()
        interactive = load_slice(text)
        marker = re.compile(r"(?m)^(?:Lemma|Theorem) " + re.escape(theorem) + r"\b")
        matches = list(marker.finditer(interactive))
        if len(matches) != 1:
            raise ValueError("The scratch does not declare the selected theorem exactly once.")
        imports = validate_launch_imports(text, function, workspace)
        required = require_modules(text)
        artifacts = entry["artifacts"]
        if (not isinstance(artifacts, dict) or set(artifacts) != required
                or any(not isinstance(module, str) or NAME.fullmatch(module) is None for module in artifacts)):
            raise ValueError("Every direct Require module needs one exact object binding.")
        objects = {module: checked_file(binding) for module, binding in artifacts.items()}
        if any(Path(row["resolved"]).suffix != ".vo" for row in objects.values()):
            raise ValueError("An entry module binding must identify a Rocq object.")
        prepared.append({"id": name, "theorem": theorem, "source": source,
                         "interactive": interactive, "imports": imports, "artifacts": objects})
    return prepared


def response_data(raw):
    value = raw.get("structuredContent") if isinstance(raw, dict) else raw.structuredContent
    if not isinstance(value, dict):
        raise ValueError("The retained MCP response has no structured result.")
    return value


def checked_export(result, state_id, directory):
    if (result.get("success") is not True or type(result.get("state_id")) is not int
            or result["state_id"] != state_id):
        raise ValueError("The entry export refused or returned a different state.")
    binding = {key: result[key] for key in ("path", "sha256", "bytes")}
    checked = checked_file(binding, directory)
    value = json.loads(Path(checked["resolved"]).read_bytes())
    if any(not isinstance(value.get(group), list) for group in GROUPS):
        raise ValueError("The entry export omits a complete goal group.")
    if any(not isinstance(frame, list) or len(frame) != 2
           or any(not isinstance(side, list) for side in frame) for frame in value["stack"]):
        raise ValueError("The entry export has an incomplete focus frame.")
    if (not isinstance(value.get("kernel_groups"), dict)
            or value.get("local_definition_export", {}).get("original_state_preserved") is not True):
        raise ValueError("The entry export lacks checked kernel terms.")
    check_kernel_groups(value, value["kernel_groups"])
    return checked


def process_identity(pid):
    if type(pid) is not int or pid <= 0:
        raise ValueError("The entry diagnostic needs a positive owned Pet PID.")
    fields = Path("/proc", str(pid), "stat").read_text().rsplit(")", 1)[1].split()
    return {"pid": pid, "start_ticks": int(fields[19]), "state": fields[0]}


def matching_live(identity):
    try:
        current = process_identity(identity["pid"])
    except (FileNotFoundError, ProcessLookupError):
        return False
    return current["start_ticks"] == identity["start_ticks"] and current["state"] not in {"Z", "X"}


async def check_entries(entries, workspace, function, output, session_factory):
    """Return a release receipt only after every selected entry passes."""
    workspace = Path(workspace).resolve(strict=True)
    output = Path(output).resolve()
    if not output.is_relative_to(workspace) or output.exists():
        raise ValueError("The entry preflight needs a fresh output inside its workspace.")
    prepared = prepare_entries(entries, workspace, function)
    output.mkdir(parents=True, exist_ok=False)
    results = []
    for entry in prepared:
        directory = output / entry["id"]
        directory.mkdir()
        interactive = directory / "Entry.v"
        interactive.write_text(entry["interactive"])
        interactive_binding = checked_file(file_reference(interactive), workspace)
        journal = ToolJournal(directory / "calls")
        result = {"id": entry["id"], "source": entry["source"],
                  "interactive": interactive_binding, "artifacts": entry["artifacts"],
                  "passed": False, "pet": None, "normal_context_closure": False,
                  "owned_pet_exited": None, "primary_calls": 0}
        try:
            async with session_factory(directory) as session:
                try:
                    await journal.initialize(session)
                    async def call(tool, arguments):
                        if tool not in {"rocq_health", "rocq_start", "rocq_diag", "rocq_query", "rocq_complete_goals"}:
                            raise ValueError("The entry preflight forbids proof execution.")
                        return response_data(await journal.call_tool(session, tool, arguments))
                    health = await call("rocq_health", {})
                    if health.get("success") is not True or health.get("ok") is not True:
                        raise ValueError("The entry toolchain health check refused.")
                    started = await call("rocq_start", {"workspace": str(workspace),
                        "file": str(interactive), "theorem": entry["theorem"], "timeout": 60})
                    diagnostic = await call("rocq_diag", {})
                    if diagnostic.get("success") is not True:
                        raise ValueError("The owned Pet diagnostic refused.")
                    result["pet"] = process_identity(diagnostic.get("pet", {}).get("pid"))
                    state_id = started.get("state_id")
                    if started.get("success") is not True or type(state_id) is not int or state_id <= 0:
                        raise ValueError("The rendered entry declaration refused.")
                    before = checked_export(await call("rocq_complete_goals", {"from_state": state_id}), state_id, directory)
                    for module, artifact in entry["artifacts"].items():
                        located = await call("rocq_query", {"from_state": state_id,
                            "command": "Locate Library " + module + ".", "timeout": 60})
                        expected = re.escape(module + " has been loaded from file") + r"[ \t\r\n]+" + re.escape(artifact["resolved"])
                        if (located.get("success") is not True or type(located.get("from_state_id")) is not int
                                or located["from_state_id"] != state_id
                                or not isinstance(located.get("output"), str)
                                    or re.fullmatch(expected, located["output"].strip()) is None):
                            raise ValueError("The loaded module differs from its exact object binding: " + module)
                    after = checked_export(await call("rocq_complete_goals", {"from_state": state_id}), state_id, directory)
                    if before["binding"] != after["binding"] or before["resolved"] != after["resolved"]:
                        raise ValueError("The read-only artifact queries changed the entry export.")
                    result["export"] = after
                    unchanged_file(entry["source"])
                    unchanged_file(interactive_binding)
                    for artifact in entry["artifacts"].values():
                        unchanged_file(artifact)
                    result["entry_checked"] = True
                except BaseException as error:
                    result["error"] = {"type": type(error).__name__, "message": str(error)}
            result["normal_context_closure"] = True
        except BaseException as error:
            result["error"] = {"type": type(error).__name__, "message": str(error)}
        finally:
            if result["pet"] is not None:
                deadline = time.monotonic() + 10
                while matching_live(result["pet"]) and time.monotonic() < deadline:
                    await asyncio.sleep(0.1)
                result["owned_pet_exited"] = not matching_live(result["pet"])
            result["journal"] = journal.snapshot()
            result["passed"] = (result.get("entry_checked") is True
                                and result["normal_context_closure"] is True
                                and result["owned_pet_exited"] is True
                                and not result["journal"]["retention_failed"])
            (directory / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
        results.append(result)
        if not result["passed"]:
            break
    input_error = None
    try:
        for entry in prepared:
            unchanged_file(entry["source"])
            for artifact in entry["artifacts"].values():
                unchanged_file(artifact)
        for result in results:
            unchanged_file(result["interactive"])
    except (OSError, ValueError) as error:
        input_error = {"type": type(error).__name__, "message": str(error)}
    receipt = {"schema": 1, "passed": (input_error is None and len(results) == len(prepared)
                                      and all(row["passed"] for row in results)),
               "input_error": input_error,
               "selected_entries": len(prepared), "checked_entries": len(results),
               "entries": results, "primary_calls": 0,
               "scope": "Entry elaboration and loaded objects only. No instruction execution or proof closure."}
    (output / "REPORT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def owned_sessions(command, workspace):
    @asynccontextmanager
    async def factory(directory):
        from mcp import ClientSession, StdioServerParameters
        from mcp.client.stdio import stdio_client
        environment = {**os.environ, "ROCQ_WORKSPACE": str(workspace),
                       "ZESU_ROCQ_MCP_BINARY": str(Path(__file__).with_name("complete_goals_mcp.sh").resolve()),
                       "ZESU_MCP_PYTHON": sys.executable,
                       "ZESU_COMPLETE_GOAL_DIR": str(directory / "complete"),
                       "ZESU_FEEDBACK_DIR": str(directory / "feedback")}
        parameters = StdioServerParameters(command=command, env=environment, cwd=str(workspace))
        with (directory / "server.log").open("x") as log:
            async with stdio_client(parameters, errlog=log) as streams:
                async with ClientSession(*streams) as session:
                    yield session
    return factory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mcp-command", required=True)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_bytes())
    if not isinstance(manifest, dict) or set(manifest) != {"schema", "workspace", "function", "entries"} or type(manifest["schema"]) is not int or manifest["schema"] != 1:
        parser.error("The entry preflight manifest has an invalid schema.")
    workspace = Path(manifest["workspace"]).resolve(strict=True)
    result = asyncio.run(check_entries(manifest["entries"], workspace, manifest["function"], args.output,
                                      owned_sessions(args.mcp_command, workspace)))
    print(json.dumps({"passed": result["passed"], "report": file_reference(args.output / "REPORT.json"),
                      "primary_calls": 0}, sort_keys=True))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
