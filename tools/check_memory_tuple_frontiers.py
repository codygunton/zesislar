#!/usr/bin/env python3
"""Check consumer progress against five authenticated frontier checkpoints.

Run this script through the resource guard with a prepared fixture manifest.
The checks establish proof progress. They do not establish contract closure.
"""

import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import sys
import time

def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def file_reference(path):
    path = Path(path).resolve()
    return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


def checkpoint(snapshot):
    def goal(value):
        return {
            "ty": value["ty"],
            "hyps": [
                {"names": h["names"], "ty": h["ty"], "definition": h.get("def")}
                for h in value["hyps"]
            ],
        }

    def groups(value):
        # These five checkpoints have no focused stack frames.
        assert value["stack"] == [], "The proof has unexpected stack frames."
        return {name: [goal(g) for g in value[name]] for name in ("goals", "shelf", "given_up")}

    return {"ordinary": groups(snapshot), "kernel": groups(snapshot["kernel_groups"])}


def checkpoint_digest(snapshot):
    data = json.dumps(checkpoint(snapshot), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def command_digest(command):
    return hashlib.sha256(command.encode()).hexdigest()


def diagnostic_summary(error):
    lines = []
    for line in error.splitlines():
        if line.startswith(("Raised ", "Called ", "Re-raised ")):
            break
        lines.append(line)
    return " ".join(" ".join(lines).split())


async def run_case(args, row, expected):
    from mcp import ClientSession, StdioServerParameters
    from mcp.client.stdio import stdio_client

    output = args.output / row["id"]
    output.mkdir(parents=True)
    exports = output / "complete-goals"
    exports.mkdir()
    environment = dict(
        os.environ,
        ROCQ_WORKSPACE=str(args.workspace),
        ROCQ_DUNE_BUILD="0",
        ROCQ_MAX_SOURCE_SIZE="2097152",
        ROCQ_QUERY_TIMEOUT_CAP=str(args.timeout),
        ROCQ_PET_TIMEOUT=str(args.timeout),
        ZESU_COMPLETE_GOAL_DIR=str(exports),
    )
    state = None
    calls = []
    result = {"id": row["id"], "passed": False}
    assert file_reference(row["fixture"]["path"]) == row["fixture"]
    assert row["fixture"]["sha256"] == expected["fixture_sha256"]
    assert [command_digest(s[1]) for s in row["stages"]] == [s["command_sha256"] for s in expected["stages"]]
    server = StdioServerParameters(
        command=sys.executable,
        args=["-B", str(args.server)],
        cwd=str(args.workspace),
        env=environment,
    )
    async with stdio_client(server) as streams:
        async with ClientSession(*streams) as session:
            await session.initialize()

            async def call(tool, arguments):
                started = time.time_ns()
                raw = await session.call_tool(tool, arguments)
                value = raw.structuredContent
                if value is None:
                    value = json.loads(next(c.text for c in raw.content if hasattr(c, "text")))
                entry = {
                    "tool": tool,
                    "arguments": arguments,
                    "started_ns": started,
                    "ended_ns": time.time_ns(),
                    "result": value,
                }
                write_json(output / f"response-{len(calls):02d}.json", entry)
                calls.append(entry)
                return value

            try:
                health = await call("rocq_health", {})
                assert health.get("success"), health
                started = await call("rocq_start", {
                    "workspace": str(args.workspace), "file": row["fixture"]["path"],
                    "theorem": row["theorem"], "timeout": args.timeout,
                })
                assert started.get("success"), started
                state = started["state_id"]
                before = await call("rocq_complete_goals", {"from_state": state})
                assert before.get("success"), before
                assert checkpoint_digest(read_json(before["path"])) == expected["initial_checkpoint_sha256"], "The initial ordinary/kernel context changed."
                checked = await call("rocq_check", {
                    "from_state": state, "body": row["stages"][0][1],
                    "timeout": args.timeout,
                })
                state = checked.get("state_id", checked.get("last_valid_state_id", state))
                after = await call("rocq_complete_goals", {"from_state": state})
                assert after.get("success"), after
                result.update(before=before, consumer=checked, after=after)
                assert checked.get("success"), "The consumer refused before its reference checkpoint."
                assert checkpoint_digest(read_json(after["path"])) == expected["consumer_checkpoint_sha256"], "The consumer did not reach its reference ordinary/kernel context."
                stages = []
                for (label, body), reference in zip(row["stages"][1:], expected["stages"][1:]):
                    checked = await call("rocq_check", {
                        "from_state": state, "body": body, "timeout": args.timeout,
                    })
                    state = checked.get("state_id", checked.get("last_valid_state_id", state))
                    exported = await call("rocq_complete_goals", {"from_state": state})
                    assert exported.get("success"), exported
                    stages.append({"label": label, "response": checked, "export": exported})
                    result["stages"] = stages
                    assert checked.get("success") is reference["success"], f"The {label} result changed."
                    if not checked.get("success"):
                        assert diagnostic_summary(checked.get("error", "")) == reference["diagnostic"], "The refusal diagnostic changed."
                        assert checkpoint_digest(read_json(exported["path"])) == expected["refusal_checkpoint_sha256"], "The refusal occurred at a different ordinary/kernel context."
                        result["reference_refusal_reached"] = True
                        break
                assert result.get("reference_refusal_reached"), "The replay did not reach its reference refusal."
                result["passed"] = True
            except Exception as error:
                result["error"] = str(error)
            finally:
                if state is not None:
                    aborted = await call("rocq_check", {"from_state": state, "body": "Abort.", "timeout": args.timeout})
                    result["session_aborted"] = aborted.get("success") is True
                    result["passed"] &= result["session_aborted"]
                health = await call("rocq_health", {})
                result["passed"] &= health.get("success") is True
    result["normal_transport_closed"] = True
    write_json(output / "RESULT.json", result)
    print(json.dumps({"id": row["id"], "passed": result["passed"]}), flush=True)
    return result


async def main(args):
    manifest = read_json(args.manifest)
    cases = read_json(args.cases)
    expected = {row["id"]: row for row in cases["cases"]}
    assert len(manifest["cases"]) == 5
    assert {row["id"] for row in manifest["cases"]} == set(expected)
    for binding in manifest["bindings"]:
        assert file_reference(binding["path"]) == binding
    semaphore = asyncio.Semaphore(args.jobs)

    async def bounded(row):
        async with semaphore:
            return await run_case(args, row, expected[row["id"]])

    rows = await asyncio.gather(*(bounded(row) for row in manifest["cases"]))
    for binding in manifest["bindings"]:
        assert file_reference(binding["path"]) == binding
    passed = all(row["passed"] for row in rows)
    write_json(args.output / "RESULT.json", {
        "passed": passed, "rows": rows, "native_reruns": 0,
        "new_premises": 0, "contract_acceptance": False,
        "manifest": file_reference(args.manifest), "cases": file_reference(args.cases),
    })
    return 0 if passed else 1


if __name__ == "__main__":
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--server", type=Path, default=root / "tools/block/complete_goals_mcp.py")
    parser.add_argument("--cases", type=Path, default=root / "ZesuSsz/Evidence/MemoryTupleFrontierRegressionCases.json")
    parser.add_argument("--jobs", type=int, default=5)
    parser.add_argument("--timeout", type=int, default=300)
    arguments = parser.parse_args()
    assert 1 <= arguments.jobs <= 8
    arguments.output.mkdir(parents=True, exist_ok=True)
    raise SystemExit(asyncio.run(main(arguments)))
