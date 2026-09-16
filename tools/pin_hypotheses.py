#!/usr/bin/env python3
"""Pin a numbered Rocq hypothesis after testing it with rocq-mcp.

Run this with a Python environment that provides the MCP client package.
The rocq-mcp uv tool environment is one such environment.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import re
import stat
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*")
HEADER = re.compile(r"^([A-Za-z_][A-Za-z_0-9', ]*)\s*(?::=.+)?\s+:\s+(.+)$")
TIME_LIMIT = re.compile(r"(?:timed? out|time limit|timeout)", re.IGNORECASE)


@dataclass(frozen=True)
class Candidate:
    name: str
    statement: str


def context_candidates(goals: str) -> list[Candidate]:
    """Read the first visible goal's hypotheses, including wrapped types."""
    result: list[Candidate] = []
    active_names: list[str] = []
    active_type: list[str] = []

    def finish() -> None:
        if active_names:
            statement = " ".join(active_type).strip()
            result.extend(Candidate(name, statement) for name in active_names)

    for line in goals.splitlines():
        if line.startswith("|-") or line.startswith("Goal 2:"):
            finish()
            break
        match = HEADER.match(line)
        if match and all(NAME.fullmatch(name.strip()) for name in match.group(1).split(",")):
            finish()
            active_names = [name.strip() for name in match.group(1).split(",")]
            active_type = [match.group(2)]
        elif active_names:
            active_type.append(line.strip())
    else:
        finish()
    return result


def replace_name(text: str, old: str, new: str) -> str:
    pattern = re.compile(rf"(?<![A-Za-z_0-9']){re.escape(old)}(?![A-Za-z_0-9'])")
    return pattern.sub(new, text)


def trial_tactic(template: str, candidate: str) -> str:
    if "{candidate}" not in template:
        raise ValueError("the trial tactic must contain {candidate}")
    return template.replace("{candidate}", candidate)


def patch_lines(path: Path, line: int, old: str, new: str, statement: str) -> str:
    lines = path.read_text().splitlines(keepends=True)
    if line < 1 or line > len(lines):
        raise ValueError("the failing line is outside the file")
    original = lines[line - 1]
    replaced = replace_name(original, old, new)
    if replaced == original:
        raise ValueError(f"{old} does not occur on line {line}")
    indent = re.match(r"[ \t]*", original).group(0)
    selector = f"{indent}match goal with H : ({statement}) |- _ => rename H into {new} end.\n"
    lines[line - 1] = selector + replaced
    return "".join(lines)


def call_data(result: object) -> dict:
    data = result.structuredContent
    if not isinstance(data, dict):
        raise RuntimeError("rocq-mcp returned no structured content")
    if not data.get("success"):
        raise RuntimeError(data.get("error", "rocq-mcp call failed"))
    return data


def prefix_chunks(prefix: str, sentences_per_chunk: int) -> list[str]:
    """Split at complete source lines, never inside a Rocq sentence."""
    chunks: list[str] = []
    lines: list[str] = []
    sentences = 0
    last_complete = False
    for line in prefix.splitlines(keepends=True):
        lines.append(line)
        stripped = line.strip()
        if not stripped:
            continue
        last_complete = stripped.endswith(".") or stripped in {"{", "}", "-", "+", "*"}
        if last_complete:
            sentences += 1
        if sentences >= sentences_per_chunk:
            chunks.append("".join(lines))
            lines = []
            sentences = 0
    if lines:
        if not last_complete:
            raise ValueError("the prefix ends inside a Rocq sentence")
        chunks.append("".join(lines))
    return chunks


async def proof_state(session: object, file: Path, workspace: Path,
                      theorem: str | None, line: int, prefix: str,
                      sentences_per_chunk: int, prefix_timeout: int) -> dict:
    # A cursor in leading whitespace is before the failing sentence.
    position = await session.call_tool("rocq_start", {
        "file": str(file), "line": line - 1, "character": 0,
        "workspace": str(workspace),
    })
    data = position.structuredContent
    if isinstance(data, dict) and data.get("success"):
        return data
    if theorem is None:
        raise RuntimeError((data or {}).get("error", "rocq_start failed"))
    if not prefix.strip():
        raise RuntimeError("theorem fallback needs a nonempty --prefix-file")
    started = call_data(await session.call_tool("rocq_start", {
        "file": str(file), "theorem": theorem, "workspace": str(workspace),
    }))
    state = started
    for number, chunk in enumerate(prefix_chunks(prefix, sentences_per_chunk), start=1):
        response = await session.call_tool("rocq_check", {
            "from_state": state["state_id"], "body": chunk,
            "workspace": str(workspace), "timeout": prefix_timeout,
        })
        try:
            state = call_data(response)
        except RuntimeError as error:
            raise RuntimeError(f"prefix chunk {number} failed: {error}") from error
        if state.get("proof_finished"):
            raise RuntimeError(f"prefix chunk {number} finished the proof before the failing line")
    return state


async def test_candidates(session: object, state: dict, candidates: list[Candidate],
                          template: str, timeout: int) -> tuple[list[Candidate], list[Candidate]]:
    winners: list[Candidate] = []
    unresolved: list[Candidate] = []
    for offset in range(0, len(candidates), 20):
        batch = candidates[offset:offset + 20]
        tactics = [trial_tactic(template, candidate.name) for candidate in batch]
        response = await session.call_tool("rocq_step_multi", {
            "from_state": state["state_id"], "tactics": tactics,
            "timeout": timeout,
        })
        tested = response.structuredContent
        if not isinstance(tested, dict):
            unresolved.extend(candidates[offset:])
            break
        results = tested.get("results", tested.get("partial_results", []))
        for candidate, result in zip(batch, results):
            if result.get("success"):
                winners.append(candidate)
            elif result.get("reason") in {"timeout", "lock_contended", "crashed"} or TIME_LIMIT.search(result.get("error") or ""):
                unresolved.append(candidate)
        if not tested.get("success") or len(results) != len(batch):
            unresolved.extend(candidates[offset + len(results):])
            break
    return winners, unresolved


async def run(args: argparse.Namespace) -> int:
    try:
        from mcp import ClientSession, StdioServerParameters, stdio_client
    except ImportError as error:
        raise RuntimeError("run with a Python environment that provides the MCP client") from error

    source = Path(args.file).resolve()
    workspace = Path(args.workspace).resolve()
    old = args.old_name
    new = args.new_name
    if not NAME.fullmatch(old) or not NAME.fullmatch(new):
        raise ValueError("hypothesis names must be Rocq identifiers")
    if old == new:
        raise ValueError("the new name must differ from the old name")
    if not source.is_file() or not source.is_relative_to(workspace):
        raise ValueError("the Rocq file must be inside the workspace")
    if args.write and not args.log:
        raise ValueError("--write requires --log for the mandatory repair record")
    original_text = source.read_text()
    prefix = Path(args.prefix_file).read_text() if args.prefix_file else ""
    env = dict(os.environ)
    if args.switch_bin:
        env["PATH"] = args.switch_bin + os.pathsep + env.get("PATH", "")
    params = StdioServerParameters(command=args.mcp_command, env=env)

    async with stdio_client(params) as (reader, writer):
        async with ClientSession(reader, writer) as session:
            await session.initialize()
            health = call_data(await session.call_tool("rocq_health", {}))
            if not health.get("ok") or not health.get("toolchain", {}).get("pet", {}).get("path"):
                raise RuntimeError("rocq-mcp has no working pet toolchain")
            state = await proof_state(session, source, workspace, args.theorem,
                                      args.line, prefix,
                                      args.prefix_sentences, args.prefix_timeout)
            if "state_id" not in state or "goals" not in state:
                raise RuntimeError("rocq_start did not return a goal state")
            candidates = context_candidates(state["goals"])
            if args.type_regex:
                pattern = re.compile(args.type_regex)
                candidates = [candidate for candidate in candidates
                              if pattern.search(candidate.statement)]
            candidates = [candidate for candidate in candidates if candidate.name != new]
            if not candidates:
                raise RuntimeError("no compatible context hypotheses are visible")
            winners, unresolved = await test_candidates(session, state, candidates,
                                                          args.trial, args.timeout)
            report = {
                "file": str(source), "line": args.line, "old_name": old,
                "candidates": [candidate.__dict__ for candidate in candidates],
                "winners": [candidate.__dict__ for candidate in winners],
                "unresolved": [candidate.__dict__ for candidate in unresolved],
            }
            if unresolved:
                print(json.dumps(report, indent=2))
                return 5
            if len(winners) != 1:
                print(json.dumps(report, indent=2))
                return 3

            winner = winners[0]
            if source.read_text() != original_text:
                raise RuntimeError("the Rocq file changed during the MCP trials")
            patched = patch_lines(source, args.line, old, new, winner.statement)
            # Test the statement selector and the following tactic in a fresh copy.
            with tempfile.TemporaryDirectory(prefix="pin-hypotheses-", dir=workspace) as temp:
                copied = Path(temp) / source.name
                copied.write_text(source.read_text())
                fresh = await proof_state(session, copied, workspace, args.theorem,
                                          args.line, prefix,
                                          args.prefix_sentences, args.prefix_timeout)
                selector = f"match goal with H : ({winner.statement}) |- _ => rename H into {new} end"
                validated = call_data(await session.call_tool("rocq_step_multi", {
                    "from_state": fresh["state_id"],
                    "tactics": [selector + "; " + trial_tactic(args.trial, new)],
                    "timeout": args.timeout,
                }))
                if not validated["results"][0].get("success"):
                    report["selector_error"] = validated["results"][0].get("error")
                    print(json.dumps(report, indent=2))
                    return 4

            report["selected_statement"] = winner.statement
            report["selector"] = selector + "."
            report["replacement"] = replace_name(original_text.splitlines()[args.line - 1], old, new)
            print(json.dumps(report, indent=2))
            if args.write:
                if source.read_text() != original_text:
                    raise RuntimeError("the Rocq file changed before the source edit")
                with tempfile.NamedTemporaryFile(mode="w", dir=source.parent,
                                                 prefix=source.name + ".pin-",
                                                 delete=False) as output:
                    output.write(patched)
                    temporary = Path(output.name)
                temporary.chmod(stat.S_IMODE(source.stat().st_mode))
                temporary.replace(source)
            if args.log and args.write:
                with Path(args.log).open("a") as output:
                    output.write(json.dumps({key: report[key] for key in
                                             ("file", "line", "old_name", "selected_statement")}) + "\n")
            return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("file", help="the Rocq source file")
    parser.add_argument("line", type=int, help="the 1-based failing tactic line")
    parser.add_argument("old_name", help="the numbered hypothesis used on that line")
    parser.add_argument("new_name", help="the descriptive replacement name")
    parser.add_argument("--trial", required=True,
                        help="one tactic string with {candidate}; include the next tactic")
    parser.add_argument("--theorem", help="fallback theorem if file-position start fails")
    parser.add_argument("--prefix-file", help="prior tactic sentences for theorem fallback")
    parser.add_argument("--prefix-sentences", type=int, default=5,
                        help="complete Rocq sentences per fallback check")
    parser.add_argument("--prefix-timeout", type=int, default=30,
                        help="seconds allowed for each fallback check")
    parser.add_argument("--type-regex", help="filter compatible printed hypothesis types")
    parser.add_argument("--workspace", default=".")
    parser.add_argument("--mcp-command", default="rocq-mcp")
    parser.add_argument("--switch-bin", help="pinned Rocq switch bin directory")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--log", help="append a JSON line for the selected statement")
    parser.add_argument("--write", action="store_true", help="apply the tested source edit")
    args = parser.parse_args()
    if args.prefix_sentences < 1 or args.prefix_timeout < 1:
        parser.error("prefix bounds must be positive")
    try:
        return asyncio.run(run(args))
    except ExceptionGroup as error:
        cause: Exception = error
        while isinstance(cause, ExceptionGroup):
            cause = cause.exceptions[0]
        print(f"pin_hypotheses: {cause}", file=sys.stderr)
        return 2
    except (OSError, ValueError, RuntimeError) as error:
        print(f"pin_hypotheses: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
