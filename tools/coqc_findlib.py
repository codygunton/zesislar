"""Preserve the private Dune findlib path for guarded MCP compilers."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


RECORD_NAME = "coqc-ocamlpath.json"
RECORD_KEYS = {"schema_version", "workspace", "private_build", "OCAMLPATH"}


def workspace_root(start):
    for candidate in (Path(start).resolve(), *Path(start).resolve().parents):
        # Dune can copy dune-project into its artifact directory.
        if "_build" not in candidate.parts and (candidate / "dune-project").is_file():
            return candidate
    return None


def active_build(workspace):
    default = Path(workspace) / "_build/default"
    if not default.exists() and not default.is_symlink():
        return None
    if not default.is_dir():
        raise ValueError("The active Dune artifact directory is unavailable")
    resolved = default.resolve()
    if resolved.name != "default":
        raise ValueError("The active Dune artifact directory has an invalid name")
    build = resolved.parent
    if not build.is_relative_to(Path(workspace).resolve()):
        raise ValueError("The active private build leaves its workspace")
    return build


def check_record(record, workspace, build):
    if (not isinstance(record, dict) or set(record) != RECORD_KEYS
            or type(record["schema_version"]) is not int
            or record["schema_version"] != 1):
        raise ValueError("The compiler findlib record has an invalid schema")
    if (record["workspace"] != str(Path(workspace).resolve())
            or record["private_build"] != str(Path(build).resolve())):
        raise ValueError("The compiler findlib record has a different workspace or build")
    value = record["OCAMLPATH"]
    if not isinstance(value, str) or any(char in value for char in "\x00\r\n"):
        raise ValueError("The compiler findlib record has an invalid OCAMLPATH")
    # A relative findlib path changes meaning when MCP changes the compiler cwd.
    if any(item and not Path(item).is_absolute() for item in value.split(":")):
        raise ValueError("The compiler findlib record requires absolute findlib paths")
    return value


def record_dune_environment(tools_directory, environment):
    tools = Path(tools_directory).resolve()
    if tools.parent.name != "default":
        return None  # The ordinary source wrapper has no private Dune recipe.
    build = tools.parent.parent
    workspace = workspace_root(build)
    # Independent Dune builds do not change the artifact mapping used by MCP.
    # Record this compiler's build. Fallback lookup still uses the active mapping.
    if workspace is None or not build.is_relative_to(workspace):
        raise ValueError("The Dune compiler build leaves its workspace")
    if "OCAMLPATH" not in environment:
        raise ValueError("The Dune compiler environment lacks OCAMLPATH")
    record = {"schema_version": 1, "workspace": str(workspace),
              "private_build": str(build), "OCAMLPATH": environment["OCAMLPATH"]}
    check_record(record, workspace, build)
    payload = (json.dumps(record, sort_keys=True) + "\n").encode()
    destination = build / RECORD_NAME
    # link publishes one complete record without replacing another compiler's record.
    with tempfile.NamedTemporaryFile(dir=build, prefix=".coqc-findlib-", delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
    try:
        try:
            os.link(temporary, destination)
        except FileExistsError:
            if destination.read_bytes() != payload:
                raise ValueError("The private build compiler findlib record changed")
    finally:
        temporary.unlink()
    return destination


def compiler_environment(start, environment):
    result = dict(environment)
    workspace = workspace_root(start)
    build = active_build(workspace) if workspace else None
    if build is None:
        return result
    path = build / RECORD_NAME
    if not path.is_file():
        raise ValueError("The active private build lacks its compiler findlib record")
    try:
        record = json.loads(path.read_text())
    except (ValueError, UnicodeError) as error:
        raise ValueError("The compiler findlib record is malformed") from error
    # Replace the ambient value. Never append paths from another private build.
    result["OCAMLPATH"] = check_record(record, workspace, build)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="operation", required=True)
    record = commands.add_parser("record")
    record.add_argument("--tools-directory", type=Path, required=True)
    guarded = commands.add_parser("guarded")
    guarded.add_argument("--guard", required=True)
    guarded.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        if args.operation == "record":
            record_dune_environment(args.tools_directory, os.environ)
        else:
            command = args.command[1:] if args.command[:1] == ["--"] else args.command
            if not command:
                raise ValueError("The guarded compiler command is absent")
            environment = compiler_environment(Path.cwd(), os.environ)
            status = subprocess.run([args.guard, "wait"], env=environment).returncode
            if status:
                raise SystemExit(status)
            os.execvpe(args.guard, [args.guard, "scope", "rocq-mcp-coqc", "--", *command], environment)
    except (ValueError, OSError) as error:
        parser.exit(2, f"compiler findlib setup: {error}\n")


if __name__ == "__main__":
    main()
