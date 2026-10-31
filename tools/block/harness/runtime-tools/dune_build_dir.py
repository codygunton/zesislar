"""Give private Dune builds a stable logical path without sharing their files."""

from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import sys
import tempfile


ALIAS = "_dune-cache"
RECORD = "dune-build-dir.json"


def option(arguments, name, start):
    matches = []
    for index in range(start, len(arguments)):
        value = arguments[index]
        if value == name:
            if index + 1 == len(arguments):
                raise ValueError("A Dune path option requires a value.")
            matches.append((index, index + 1, arguments[index + 1]))
        elif value.startswith(name + "="):
            matches.append((index, index, value[len(name) + 1:]))
    if len(matches) > 1:
        raise ValueError("A Dune path option is repeated.")
    return matches[0] if matches else None


def invocation(command, cwd):
    # A gate can wrap Dune in build_record.py and opam exec. Keep their options.
    start = next((index for index, value in enumerate(command)
                  if Path(value).name == "dune" and index + 1 < len(command)
                  and command[index + 1] in {"build", "rules", "describe"}), None)
    if start is None:
        return None
    root_option = option(command, "--root", start + 1)
    root = (Path(cwd) / root_option[2]).resolve() if root_option else Path(cwd).resolve()
    build_option = option(command, "--build-dir", start + 1)
    if build_option is None:
        return None
    physical = (root / build_option[2]).resolve()
    owned = (root / "_build/agents").resolve()
    if (not owned.is_relative_to(root) or owned == root
            or not physical.is_relative_to(owned) or physical == owned):
        raise ValueError("Canonical Dune caching requires a private _build/agents directory.")
    return root, physical, build_option


def active_dune(root):
    """Reject alias retargeting after an interrupted wrapper left Dune alive."""
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            if (process / "exe").resolve().name != "dune":
                continue
            cwd = (process / "cwd").resolve()
            if cwd == root or cwd.is_relative_to(root):
                return True
        except (OSError, ProcessLookupError):
            continue
    return False


@contextmanager
def canonical_command(command, *, cwd=None):
    selected = invocation(command, cwd or Path.cwd())
    if selected is None:
        yield list(command)
        return
    root, physical, (index, value_index, _) = selected
    physical.mkdir(parents=True, exist_ok=True)
    lock_path = root / "_build/agents/.dune-cache-alias.lock"
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        alias = root / ALIAS
        if alias.exists() and not alias.is_symlink():
            raise ValueError("The logical Dune directory is not an owned symlink.")
        if alias.is_symlink():
            previous = alias.resolve()
            if not previous.is_relative_to((root / "_build/agents").resolve()):
                raise ValueError("The logical Dune directory points outside private build storage.")
            if previous != physical and active_dune(root):
                raise ValueError("A Dune process still uses this workspace; do not retarget its alias.")
        if not alias.is_symlink() or alias.resolve() != physical:
            with tempfile.TemporaryDirectory(dir=alias.parent, prefix=".dune-alias-") as directory:
                pending = Path(directory) / "link"
                pending.symlink_to(os.path.relpath(physical, root), target_is_directory=True)
                pending.replace(alias)
        record = {"schema": 1, "workspace": str(root), "logical_directory": str(alias),
                  "physical_directory": str(physical)}
        with tempfile.TemporaryDirectory(dir=physical, prefix=".dune-alias-record-") as directory:
            pending = Path(directory) / RECORD
            pending.write_text(json.dumps(record, indent=2) + "\n")
            pending.replace(physical / RECORD)
        rewritten = list(command)
        rewritten[value_index] = (ALIAS if index != value_index else "--build-dir=" + ALIAS)
        # Run after opam sets PATH, so Dune finds the dependency wrapper first.
        shim_directory = Path(__file__).resolve().parent / "canonical-bin"
        start = next(index for index, value in enumerate(rewritten)
                     if Path(value).name == "dune" and index + 1 < len(rewritten)
                     and rewritten[index + 1] in {"build", "rules", "describe"})
        rewritten[start:start] = [sys.executable, '-B', str(Path(__file__).resolve()),
                                   "--execute", str(shim_directory)]
        yield rewritten


def physical_working_dir(build_dir, working_dir):
    """Keep saved recipes usable after the workspace alias selects another build."""
    build_dir = Path(build_dir).resolve()
    record_path = build_dir / RECORD
    if working_dir is None or not record_path.is_file():
        return working_dir
    record = json.loads(record_path.read_text())
    if record.get("schema") != 1 or record.get("physical_directory") != str(build_dir):
        raise ValueError("The logical Dune directory record does not bind this private build.")
    logical = Path(record["logical_directory"])
    path = Path(working_dir)
    return str(build_dir / path.relative_to(logical)) if path.is_relative_to(logical) else working_dir


if __name__ == "__main__":
    if len(sys.argv) < 4 or sys.argv[1] != "--execute":
        raise SystemExit("A canonical tool directory and a Dune command are required.")
    environment = dict(os.environ)
    environment["PATH"] = sys.argv[2] + os.pathsep + environment.get("PATH", "")
    os.execvpe(sys.argv[3], sys.argv[3:], environment)
