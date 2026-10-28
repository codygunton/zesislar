"""Stage the complete stock guard closure before a private launch."""

import hashlib
from pathlib import Path
import shutil


GUARD_RUNTIME_FILES = (
    "tools/resource_guard.sh",
    "tools/rocq_mcp_guarded.sh",
    "tools/rocq_coqc_guarded.sh",
    "tools/coqc_findlib.py",
    "tools/run_registry.py",
    "tools/dune_trace_guard.py",
    "tools/coqc_recipe.py",
    "tools/dune_build_dir.py",
    "tools/module_memory.py",
    "tools/det/prom.py",
    "tools/det/coqc_slots.py",
    "tools/block/guard_workspace.py",
)


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def checked_bindings(rows):
    """Coalesce identical aliases while constructing input bindings.

    This does not replace the final runtime's strict duplicate-path check.
    Conflicting hashes fail before any file validation or workspace change.
    """
    unique = {}
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {"path", "sha256"}
                or not isinstance(row["path"], str)
                or not isinstance(row["sha256"], str)
                or len(row["sha256"]) != 64
                or any(c not in "0123456789abcdef" for c in row["sha256"])):
            raise ValueError("A guard binding has invalid fields.")
        path = str(Path(row["path"]).resolve())
        if path in unique and unique[path]["sha256"] != row["sha256"]:
            raise ValueError("Guard bindings have conflicting hashes: " + path)
        unique[path] = {"path": path, "sha256": row["sha256"]}
    for path, row in unique.items():
        if not Path(path).is_file():
            raise ValueError("A required guard helper is missing: " + path)
        if digest(path) != row["sha256"]:
            raise ValueError("A guard binding changed: " + path)
    return list(unique.values())


def guard_bindings(source_root):
    """Bind every helper, including nested helpers and this implementation."""
    root = Path(source_root).resolve()
    rows = []
    for relative in GUARD_RUNTIME_FILES:
        path = root / relative
        if not path.is_file():
            raise ValueError("A required guard helper is missing: " + relative)
        rows.append({"path": str(path), "sha256": digest(path)})
    checked = checked_bindings(rows)
    if len(checked) != len(GUARD_RUNTIME_FILES):
        raise ValueError("Distinct guard helpers share one source path.")
    return checked


def stage_guard_tools(source_root, workspace, *, expected=None):
    """Copy verified helpers into a distinct workspace without shared inodes."""
    source_root, workspace = Path(source_root).resolve(), Path(workspace).resolve()
    if source_root == workspace:
        raise ValueError("The guard workspace must differ from its source root.")
    sources = guard_bindings(source_root)
    if expected is not None:
        if set(expected) != set(GUARD_RUNTIME_FILES):
            raise ValueError("The guard helper closure is incomplete.")
        for relative, row in zip(GUARD_RUNTIME_FILES, sources):
            if expected[relative] != row["sha256"]:
                raise ValueError("A guard binding changed: " + relative)
    for relative in GUARD_RUNTIME_FILES:
        target = workspace / relative
        if not target.parent.resolve().is_relative_to(workspace):
            raise ValueError("A guard helper destination leaves its workspace.")
        if target.exists() and not target.is_symlink() and target.samefile(source_root / relative):
            raise ValueError("A guard helper shares its source inode: " + relative)
    copies = []
    for relative, row in zip(GUARD_RUNTIME_FILES, sources):
        source, target = Path(row["path"]), workspace / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink():
            target.unlink()
        shutil.copy2(source, target)
        if digest(target) != row["sha256"]:
            raise ValueError("A guard helper changed during copying: " + relative)
        if (source.stat().st_dev, source.stat().st_ino) == (target.stat().st_dev, target.stat().st_ino):
            raise ValueError("A guard helper shares its source inode: " + relative)
        copies.append({"relative_path": relative, "source": row,
                       "owned": {"path": str(target), "sha256": row["sha256"]}})
    validate_guard_tools(workspace, copies)
    return copies


def validate_guard_tools(workspace, copies):
    """Refuse an incomplete or changed closure before admission."""
    workspace = Path(workspace).resolve()
    if [row["relative_path"] for row in copies] != list(GUARD_RUNTIME_FILES):
        raise ValueError("The guard helper closure is incomplete or repeated.")
    for row in copies:
        target = workspace / row["relative_path"]
        if target.is_symlink() or not target.resolve().is_relative_to(workspace):
            raise ValueError("A guard helper destination leaves its workspace.")
        if row["owned"]["path"] != str(target):
            raise ValueError("A guard helper binding names another workspace.")
    checked_bindings([row["source"] for row in copies])
    checked_bindings([row["owned"] for row in copies])
