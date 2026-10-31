#!/usr/bin/env python3
"""Prepare isolated entry attempts. Proof execution requires a separate release."""

import argparse
from copy import deepcopy
import hashlib
import json
import math
from pathlib import Path
import shutil
import subprocess
import tempfile

from complete_goals_mcp import check_kernel_groups, goal_groups

SOURCE_COMMIT = "eea6cadd24f49346da92cc80a374f730de4cc7e6"
OWNED_WORKSPACE = Path(__file__).resolve().parents[4]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(value):
    path = Path(value)
    if path.is_absolute() or not path.parts or any(part in (".", "..") for part in path.parts):
        raise ValueError("The packet path must stay inside its owned directory.")
    return path


def positive(value, label):
    if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
        raise ValueError("The packet needs a positive measurement: " + label)
    return value


def budget(entry):
    values = [positive(entry[side]["cpu_seconds"], side) for side in ("predecessor", "successor")]
    return 3 * sum(values)


def worker_limit(available_bytes, region_reserve_bytes, peak_bytes):
    """Reserve region memory before calculating the pilot worker count."""
    if type(available_bytes) is not int or type(region_reserve_bytes) is not int:
        raise ValueError("Memory amounts must use integer bytes.")
    if available_bytes < 0 or region_reserve_bytes < 0:
        raise ValueError("Memory amounts must not be negative.")
    peak = positive(peak_bytes, "peak_bytes")
    return min(48, int(max(0, available_bytes * 7 // 10 - region_reserve_bytes) // peak))


def splice(author, entry, supplied):
    """Change only explicit value paths from the reviewed entry packet."""
    if set(supplied) != {"entry", "values"} or supplied["entry"] != entry["id"]:
        raise ValueError("The supplied values name a different entry.")
    values = supplied["values"]
    if not isinstance(values, dict) or set(values) != set(entry["author_value_paths"]):
        raise ValueError("The supplied values differ from the reviewed value paths.")
    result = deepcopy(author)
    for pointer, value in values.items():
        if not pointer.startswith("/bodies/"):
            raise ValueError("An author value must belong to one entry body.")
        parts = [part.replace("~1", "/").replace("~0", "~") for part in pointer[1:].split("/")]
        body = result["bodies"][int(parts[1])]
        if body["at"] != entry["pc"] or parts[2] in ("at", "annotations", "metadata_profile"):
            raise ValueError("An author value changes another entry or its metadata.")
        current = result
        for part in parts[:-1]:
            current = current[int(part)] if isinstance(current, list) else current[part]
        key = int(parts[-1]) if isinstance(current, list) else parts[-1]
        original = current[key]
        if isinstance(original, (dict, list)) or type(value) is not type(original):
            raise ValueError("An author value must preserve the scalar field type.")
        current[key] = value
    return result


def copy_bound(source, target, expected):
    """Copy one bound file without preserving a source inode or link."""
    source, target = Path(source), Path(target)
    if digest(source) != expected:
        raise ValueError("A bound input hash changed: " + str(source))
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():raise FileExistsError(target)
    from clone_copy import copy2
    copy2(source,target)
    before, after = source.stat(), target.stat()
    if (before.st_dev, before.st_ino) == (after.st_dev, after.st_ino) or target.is_symlink():
        raise ValueError("An owned copy shares its source inode.")
    if digest(target) != expected or digest(source) != expected:
        raise ValueError("A bound input changed during its copy.")
    return {"source": str(source.resolve()), "path": str(target.resolve()), "sha256": expected,
            "source_device": before.st_dev, "source_inode": before.st_ino,
            "device": after.st_dev, "inode": after.st_ino}


def retain_residual(export, output):
    """Retain full exported groups. Limit only the response excerpt."""
    if export.get("success") is not True:
        raise ValueError("The complete goal export failed.")
    source = Path(export["path"])
    if digest(source) != export["sha256"]:
        raise ValueError("The complete goal export hash changed.")
    value = json.loads(source.read_text())
    kernel = value["kernel_groups"]
    check_kernel_groups(value, kernel)
    if value["local_definition_export"]["original_state_preserved"] is not True:
        raise ValueError("The goal export did not preserve its source state.")
    goals = [goal for group in goal_groups(kernel) for goal in group]
    if not goals:
        raise ValueError("The complete export contains no residual goal.")
    retained = copy_bound(source, Path(output) / "RESIDUAL.json", export["sha256"])
    # The complete first goal stays inside RESIDUAL.json with every group.
    full = json.dumps(goals[0], ensure_ascii=False, indent=2).encode()
    excerpt = full[:4800].decode(errors="ignore")
    response = {"status": "fail", "residual": retained["path"], "sha256": retained["sha256"],
                "first_residual_excerpt": excerpt, "excerpt_truncated": len(full) > 4800}
    if len(json.dumps(response, ensure_ascii=False).encode()) > 6144:
        response["first_residual_excerpt"] = "The first residual remains in the complete artifact."
        response["excerpt_truncated"] = True
    return response


class CpuLedger:
    """Count inclusive cgroup CPU once. Keep the same roots until completion."""

    def __init__(self, roots, limit_seconds):
        candidates = sorted({Path(root).resolve() for root in roots},
                            key=lambda path: (len(path.parts), str(path)))
        self.roots = []
        for path in candidates:
            if not any(path.is_relative_to(parent) for parent in self.roots):
                self.roots.append(path)
        if not self.roots:
            raise ValueError("The attempt needs an owned cgroup root.")
        self.limit_usec = positive(limit_seconds, "CPU limit") * 1_000_000
        self.previous = {str(path): 0 for path in self.roots}

    def sample(self, usage):
        if set(usage) != set(self.previous):
            raise ValueError("The CPU roots changed during the attempt.")
        for root, value in usage.items():
            if type(value) is not int or value < self.previous[root]:
                raise ValueError("A cumulative CPU counter decreased.")
        self.previous = dict(usage)
        total = sum(usage.values())
        return {"cpu_seconds": total / 1_000_000, "budget_exceeded": total >= self.limit_usec,
                "method": "inclusive cpu.stat usage_usec across disjoint owned cgroup roots"}

    def read(self):
        usage = {}
        for root in self.roots:
            fields = dict(line.split() for line in (root / "cpu.stat").read_text().splitlines())
            usage[str(root)] = int(fields["usage_usec"])
        return self.sample(usage)


def prepare(packet_path, entry_id, values_path, attempts):
    packet_path, values_path = Path(packet_path).resolve(), Path(values_path).resolve()
    packet = json.loads(packet_path.read_text())
    if packet["schema"] != "entry-pilot.packet.v1" or packet["source_commit"] != SOURCE_COMMIT:
        raise ValueError("The packet must bind exact main eea6cadd.")
    workspace = Path(packet["source_workspace"]).resolve()
    if workspace != OWNED_WORKSPACE or workspace.parent.name != ".worktrees":
        raise ValueError("The packet must use this tool's isolated worktree.")
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=workspace, text=True).strip()
    if actual != SOURCE_COMMIT:
        raise ValueError("The source workspace uses another commit.")
    rows = [entry for entry in packet["entries"] if entry["id"] == entry_id]
    if len(rows) != 1:
        raise ValueError("The packet needs one matching entry.")
    entry = rows[0]
    limit = budget(entry)
    for side in ("predecessor", "successor"):
        positive(entry[side]["peak_bytes"], side + " peak")
        if not entry[side].get("measurement_binding"):
            raise ValueError("The entry lacks a measurement binding.")
    author_path = relative(packet["author_path"])
    bindings = packet["source_files"]
    if str(author_path) not in bindings:
        raise ValueError("The source packet must bind the compact author input.")
    supplied = json.loads(values_path.read_text())
    author = json.loads((workspace / author_path).read_text())
    changed = splice(author, entry, supplied)
    attempts = Path(attempts).resolve()
    if not attempts.is_relative_to(workspace / "_build"):
        raise ValueError("Attempts must stay inside the owned workspace build directory.")
    attempts.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="attempt-", dir=attempts))
    copies = []
    for name, expected in bindings.items():
        name = relative(name)
        copies.append(copy_bound(workspace / name, output / "source" / name, expected))
    for binding in packet["object_files"]:
        name = relative(binding["relative_path"])
        copies.append(copy_bound(binding["source"], output / "objects" / name, binding["sha256"]))
    (output / "source" / author_path).write_text(json.dumps(changed, indent=2) + "\n")
    retained_packet = copy_bound(packet_path, output / "PACKET.json", digest(packet_path))
    retained_values = copy_bound(values_path, output / "VALUES.json", digest(values_path))
    record = {"schema": "entry-pilot.attempt.v1", "entry": entry_id, "status": "prepared",
              "proof_execution_released": False, "cpu_budget_seconds": limit,
              "result": None, "attempt": str(output), "inputs": copies,
              "packet": retained_packet, "author_values": retained_values,
              "author_output_sha256": digest(output / "source" / author_path)}
    (output / "ATTEMPT.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entry")
    parser.add_argument("author_values_file", type=Path)
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--attempts", required=True, type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    if not args.prepare_only:
        parser.error("Root did not release proof execution. Use --prepare-only.")
    try:
        result = prepare(args.packet, args.entry, args.author_values_file, args.attempts)
    except (OSError, ValueError, KeyError, IndexError, TypeError) as error:
        parser.error(str(error))
    print(json.dumps({key: result[key] for key in
                      ("schema", "entry", "status", "attempt", "cpu_budget_seconds", "result")}))


if __name__ == "__main__":
    main()
