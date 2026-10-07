"""Preserve a compiler recipe across cached Dune builds."""

import hashlib
import json
import tempfile
from pathlib import Path


def trace_events(data: bytes):
    offset = 0

    def parse():
        nonlocal offset
        if data[offset:offset + 1] == b"(":
            offset += 1
            result = []
            while data[offset:offset + 1] != b")":
                result.append(parse())
            offset += 1
            return result
        colon = data.index(b":", offset)
        length = int(data[offset:colon])
        offset = colon + 1
        atom = data[offset:offset + length].decode()
        offset += length
        return atom

    while offset < len(data):
        try:
            event = parse()
        except (ValueError, IndexError, UnicodeDecodeError):
            break  # A running Dune process can leave its last event incomplete.
        yield event


def project_recipe(recipe):
    return recipe is not None and any(
        arg.startswith("ZesuSsz/") and arg.endswith(".v")
        for arg in recipe["command"])


def compiler_recipe(data: bytes):
    recipe = None
    for event in trace_events(data):
        if not isinstance(event, list) or event[:2] != ["process", "start"]:
            continue
        fields = {field[0]: field[1:] for field in event[3:]
                  if isinstance(field, list) and field}
        program = fields.get("prog", [""])[0]
        raw_args = fields.get("process_args", [])
        args = raw_args[0] if len(raw_args) == 1 and isinstance(raw_args[0], list) else raw_args
        if Path(program).name == "coqc" and any(arg.endswith(".v") for arg in args):
            candidate = {"command": [program, *args],
                         "working_dir": fields.get("dir", [None])[0]}
            if recipe is None or project_recipe(candidate) or not project_recipe(recipe):
                recipe = candidate
    return recipe


def remember_recipe(build_dir: Path):
    trace = build_dir / "trace.csexp"
    cache = build_dir / "coqc_recipe.json"
    recipe = compiler_recipe(trace.read_bytes()) if trace.exists() else None
    cached = json.loads(cache.read_text()) if cache.exists() else None
    if project_recipe(cached) and recipe is not None and not project_recipe(recipe):
        return cached
    if recipe is not None:
        recipe["working_dir"] = recipe["working_dir"] or str(build_dir / "default")
        with tempfile.TemporaryDirectory(dir=build_dir, prefix=".coqc-recipe-") as directory:
            pending = Path(directory) / "recipe.json"
            pending.write_text(json.dumps(recipe) + "\n")
            pending.replace(cache)
        return recipe
    return cached


def snapshot_recipe(build_dir: Path, destination: Path):
    """Seal one preflight recipe without replacing an existing snapshot."""
    destination = Path(destination)
    if destination.exists():
        raise ValueError("An existing recipe snapshot must be reused")
    recipe = remember_recipe(Path(build_dir))
    if recipe is None:
        raise ValueError("A compiler recipe is unavailable")
    data = (json.dumps(recipe, sort_keys=True) + "\n").encode()
    with destination.open("xb") as output:
        output.write(data)
    return hashlib.sha256(data).hexdigest()


def read_snapshot(path: Path, expected_sha256: str):
    """Check immutable bytes without consulting the mutable Dune trace."""
    data = Path(path).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected_sha256:
        raise ValueError("The compiler recipe snapshot changed")
    return json.loads(data)
