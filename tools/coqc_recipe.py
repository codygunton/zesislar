"""Preserve a compiler recipe across cached Dune builds."""

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
            recipe = {"command": [program, *args],
                      "working_dir": fields.get("dir", [None])[0]}
    return recipe


def remember_recipe(build_dir: Path):
    trace = build_dir / "trace.csexp"
    cache = build_dir / "coqc_recipe.json"
    recipe = compiler_recipe(trace.read_bytes()) if trace.exists() else None
    if recipe is not None:
        recipe["working_dir"] = recipe["working_dir"] or str(build_dir / "default")
        with tempfile.TemporaryDirectory(dir=build_dir, prefix=".coqc-recipe-") as directory:
            pending = Path(directory) / "recipe.json"
            pending.write_text(json.dumps(recipe) + "\n")
            pending.replace(cache)
        return recipe
    return json.loads(cache.read_text()) if cache.exists() else None
