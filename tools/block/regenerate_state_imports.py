#!/usr/bin/env python3
"""Regenerate reviewed state imports without changing state bodies."""
import argparse
import hashlib
import json
import re
from pathlib import Path

import gen_block


def replace_imports(source: str, record: dict) -> str:
    definition = re.search(r"^Definition " + re.escape(record["name"]) + r"\b",
                           source, re.MULTILINE)
    if definition is None:
        raise ValueError(f"missing definition: {record['name']}")
    first_definition = re.search(r"^Definition ", source, re.MULTILINE)
    prefix, body = (source[:first_definition.start()],
                    source[first_definition.start():])
    if hashlib.sha256(body.encode()).hexdigest() != record["body_sha256"]:
        raise ValueError(f"state body differs from manifest: {record['name']}")
    first_import = prefix.index("Require Import ")
    remaining = re.sub(r"^Require Import [\w.]+\.\n", "",
                       prefix[first_import:], flags=re.MULTILINE)
    if remaining.strip():
        raise ValueError(f"unsupported state preamble: {record['name']}")
    imports = gen_block.state_imports(record["name"], record["imports"])
    return (prefix[:first_import]
            + "\n".join(f"Require Import {module}." for module in imports)
            + "\n\n" + body)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    records = json.loads(gen_block.STATE_IMPORT_MANIFEST.read_text())["states"]
    changed = 0
    for record in records:
        if not re.fullmatch(r"ZesuSsz\.Generated\.WriteSuccess\.States\.\w+",
                            record["module"]):
            raise ValueError(f"invalid state module: {record['module']}")
        path = root / (record["module"].replace(".", "/") + ".v")
        source = path.read_text()
        updated = replace_imports(source, record)
        if source != updated:
            changed += 1
            if not args.check:
                path.write_text(updated)
    print(f"{len(records)} state bodies match; {changed} import lists differ")
    return int(args.check and changed != 0)


if __name__ == "__main__":
    raise SystemExit(main())
