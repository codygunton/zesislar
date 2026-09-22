#!/usr/bin/env python3
"""Audit Print Assumptions for listed A6 lemmas before and after cleanup.

Compile generated scratch files with tools/coqc_scratch.sh. The capture step
accepts only successful scratch logs with every expected marker present.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from closed_cleanup_rewrite import listed_rows


MARKER = re.compile(r"^A6_(BEGIN|END)_(\d{4})$")
SUCCESS = re.compile(r"(?m)^exit=0 ms=\d+ rss_kb=\d+\s*$")
ANSI = re.compile(r"\x1b\[[0-9;]*m")


def selected_modules(list_path: Path, batch: int) -> dict[str, list[str]]:
    rows = listed_rows(list_path)
    modules: dict[str, list[str]] = {}
    for module, lemma in rows:
        modules.setdefault(module, []).append(lemma)
    if batch:
        if batch < 1 or batch > (len(modules) + 49) // 50:
            raise ValueError(f"batch {batch} is outside the listed modules")
        names = list(modules)[(batch - 1) * 50:batch * 50]
        modules = {name: modules[name] for name in names}
    return modules


def proof_module(module: str) -> str:
    paths = list(Path("ZesuSsz/Proofs").rglob(module))
    if len(paths) != 1:
        raise ValueError(f"expected one path for {module}; found {len(paths)}")
    return ".".join(paths[0].with_suffix("").parts)


def scratch_text(module: str, lemmas: list[str]) -> str:
    qualified_module = proof_module(module)
    lines = [f"Require Import {qualified_module}.", ""]
    for number, lemma in enumerate(lemmas):
        for command in (
            "Goal True.",
            f'  idtac "A6_BEGIN_{number:04d}".',
            "Abort.",
            f"Print Assumptions {qualified_module}.{lemma}.",
            "Goal True.",
            f'  idtac "A6_END_{number:04d}".',
            "Abort.",
            "",
        ):
            lines.append(command)
    return "\n".join(lines)


def normalize(lines: list[str]) -> list[str]:
    return [" ".join(ANSI.sub("", line).split()) for line in lines if line.strip()]


def parse_log(content: str, lemmas: list[str]) -> list[list[str]]:
    if len(SUCCESS.findall(content)) != 1:
        raise ValueError("scratch log lacks one successful exit line")
    result: list[list[str]] = []
    active: int | None = None
    body: list[str] = []
    for line in content.splitlines():
        marker = MARKER.fullmatch(ANSI.sub("", line).strip())
        if marker:
            kind, number_text = marker.groups()
            number = int(number_text)
            if number >= len(lemmas):
                raise ValueError(f"marker {number_text} exceeds lemma count")
            if kind == "BEGIN":
                if active is not None or number != len(result):
                    raise ValueError(f"unexpected begin marker {number_text}")
                active, body = number, []
            else:
                if active != number:
                    raise ValueError(f"unexpected end marker {number_text}")
                normalized = normalize(body)
                if not normalized:
                    raise ValueError(f"empty assumptions output for {lemmas[number]}")
                result.append(normalized)
                active = None
            continue
        if active is not None:
            body.append(line)
    if active is not None or len(result) != len(lemmas):
        raise ValueError(f"found {len(result)} outputs; expected {len(lemmas)}")
    return result


def generate(list_path: Path, batch: int, output_dir: Path) -> None:
    modules = selected_modules(list_path, batch)
    output_dir.mkdir(parents=True, exist_ok=True)
    for module, lemmas in modules.items():
        (output_dir / module).write_text(scratch_text(module, lemmas))
    print(f"generated {len(modules)} scratch files in {output_dir}")


def capture(list_path: Path, batch: int, log_dir: Path, output: Path) -> None:
    modules = selected_modules(list_path, batch)
    entries = []
    for module, lemmas in modules.items():
        log = log_dir / f"{Path(module).stem}.log"
        if not log.is_file():
            raise ValueError(f"missing scratch log: {log}")
        for lemma, assumptions in zip(lemmas, parse_log(log.read_text(), lemmas), strict=True):
            entries.append({"module": module, "lemma": lemma,
                            "assumptions": assumptions})
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps({"schema": 1, "batch": batch, "entries": entries},
                                 indent=2, sort_keys=True) + "\n")
    print(f"captured {len(entries)} lemmas from {len(modules)} scratch logs")


def compare(before: Path, after: Path) -> int:
    first = json.loads(before.read_text())
    second = json.loads(after.read_text())
    for data in (first, second):
        if data.get("schema") != 1 or not isinstance(data.get("entries"), list):
            raise ValueError("invalid assumption capture")
    if first.get("batch") != second.get("batch"):
        raise ValueError("assumption captures use different batches")
    old = {(row["module"], row["lemma"]): row["assumptions"]
           for row in first["entries"]}
    new = {(row["module"], row["lemma"]): row["assumptions"]
           for row in second["entries"]}
    if len(old) != len(first["entries"]) or len(new) != len(second["entries"]):
        raise ValueError("duplicate lemma in assumption capture")
    if old.keys() != new.keys():
        raise ValueError(f"capture keys changed: removed={old.keys() - new.keys()}, "
                         f"added={new.keys() - old.keys()}")
    changed = [key for key in old if old[key] != new[key]]
    for module, lemma in changed:
        print(f"CHANGED {module} {lemma}")
    print(f"assumptions: {len(old)} checked; {len(changed)} changed")
    return 1 if changed else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("generate", "capture"):
        command = commands.add_parser(name)
        command.add_argument("--list", type=Path, required=True)
        command.add_argument("--batch", type=int, default=0,
                             help="1-based 50-module batch; default is all modules")
        if name == "generate":
            command.add_argument("--output-dir", type=Path, required=True)
        else:
            command.add_argument("--log-dir", type=Path, required=True)
            command.add_argument("--output", type=Path, required=True)
    command = commands.add_parser("compare")
    command.add_argument("--before", type=Path, required=True)
    command.add_argument("--after", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "generate":
            generate(args.list, args.batch, args.output_dir)
        elif args.command == "capture":
            capture(args.list, args.batch, args.log_dir, args.output)
        else:
            return compare(args.before, args.after)
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
