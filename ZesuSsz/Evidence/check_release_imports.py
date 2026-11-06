#!/usr/bin/env python3
"""Check the final imports in release controls and callers."""

import argparse
from pathlib import Path
import re
import subprocess
import sys

from check_proof_hygiene import executable_text

ROOT = Path(__file__).resolve().parents[2]
ALL = "ZesuSsz.Automation.All"
IMPORT = re.compile(
    r"(?m)^\s*(?:From\s+(?P<prefix>[\w.]+)\s+)?"
    r"(?:Require(?:\s+(?:Import|Export))?|Import|Export)\s+"
    r"(?P<modules>[\w.\s]+?)\.(?=\s|$)"
)


def imports(source):
    """Return module names and command offsets. Ignore comments and strings."""
    for match in IMPORT.finditer(executable_text(source)):
        prefix = match.group("prefix")
        names = match.group("modules").split()
        if prefix:
            names = [prefix + "." + name for name in names]
        start = match.start() + len(match.group()) - len(match.group().lstrip())
        yield start, match.end(), names


def import_errors(source, umbrellas=(ALL,)):
    commands = list(imports(source))
    if not commands:
        return ["The file has no import command."]
    final = commands[-1]
    if final[2] in ([name] for name in umbrellas):
        return []
    line = source.count("\n", 0, final[0]) + 1
    return [f"line {line}: The final import must contain only an approved umbrella. "
            f"Found: {' '.join(final[2])}."]


def release_controls(root, base):
    """Include every evidence control and each test changed by this release."""
    files = set()
    for path in (root / "ZesuSsz/Evidence").glob("*.v"):
        if any(word in path.stem for word in ("Control", "Activation")):
            files.add(path)
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", base, "--", "ZesuSsz/Proofs/Tests", "tools/fixtures"],
        cwd=root, text=True,
    ).splitlines()
    changed += subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "--",
         "ZesuSsz/Proofs/Tests", "tools/fixtures"], cwd=root, text=True,
    ).splitlines()
    files.update(root / name for name in changed if name.endswith(".v"))
    return {path for path in files if path.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    parser.add_argument("--caller-dir", action="append", default=[], type=Path)
    parser.add_argument("--umbrella", action="append", default=[])
    parser.add_argument("--base", default="origin/main")
    args = parser.parse_args()
    files = release_controls(ROOT, args.base)
    files.update(args.paths)
    for directory in args.caller_dir:
        files.update(directory.rglob("*.v"))
    failures = []
    for path in sorted(files):
        for error in import_errors(path.read_text(), (ALL, *args.umbrella)):
            failures.append(f"{path}: {error}")
    for error in failures:
        print(error, file=sys.stderr)
    if not failures:
        print(f"Release import check passed: {len(files)} files.")
    return int(bool(failures))


if __name__ == "__main__":
    sys.exit(main())
