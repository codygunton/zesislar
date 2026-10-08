#!/usr/bin/env python3
"""Check that the decodeItem umbrella exports every Compliance hint module."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
PREFIX = "ZesuSsz.Compliance."
UMBRELLA = "DecodeItemHints.v"


def source_commands(text: str) -> list[str]:
    """Read commands without nested comments or quoted strings."""
    clean = []
    depth = 0
    quoted = False
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "(*":
                depth += 1
                index += 2
            elif pair == "*)":
                depth -= 1
                index += 2
            else:
                clean.append("\n" if char == "\n" else " ")
                index += 1
        elif quoted:
            if pair == '""':
                index += 2
            elif char == '"':
                quoted = False
                index += 1
            else:
                clean.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "(*":
            depth = 1
            clean.append(" ")
            index += 2
        elif char == '"':
            quoted = True
            clean.append(" ")
            index += 1
        else:
            clean.append(char)
            index += 1
    if depth or quoted:
        raise ValueError("The source has an unfinished comment or string.")
    return re.split(r"\.(?=\s|$)", "".join(clean))


def has_hint_registration(text: str) -> bool:
    for command in source_commands(text):
        attributes = re.findall(r"#\[([^]]*)\]", command)
        if any(re.search(r"\blocal\b", attribute) for attribute in attributes):
            continue
        head = re.sub(r"^\s*(?:#\[[^]]*\]\s*)*", "", command)
        if re.match(
            r"(?:Global\s+)?(?:Hint\b|(?:(?:Program|Existing|Declare)\s+)?Instances?\b)",
            head,
        ):
            return True
    return False


def hint_modules(directory: Path) -> set[str]:
    return {
        PREFIX + ".".join(path.relative_to(directory).with_suffix("").parts)
        for path in directory.rglob("*.v")
        if path != directory / UMBRELLA and has_hint_registration(path.read_text())
    }


def exported_modules(text: str) -> set[str]:
    modules = set()
    for command in source_commands(text):
        match = re.fullmatch(r"\s*Require\s+Export\s+([\w.\s]+)\s*", command)
        if match:
            modules.update(match[1].split())
        match = re.fullmatch(
            r"\s*From\s+([\w.]+)\s+Require\s+Export\s+([\w.\s]+)\s*", command
        )
        if match:
            modules.update(match[1] + "." + module for module in match[2].split())
    return modules


def missing_hint_modules(directory: Path) -> list[str]:
    return sorted(hint_modules(directory) - exported_modules((directory / UMBRELLA).read_text()))


def main() -> int:
    directory = ROOT / "ZesuSsz" / "Compliance"
    missing = missing_hint_modules(directory)
    for module in missing:
        print(f"The hint umbrella does not export {module}.")
    if missing:
        return 1
    print(f"The hint umbrella exports all {len(hint_modules(directory))} Compliance hint modules.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
