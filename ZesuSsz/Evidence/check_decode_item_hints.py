#!/usr/bin/env python3
"""Check each function's hint exports and declared scoped imports."""

import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
PREFIX = "ZesuSsz.Compliance."
UMBRELLA = "DecodeItemHints.v"
# These hints apply only at their declared consumers.
SCOPED_HINT_IMPORTS = {
    PREFIX + "DecodeItemExitDataFacts": (
        "ZesuSsz.Compliance.DecodeItemC1BMeaning",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d697c",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d698cLiteral",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d698cShortString",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d69b0",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d69e8",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a40",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a78",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6ae0",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6b08",
    ),
    PREFIX + "DecodeItemLoopDerivedFacts": (
        "ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a24",
        "ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ac4",
    ),
    PREFIX + "DecodeItemLoopInitialization": (
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a14",
        "ZesuSsz.Proofs.DecodeItem.Auto.Block800d6ab4",
        "ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a24",
        "ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ac4",
    ),
}


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


def hint_modules(directory: Path, umbrellas=(UMBRELLA,)) -> set[str]:
    excluded = {directory / path for path in umbrellas}
    return {
        PREFIX + ".".join(path.relative_to(directory).with_suffix("").parts)
        for path in directory.rglob("*.v")
        if path not in excluded and has_hint_registration(path.read_text())
    }


def required_modules(text: str, action: str) -> set[str]:
    modules = set()
    for command in source_commands(text):
        match = re.fullmatch(rf"\s*Require\s+{action}\s+([\w.\s]+)\s*", command)
        if match:
            modules.update(match[1].split())
        match = re.fullmatch(
            rf"\s*From\s+([\w.]+)\s+Require\s+{action}\s+([\w.\s]+)\s*", command
        )
        if match:
            modules.update(match[1] + "." + module for module in match[2].split())
    return modules


def exported_modules(text: str) -> set[str]:
    return required_modules(text, "Export")


def imported_modules(text: str) -> set[str]:
    return required_modules(text, "Import")


def missing_hint_modules(directory: Path) -> list[str]:
    return sorted(hint_modules(directory) - exported_modules((directory / UMBRELLA).read_text()))


def manifest_umbrellas(root: Path) -> list[tuple[Path, Path | None, set[str]]]:
    """Read the single Hints module listed in each registration category."""
    result = []
    for manifest in sorted((root / "ZesuSsz/Evidence").glob("*_function_text.json")):
        data = json.loads(manifest.read_text())
        inventory_only = data.get("inventory_only", False)
        if not isinstance(inventory_only, bool):
            raise ValueError(f"Invalid inventory_only flag in {manifest.name}.")
        registrations = data.get("registrations", [])
        if not isinstance(registrations, list) or any(not isinstance(path, str)
                                                      for path in registrations):
            raise ValueError(f"Invalid registrations in {manifest.name}.")
        umbrellas = [path for path in registrations if Path(path).name.endswith("Hints.v")]
        if len(umbrellas) != 1 and not (inventory_only and not umbrellas):
            raise ValueError(f"The manifest must list one hint umbrella: {manifest.name}.")
        listed = set()
        for category in ("contracts", "introductions", "exit_meanings", "loop_steps", "registrations"):
            paths = data.get(category, [])
            if not isinstance(paths, list) or any(not isinstance(path, str) for path in paths):
                raise ValueError(f"Invalid {category} in {manifest.name}.")
            listed.update(paths)
        compliance = root / "ZesuSsz/Compliance"
        owned = set()
        for name in listed:
            path = (root / name).resolve()
            if not path.is_relative_to(root.resolve()):
                raise ValueError(f"The manifest path leaves the workspace: {name}.")
            if path.is_relative_to(compliance.resolve()) and path.suffix == ".v":
                if not path.is_file():
                    raise ValueError(f"The listed Compliance source is missing: {name}.")
                if has_hint_registration(path.read_text()):
                    owned.add(PREFIX + ".".join(path.relative_to(compliance.resolve()).with_suffix("").parts))
        if inventory_only and not umbrellas:
            result.append((manifest, None, owned))
            continue
        umbrella = (root / umbrellas[0]).resolve()
        if not umbrella.is_relative_to(compliance.resolve()) or not umbrella.is_file():
            raise ValueError(f"The hint umbrella is not a Compliance source: {umbrellas[0]}.")
        own_name = PREFIX + ".".join(umbrella.relative_to(compliance.resolve()).with_suffix("").parts)
        owned.discard(own_name)
        result.append((manifest, umbrella, owned))
    if not result:
        raise ValueError("No function-text manifest declares a hint umbrella.")
    return result


def manifest_errors(root: Path) -> tuple[list[str], int]:
    """Check umbrella exports and the declared direct imports of scoped hints."""
    groups = manifest_umbrellas(root)
    directory = root / "ZesuSsz/Compliance"
    umbrellas = [path.relative_to(directory.resolve()) for _, path, _ in groups if path is not None]
    modules = hint_modules(directory, umbrellas)
    scoped = modules & SCOPED_HINT_IMPORTS.keys()
    covered, errors = set(scoped), []
    for manifest, umbrella, owned in groups:
        if umbrella is None:
            covered.update(owned)  # Inventory mode skips only missing umbrella coverage.
            continue
        exports = exported_modules(umbrella.read_text())
        covered.update(exports)
        for module in sorted(owned - exports - scoped):
            errors.append(f"{manifest.name}: {umbrella.name} does not export {module}.")
    for module in sorted(modules - covered):
        errors.append(f"No function hint umbrella exports {module}.")
    for module in sorted(scoped):
        for importer in SCOPED_HINT_IMPORTS[module]:
            path = root / (importer.replace(".", "/") + ".v")
            if not path.is_file():
                errors.append(f"Scoped hint importer is missing: {importer}.")
            elif module not in imported_modules(path.read_text()):
                errors.append(f"{importer} does not directly import {module}.")
    return errors, len(modules)


def main() -> int:
    try:
        errors, count = manifest_errors(ROOT)
    except (ValueError, OSError) as error:
        print(error)
        return 1
    for error in errors:
        print(error)
    if errors:
        return 1
    print(f"Umbrella exports and scoped imports cover all {count} Compliance hint modules.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
