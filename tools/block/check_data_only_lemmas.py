"""Check the data-only modules listed in each function text manifest."""

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CATEGORIES = ("contracts", "introductions", "exit_meanings", "loop_steps",
              "registrations", "generator_json")
DATA_CATEGORIES = ("introductions", "exit_meanings", "loop_steps")
FORBIDDEN = re.compile(r"instr_body|instr_pre|WPasm|liAStep|zesu_block|zesu_liAStep")


def manifest_files(manifest: dict, root: Path) -> dict[str, list[Path]]:
    """Require file lists that stay inside the repository."""
    if not isinstance(manifest, dict) or not isinstance(manifest.get("function"), str) \
            or not manifest["function"].strip():
        raise ValueError("The manifest requires a nonempty function name.")
    files = {}
    for category in CATEGORIES:
        values = manifest.get(category)
        if not isinstance(values, list) or any(not isinstance(value, str) or not value
                                               for value in values):
            raise ValueError(f"The manifest requires a file list for {category}.")
        files[category] = []
        for value in values:
            relative = Path(value)
            path = root / relative
            if relative.is_absolute() or not path.resolve().is_relative_to(root.resolve()):
                raise ValueError(f"The listed file leaves the repository: {value}")
            if not path.is_file():
                raise ValueError(f"The listed file is missing: {value}")
            files[category].append(path)
    return files


def violations(root: Path) -> list[str]:
    errors = []
    for manifest in sorted((root / "ZesuSsz/Evidence").glob("*_function_text.json")):
        label = manifest.relative_to(root)
        try:
            files = manifest_files(json.loads(manifest.read_text()), root)
        except (ValueError, OSError) as error:
            errors.append(f"{label}: {error}")
            continue
        for category in DATA_CATEGORIES:
            for path in files[category]:
                for line, text in enumerate(path.read_text().splitlines(), 1):
                    for match in FORBIDDEN.finditer(text):
                        errors.append(f"{label}: {path.relative_to(root)}:{line}: "
                                      f"Forbidden data-lemma reference: {match.group()}")
    return errors


def main() -> int:
    errors = violations(ROOT)
    for error in errors:
        print(error)
    if errors:
        return 1
    count = len(list((ROOT / "ZesuSsz/Evidence").glob("*_function_text.json")))
    print(f"Data-only lemma checks passed for {count} function manifests.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
