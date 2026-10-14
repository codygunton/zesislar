"""Reject machine addresses and function identifiers in generic automation."""

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
FORBIDDEN = re.compile(
    r"0x800[0-9a-f]{5}|2148[0-9]{6}|"
    r"decodeItem|DecodeItem|parentHeader|nextUint64|alt_fl_alloc|memcpy"
)


def violations(root: Path) -> list[str]:
    """Scan complete source text, including comments and nested modules."""
    errors = []
    for path in sorted((root / "ZesuSsz/Automation").rglob("*.v")):
        for line, text in enumerate(path.read_text().splitlines(), 1):
            for match in FORBIDDEN.finditer(text):
                errors.append(f"{path.relative_to(root)}:{line}:{match.start() + 1}: "
                              f"Forbidden automation reference: {match.group()}")
    return errors


def main() -> int:
    errors = violations(ROOT)
    for error in errors:
        print(error)
    if errors:
        print(f"Generic automation contains {len(errors)} forbidden references.")
        return 1
    print("Generic automation contains no forbidden references.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
