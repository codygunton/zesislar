"""Check the approved umbrella against the reviewed native-pass switch list."""

import json
from pathlib import Path

from ZesuSsz.Evidence.check_decode_item_hints import exported_modules


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "ZesuSsz/Evidence/approved_automation_switches.json"
UMBRELLA = ROOT / "ZesuSsz/Automation/Approved.v"
PREFIX = "ZesuSsz.Automation.Switches."


def inventory_modules(manifest: dict) -> set[str]:
    modules = manifest["approved_modules"]
    if len(modules) != len(set(modules)):
        raise ValueError("The approved list contains duplicate modules.")
    if any(not module.startswith(PREFIX) for module in modules):
        raise ValueError("The approved list contains a non-switch module.")
    exclusions = {PREFIX + item["switch"] for item in manifest["exclusions"]}
    if exclusions.intersection(modules):
        raise ValueError("The approved list contains an excluded switch.")
    return set(modules)


def export_differences(text: str, manifest: dict) -> tuple[list[str], list[str]]:
    expected = inventory_modules(manifest)
    actual = exported_modules(text)
    return sorted(expected - actual), sorted(actual - expected)


def main() -> int:
    manifest = json.loads(MANIFEST.read_text())
    missing, extra = export_differences(UMBRELLA.read_text(), manifest)
    for module in missing:
        print(f"The approved umbrella does not export {module}.")
    for module in extra:
        print(f"The approved umbrella exports an unapproved module: {module}.")
    if missing or extra:
        return 1
    print(f"The approved umbrella exports all {len(inventory_modules(manifest))} switches.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
