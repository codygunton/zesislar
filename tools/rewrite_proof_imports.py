#!/usr/bin/env python3
"""Rewrite Coq module paths after the Plan 0.5 proof move."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REWRITES = {
    "ZesuSsz.Experiments.ReadInput": "ZesuSsz.Proofs.ReadInput.ReadInput",
    "ZesuSsz.Experiments.AllocatorGet":
        "ZesuSsz.Proofs.AllocatorGet.AllocatorGet",
    "ZesuSsz.Experiments.WriteFailure":
        "ZesuSsz.Proofs.WriteFailure.WriteFailure",
    "ZesuSsz.Experiments.ZkvmExit": "ZesuSsz.Proofs.ZkvmExit.ZkvmExit",
    "ZesuSsz.Experiments.WriteSuccess":
        "ZesuSsz.Proofs.WriteSuccess.WriteSuccess",
}


def main() -> None:
    paths = list((ROOT / "ZesuSsz").rglob("*.v"))
    paths.extend((ROOT / "ZesuSsz").rglob("*.sh"))
    paths.extend((ROOT / "ZesuSsz").rglob("*.py"))
    paths.append(ROOT / "ZesuSsz" / "dune")
    changed = 0
    for path in paths:
        text = path.read_text()
        rewritten = text
        for old, new in REWRITES.items():
            rewritten = rewritten.replace(old, new)
        if rewritten != text:
            path.write_text(rewritten)
            changed += 1
    print(f"rewrote {changed} files")


if __name__ == "__main__":
    main()
