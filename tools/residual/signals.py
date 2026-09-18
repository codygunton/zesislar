"""Names the residual classes key on, read from the sources.

Class C3 covers goals whose head is a sealed definition. The sealed names are
the `Opaque` declarations of the proof tree, so this module reads them instead
of repeating a list that would go stale.
"""

from __future__ import annotations

import functools
import re
from pathlib import Path

OPAQUE = re.compile(r"(?m)^\s*(?:Global\s+|Local\s+)?Opaque\s+(?P<names>[^.]+)\.")
UNFOLD_LEMMA = re.compile(r"(?m)^\s*Lemma\s+(?P<name>\w+_unfold)\b")
PROOF_ROOT = Path("ZesuSsz")


@functools.lru_cache(maxsize=8)
def opaque_names(root: Path = PROOF_ROOT) -> frozenset[str]:
    """Every `Opaque` name under `root`."""
    names: set[str] = set()
    for source in sorted(Path(root).rglob("*.v")):
        for found in OPAQUE.finditer(source.read_text()):
            names.update(found.group("names").split())
    return frozenset(names)


@functools.lru_cache(maxsize=8)
def unfold_lemmas(root: Path = PROOF_ROOT) -> frozenset[str]:
    """Every `..._unfold` lemma under `root`."""
    names: set[str] = set()
    for source in sorted(Path(root).rglob("*.v")):
        for found in UNFOLD_LEMMA.finditer(source.read_text()):
            names.add(found.group("name"))
    return frozenset(names)


def opaque_pattern(root: Path = PROOF_ROOT) -> re.Pattern[str]:
    names = sorted(opaque_names(root), key=len, reverse=True)
    if not names:
        return re.compile(r"(?!x)x")
    return re.compile(r"\b(" + "|".join(re.escape(name) for name in names) + r")\b")
