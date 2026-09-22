"""The corpus file: one JSON record per probed proof."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

CORPUS = Path("ZesuSsz/Evidence/residuals/corpus.jsonl")
FIELDS = ["module", "lemma", "commit", "tier", "outcome", "seconds", "rss_mib",
          "zesu_run_seconds", "goal_count", "goal_heads", "goal_text",
          "goal_sha256", "label_lines", "label_class", "pred_class",
          "population", "label_classes", "pred_detail", "solver",
          "error_kind",
          "probe_variant", "error_lines"]


@dataclass(frozen=True)
class Key:
    module: str
    lemma: str
    commit: str


def read(path: Path = CORPUS) -> list[dict]:
    if not Path(path).exists():
        return []
    records = []
    for line in Path(path).read_text().split("\n"):
        if line.strip():
            records.append(json.loads(line))
    return records


def keys(records: list[dict]) -> set[Key]:
    return {Key(record["module"], record["lemma"], record["commit"])
            for record in records}


def order(record: dict) -> dict:
    """The record with the mandated fields first, in the mandated order."""
    ordered = {field: record[field] for field in FIELDS if field in record}
    ordered.update({key: value for key, value in record.items()
                    if key not in ordered})
    return ordered


def append(records: list[dict], path: Path = CORPUS) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with Path(path).open("a") as handle:
        for record in records:
            handle.write(json.dumps(order(record), sort_keys=False) + "\n")
