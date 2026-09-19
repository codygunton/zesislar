#!/usr/bin/env python3
"""Re-read the stored message-probe logs, with no probe re-run.

The probe writes its whole output beside the goals, so a parser fix is an
offline change: read the logs again rather than paying for the probes.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from replay import BEGIN, END, parse_messages  # noqa: E402

MESSAGES = Path("ZesuSsz/Evidence/residuals/messages.jsonl")
LOGS = Path("_build/agents/corpus/residuals")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--messages", type=Path, default=MESSAGES)
    parser.add_argument("--logs", type=Path, default=LOGS)
    arguments = parser.parse_args()
    records = [json.loads(line) for line
               in arguments.messages.read_text().split("\n") if line.strip()]
    found = 0
    for record in records:
        stem = Path(record["module"]).stem + "__" + record["lemma"] + "__messages"
        log = arguments.logs / f"{stem}.log"
        if not log.exists():
            continue
        text = log.read_text()
        marked = text.split(BEGIN, 1)[-1].split(END, 1)[0]
        record["messages"] = parse_messages(marked)
        found += 1
    arguments.messages.write_text(
        "".join(json.dumps(record) + "\n" for record in records))
    print(f"reparsed {found} of {len(records)} logs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
