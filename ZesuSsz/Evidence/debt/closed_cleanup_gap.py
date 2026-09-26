#!/usr/bin/env python3
"""Explain which of the 217 closed hand proofs the A6 cleanup did not replace.

The residual corpus study found 217 hand proofs that `zesu_block.` alone
closes. The corpus with exactly those 217 `closed` records is
`ZesuSsz/Evidence/residuals/corpus.jsonl.gz` at commit 14c42a48 (branch
`residual-corpus`, CP-D). `closed_cleanup.txt` was generated from that
corpus. Phase A6 of PLAN_BUILDER_BUILDOUT replaced the listed bodies in four
batches.

For each of the 217 proofs this script checks the current tree:
the module exists, the lemma exists, and the body is the `zesu_block` form.
It gives a reason for each proof that was not replaced.
Standard library only. Run it from the repository root.
"""

from __future__ import annotations

import argparse
import collections
import gzip
import io
import json
import re
import subprocess
from pathlib import Path

CORPUS_PATH = "ZesuSsz/Evidence/residuals/corpus.jsonl.gz"
CORPUS_REF = "14c42a48"  # CP-D: 2,315 records, 217 closed
LATER_REF = "6d8ef58e"   # CP-F: the same corpus after replay, 223 closed
CLEANUP = Path("ZesuSsz/Evidence/residuals/closed_cleanup.txt")
SECONDS_CAP = 60.0       # tools/residual/closed_cleanup.py SECONDS_CAP
BATCHES = {              # A6 batch commits on the tip ancestry
    "131a9797": "A6 batch 1",
    "178336f8": "A6 batch 2",
    "e7166198": "A6 batch 3",
    "36ba510c": "A6 batch 4",
}
# Skip records for A6. BUILDOUT_REPORT.md records 66+56+60+16 = 198 lemmas
# with unchanged Print Assumptions and names no skip. Add entries here as
# (module, lemma): "evidence" if a skip record is found.
A6_SKIPS: dict[tuple[str, str], str] = {}

DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:Local |Global )?"
    r"(?:Lemma|Theorem|Corollary|Fact|Proposition|Remark)\s+")
PROOF_START = re.compile(r"(?m)^[ \t]*Proof(?:\s+using\s+[^.]*)?\.")
PROOF_END = re.compile(r"\b(?:Qed|Defined|Admitted|Abort)\.")
ZESU_FORM = re.compile(
    r"^Proof\. (?:move => \*\. |intros\. |iIntros\. )?zesu_block\. Qed\.$")


def git(*args: str) -> bytes:
    return subprocess.run(["git", *args], check=True,
                          capture_output=True).stdout


def load_corpus(ref: str) -> list[dict]:
    blob = git("cat-file", "blob", f"{ref}:{CORPUS_PATH}")
    with gzip.open(io.BytesIO(blob), "rt") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def load_cleanup(path: Path) -> dict[tuple[str, str], tuple[int, float, int]]:
    rows = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        module, lemma, hand, seconds = line.split()
        rows[module, lemma] = (int(hand), float(seconds), number)
    return rows


def normalize(text: str) -> str:
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    text = re.sub(r"\s+", " ", text).strip()
    return re.sub(r"=>\s*\*", "=> *", text)


def proof_body(source: str, lemma: str) -> tuple[str | None, str]:
    """Return (body, status). status is ok, missing, or a parse problem."""
    hits = [m for m in DECLARATION.finditer(source)
            if re.match(rf"{re.escape(lemma)}\b", source[m.end():])]
    if not hits:
        return None, "missing"
    if len(hits) > 1:
        return None, f"{len(hits)} declarations"
    decl = hits[0]
    following = DECLARATION.search(source, decl.end())
    limit = following.start() if following else len(source)
    start = PROOF_START.search(source, decl.end(), limit)
    if start is None:
        return None, "no Proof command"
    end = PROOF_END.search(source, start.end(), limit)
    if end is None:
        return None, "no proof end"
    return source[start.start():end.end()], "ok"


def batch_modules() -> dict[str, str]:
    touched = {}
    for commit, name in BATCHES.items():
        for path in git("show", "--name-only", "--format=", commit).decode().split():
            touched.setdefault(Path(path).name, f"{name} ({commit})")
    return touched


def find_module(root: Path, module: str) -> list[Path]:
    return sorted((root / "ZesuSsz").rglob(module))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--corpus-ref", default=CORPUS_REF)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    corpus = load_corpus(args.corpus_ref)
    closed = [r for r in corpus if r.get("outcome") == "closed"]
    keys = collections.Counter((r["module"], r["lemma"]) for r in closed)
    later = {(r["module"], r["lemma"]) for r in load_corpus(LATER_REF)
             if r.get("outcome") == "closed"}
    listed = load_cleanup(args.root / CLEANUP)
    touched = batch_modules()

    rows = []
    for rec in sorted(closed, key=lambda r: (r["module"], r["lemma"])):
        key = module, lemma = rec["module"], rec["lemma"]
        seconds = float(rec["seconds"])
        row = {"module": module, "lemma": lemma, "seconds": seconds,
               "tier": str(rec.get("tier")), "population": rec.get("population", ""),
               "listed": key in listed}
        paths = find_module(args.root, module)
        if not paths:
            row.update(state="module_deleted", evidence="no file under ZesuSsz/")
        elif len(paths) > 1:
            row.update(state="module_ambiguous",
                       evidence=", ".join(str(p) for p in paths))
        else:
            body, status = proof_body(paths[0].read_text(), lemma)
            if body is None:
                row.update(state="lemma_missing" if status == "missing"
                           else "lemma_unparsed",
                           evidence=f"{paths[0]}: {status}")
            elif ZESU_FORM.match(normalize(body)):
                row.update(state="replaced",
                           evidence=touched.get(module, "no A6 batch touched module"))
            else:
                lines = len([l for l in body.splitlines() if l.strip()])
                row.update(state="body_differs",
                           evidence=f"{paths[0].relative_to(args.root)}: "
                                    f"{lines}-line body")
        if row["state"] == "replaced":
            row["reason"] = "replaced"
        elif keys[key] > 1:
            row["reason"] = "duplicate corpus record"
        elif not row["listed"]:
            if seconds > SECONDS_CAP:
                row["reason"] = "not listed: probe over 60 s"
                row["evidence"] = (f"corpus {args.corpus_ref} seconds={seconds:.1f} > "
                                   f"SECONDS_CAP; {row['evidence']}")
            else:
                row["reason"] = f"not listed: {row['state']}"
        elif key in A6_SKIPS:
            row["reason"] = "listed, skipped in A6"
            row["evidence"] = A6_SKIPS[key]
        else:
            row["reason"] = f"listed, {row['state']}"
            row["evidence"] = (f"closed_cleanup.txt:{listed[key][2]}; "
                               f"{row['evidence']}")
        rows.append(row)

    extra_listed = sorted(set(listed) - set(keys))
    extra_later = sorted(later - set(keys))
    reasons = collections.Counter(r["reason"] for r in rows)
    states = collections.Counter(r["state"] for r in rows if r["reason"] != "replaced")
    tiers = collections.Counter(r["tier"] for r in rows if r["reason"] != "replaced")
    out = [
        "# Closed-proof cleanup gap",
        "",
        f"Source of the closed set: `{CORPUS_PATH}` at `{args.corpus_ref}` "
        f"({len(corpus)} records). Cleanup list: `{CLEANUP}` "
        f"({len(listed)} lemmas). Tree: `{args.root.resolve()}`.",
        "",
        "## Summary",
        "",
        f"- Closed proofs in corpus: {len(closed)} "
        f"({len(keys)} distinct module/lemma pairs)",
        f"- In closed_cleanup.txt: {sum(r['listed'] for r in rows)}",
        f"- Replaced by the zesu_block form at the tip: "
        f"{reasons['replaced']}",
        f"- Not replaced: {len(rows) - reasons['replaced']}",
        f"- Listed lemmas that are not in the closed set: {len(extra_listed)}",
        f"- A6 skip records found: {len(A6_SKIPS)} (BUILDOUT_REPORT.md: "
        "66+56+60+16 = 198 lemmas, Print Assumptions unchanged)",
        "",
        "## Reasons",
        "",
        "| reason | count |",
        "| --- | ---: |",
    ]
    out += [f"| {k} | {v} |" for k, v in reasons.most_common()]
    out += ["", f"Tip state of the not-replaced proofs: "
            + ", ".join(f"{k} {v}" for k, v in states.most_common())
            + ". Tiers: " + ", ".join(f"tier {k} {v}" for k, v in sorted(tiers.items()))
            + ".", "",
            "## Not-replaced proofs", "",
            "| module | lemma | tier | probe s | reason | evidence |",
            "| --- | --- | --- | ---: | --- | --- |"]
    for r in sorted((r for r in rows if r["reason"] != "replaced"),
                    key=lambda r: -r["seconds"]):
        out.append(f"| {r['module']} | {r['lemma']} | {r['tier']} | "
                   f"{r['seconds']:.1f} | {r['reason']} | {r['evidence']} |")
    if extra_listed:
        out += ["", "## Listed but not in the closed set", ""]
        out += [f"- {m} {l}" for m, l in extra_listed]
    if extra_later:
        out += ["", f"## Closed only in the later corpus `{LATER_REF}` "
                "(not part of the 217)", ""]
        for m, l in extra_later:
            paths = find_module(args.root, m)
            state = "module missing"
            if len(paths) == 1:
                body, status = proof_body(paths[0].read_text(), l)
                state = ("replaced" if body and ZESU_FORM.match(normalize(body))
                         else status if body is None else "hand proof")
            out.append(f"- {m} {l}: {state}")
    args.output.write_text("\n".join(out) + "\n")
    print("\n".join(out[:out.index("## Not-replaced proofs")]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
