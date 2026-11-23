#!/usr/bin/env python3
"""Similar closed lemmas for a pure goal (model-free).

    similar.py index [--residuals DIR] [--runs RUN ...] --out INDEX.json
    similar.py query GOAL.v [--index INDEX.json | --residuals DIR] [--runs RUN ...]
                     [--k 3] [--max-bytes N]

The index holds every closed pure lemma: the residual modules ZesuSsz/Residuals/Block800d*.v
and <function>/Block*.v, the shared module DecodeItemBridges.v, and each goal closed later
(RUN/goals/<id>/ with STATUS.json result PASS and proof.v, the layout of
tools/block/residual_loop.py). Each lemma is keyed by the head of its conclusion and the set
of names its statement uses (qualified names and identifiers; binder names, numerals and
positive constructors excluded). A query returns the K nearest by Jaccard similarity of
those keys, each with its statement and proof, as long as the text stays within
--max-bytes. A lemma with the query's own statement is never returned.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/residuals"))
import render_residual_module as rrm  # noqa: E402

RESIDUALS = ROOT / "ZesuSsz/Residuals"
K = 3
IDENT = re.compile(r"(?<![\w'])@?([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)")
NOISE = frozenset("""forall exists fun let in match with end return as if then else Type Prop Set
                     xO xI xH Zpos Zneg Npos Z0 N0 O S true false""".split())
LEMMA_TEXT = re.compile(r"^Lemma (?P<name>\S+) :\n(?P<stmt>.*?)\.\nProof\.\n(?P<proof>.*?Qed\.)", re.S | re.M)


def split_binders(statement):
    """(binder names, conclusion) of `forall (x : T) ..., C` or nested `(forall (x : T), ...)` text."""
    names, text = [], statement.strip()
    while True:
        while text.startswith("(") and matching(text, 0) == len(text) - 1:
            text = text[1:-1].strip()
        if not text.startswith("forall"):
            return names, text
        comma = top_level_comma(text)
        if comma is None:
            return names, text
        binders = text[len("forall"):comma]
        for group in re.findall(r"\(\s*([\w'\s]+?)\s*:", binders):
            names += group.split()
        if "(" not in binders:
            names += binders.split(":")[0].split()
        text = text[comma + 1:].strip()


def matching(text, i):
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    return None


def top_level_comma(text):
    depth = 0
    for j, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            return j
    return None


INFIX = re.compile(r"\s(<=|<>|>=|<|>|=|≤|≥|≠|/\\|\\/|<->|∧|∨)\s")


def top_level(text, pattern):
    """Matches of PATTERN in TEXT outside parentheses."""
    out, depth = [], 0
    for j, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and ch.isspace():
            match = pattern.match(text, j)
            if match:
                out.append(match)
    return out


LET_IN = re.compile(r"\sin\s")
ARROW = re.compile(r"\s(->|→)\s")


def head_of(conclusion, binders=()):
    """The head symbol of a conclusion: past `let ... in` and premises `A -> ...`, the
    infix operator of an infix form, else the first applied name."""
    text = conclusion.strip()
    while True:
        while text.startswith("(") and matching(text, 0) == len(text) - 1:
            text = text[1:-1].strip()
        cuts = top_level(text, LET_IN) if text.startswith("let") else top_level(text, ARROW)
        if not cuts:
            break
        text = text[cuts[-1].end():].strip()
    infix = top_level(text, INFIX)
    if infix:
        return infix[0].group(1)
    while text.startswith("("):
        text = text[1:].lstrip()
    match = IDENT.match(text)
    if match and match.group(1) not in binders:
        return match.group(1)
    operator = re.match(r"\S+", text)
    return operator.group(0) if operator else ""


def keys(statement):
    names, conclusion = split_binders(statement)
    binders = set(names)
    used = {m for m in IDENT.findall(statement) if m not in binders and m not in NOISE}
    return head_of(conclusion, binders), sorted(used)


def entry(name, statement, proof, source):
    head, names = keys(statement)
    return dict(name=name, statement=statement, proof=proof, source=source, head=head, names=names,
                statement_sha256=hashlib.sha256(statement.encode()).hexdigest())


def module_entries(path):
    text = Path(path).read_text()
    out = []
    for match in LEMMA_TEXT.finditer(text):
        out.append(entry(match["name"], match["stmt"].strip(), match["proof"].strip(), str(path)))
    return out


def residual_files(residuals):
    residuals = Path(residuals)
    files = sorted(residuals.glob("Block800d*.v")) + sorted(residuals.glob("*/Block*.v"))
    files += [residuals / ("%s.v" % name) for name in sorted(rrm.SHARED) if (residuals / ("%s.v" % name)).exists()]
    return files


def run_entries(run):
    out = []
    for status in sorted(Path(run).glob("goals/*/STATUS.json")):
        d = status.parent
        try:
            if json.loads(status.read_text()).get("result") != "PASS" or not (d / "proof.v").exists():
                continue
        except json.JSONDecodeError:
            continue
        match = LEMMA_TEXT.search((d / "proof.v").read_text())
        if match:
            out.append(entry(match["name"], match["stmt"].strip(), match["proof"].strip(), str(d)))
    return out


def build_index(residuals=RESIDUALS, runs=()):
    entries, seen = [], set()
    for path in residual_files(residuals):
        for e in module_entries(path):
            if e["statement_sha256"] not in seen:
                seen.add(e["statement_sha256"])
                entries.append(e)
    for run in runs:
        for e in run_entries(run):
            if e["statement_sha256"] not in seen:
                seen.add(e["statement_sha256"])
                entries.append(e)
    return dict(schema="oblig-similar/1", entries=entries)


def key_set(head, names):
    return {"head:" + head} | set(names)


def jaccard(a, b):
    return len(a & b) / len(a | b) if a | b else 0.0


def render(e):
    return "### %s\n\n```coq\nLemma %s :\n  %s.\nProof.\n%s\n```\n" % (e["name"], e["name"], e["statement"], e["proof"])


def nearest(index, statement, k=K, max_bytes=None):
    """The K nearest entries [(score, entry)] whose rendered text fits in MAX_BYTES together."""
    own = hashlib.sha256(statement.strip().encode()).hexdigest()
    head, names = keys(statement)
    query = key_set(head, names)
    scored = sorted(((jaccard(query, key_set(e["head"], e["names"])), e) for e in index["entries"]
                     if e["statement_sha256"] != own), key=lambda pair: (-pair[0], pair[1]["name"]))
    out, used = [], 0
    for score, e in scored:
        if len(out) == k or score == 0.0:
            break
        size = len(render(e).encode())
        if max_bytes is not None and used + size > max_bytes:
            continue
        out.append((score, e))
        used += size
    return out


def goal_statement(path):
    text = Path(path).read_text()
    match = re.search(r"^Lemma \S+ :\n(?P<stmt>.*?)\.\nProof\.", text, re.S | re.M) or \
        re.search(r"^Goal (?P<stmt>.*)\.\s*$", text, re.S | re.M)
    if not match:
        raise SystemExit("similar: %s holds neither a Lemma nor a Goal." % path)
    return match["stmt"].strip()


def section(found):
    if not found:
        return ""
    return "## Similar closed lemmas\n\n" + "\n".join(
        "Similarity %.2f.\n\n%s" % (score, render(e)) for score, e in found)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    i = sub.add_parser("index")
    i.add_argument("--residuals", default=str(RESIDUALS))
    i.add_argument("--runs", nargs="*", default=[])
    i.add_argument("--out", required=True)
    q = sub.add_parser("query")
    q.add_argument("goal")
    q.add_argument("--index")
    q.add_argument("--residuals", default=str(RESIDUALS))
    q.add_argument("--runs", nargs="*", default=[])
    q.add_argument("--k", type=int, default=K)
    q.add_argument("--max-bytes", type=int)
    a = ap.parse_args(argv)
    if a.command == "index":
        index = build_index(a.residuals, a.runs)
        Path(a.out).write_text(json.dumps(index, indent=1, sort_keys=True) + "\n")
        print("indexed %d lemma(s) in %s" % (len(index["entries"]), a.out))
        return
    index = json.loads(Path(a.index).read_text()) if a.index else build_index(a.residuals, a.runs)
    print(section(nearest(index, goal_statement(a.goal), a.k, a.max_bytes)), end="")


if __name__ == "__main__":
    main()
