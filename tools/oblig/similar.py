#!/usr/bin/env python3
"""Similar closed lemmas for a pure goal (model-free).

    similar.py index [--residuals DIR] [--runs RUN ...] --out INDEX.json
    similar.py query GOAL.v [--index INDEX.json | --residuals DIR] [--runs RUN ...]
                     [--k 3] [--max-bytes N]

The index holds every closed pure lemma: the residual modules ZesuSsz/Residuals/Block800d*.v
and <function>/Block*.v, the shared module DecodeItemBridges.v, and each goal closed later
(RUN/goals/<id>/ with STATUS.json result PASS and proof.v, the layout of
tools/block/residual_loop.py; sibling_runs() lists those of every region beside a run, so a lemma
closed in one region serves the same shape in another). Each lemma is keyed by the head of its
conclusion and the set of names its statement uses (qualified names and identifiers; binder
names, numerals and positive constructors excluded), and by the premise shapes its proof uses:
for each named premise `(H.. : P)` the proof names, the head of P with the head of its first
argument (`zesu_hist(fp_machineAt#_ForwardA0N0_Hist)`), short names, block offsets as `#`. A query
scores Jaccard similarity of the keys plus PREMISE_WEIGHT times the share of a lemma's used premise
shapes that the query's premises have (range 0 to 1 + PREMISE_WEIGHT), and returns the K best,
each with its statement and proof, as long as the text stays within --max-bytes. A lemma with the
query's own statement is never returned.
"""
import argparse
import hashlib
import json
import math
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/residuals"))
import render_residual_module as rrm  # noqa: E402

RESIDUALS = ROOT / "ZesuSsz/Residuals"
K = 3
PREMISE_WEIGHT = 0.5
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


NAMED_PREMISE = re.compile(r"^H[\w']*$")
BLOCK_OFFSET = re.compile(r"(?<=[A-Za-z_])[0-9a-f]{4}(?=_|$)")


def premises(statement):
    """[(name, type)] of the named premise binders `(H.. : P)` of a `forall` statement (nested
    exporter form included)."""
    out, text = [], statement.strip()
    while True:
        while text.startswith("(") and matching(text, 0) == len(text) - 1:
            text = text[1:-1].strip()
        if not text.startswith("forall"):
            return out
        comma = top_level_comma(text)
        if comma is None:
            return out
        binders, i = text[len("forall"):comma], 0
        while i < len(binders):
            if binders[i] != "(":
                i += 1
                continue
            j = matching(binders, i)
            if j is None:
                break
            group = binders[i + 1:j]
            colon = group.find(":")
            if colon > 0:
                names = group[:colon].split()
                if names and all(NAMED_PREMISE.match(n) for n in names):
                    out += [(n, group[colon + 1:].strip()) for n in names]
            i = j + 1
        text = text[comma + 1:].strip()


def short(name):
    """The last component of NAME with a block offset (4 hex digits, one a digit) written `#`."""
    return BLOCK_OFFSET.sub(lambda m: "#" if re.search(r"\d", m.group(0)) else m.group(0), name.rsplit(".", 1)[-1])


def shape(prop):
    """`head(first argument's head)` of a premise, short names, block offsets as `#`."""
    head = head_of(prop)
    text = prop.strip()
    while text.startswith("("):
        text = text[1:].lstrip()
    match = IDENT.match(text)
    if not match or match.group(1) != head:
        return short(head)
    rest = text[match.end():].lstrip()
    if rest.startswith("("):
        end = matching(rest, 0)
        inner = rest[1:end].strip() if end is not None else ""
        while inner.startswith("("):
            inner = inner[1:].lstrip()
        arg = IDENT.match(inner)
        if arg:
            return "%s(%s)" % (short(head), short(arg.group(1)))
    return short(head)


def premise_shapes(statement, proof=None):
    """The shapes of the named premises of STATEMENT; with PROOF, only those the proof names."""
    return sorted({shape(prop) for name, prop in premises(statement)
                   if proof is None or re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(name), proof)})


def entry(name, statement, proof, source):
    head, names = keys(statement)
    return dict(name=name, statement=statement, proof=proof, source=source, head=head, names=names,
                premises_used=premise_shapes(statement, proof),
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


def premise_bonus(query_shapes, used, weights):
    """The rarity of the premise shapes a lemma's proof uses that the query also has: the sum of their
    inverse document frequencies (WEIGHTS) over the index, divided by that of a shape used once and
    capped at 1 (0 when none is shared). A shape most proofs use (`and`, `le`) adds little; one only a
    few proofs use (a sealed history premise) adds the most."""
    top = max(weights.values(), default=0.0)
    if not top:
        return 0.0
    return min(1.0, sum(weights.get(s, top) for s in set(used or ()) & query_shapes) / top)


def shape_weights(entries):
    """{shape: log(N / number of entries whose proof uses it)} over the index entries, N = entries + 1."""
    counts = {}
    for e in entries:
        for s in set(e.get("premises_used") or ()):
            counts[s] = counts.get(s, 0) + 1
    total = len(entries) + 1
    return {s: math.log(total / n) for s, n in counts.items()}


def sibling_runs(run, depth=3):
    """The residual_loop run dirs (MANIFEST.json and goals/) of every region beside RUN: under the
    parent of RUN's region dir (`<aa>/<function>/<resid>/<block>` gives `<aa>`), at most DEPTH deep."""
    run = Path(run).resolve()
    for parent in [run] + list(run.parents):
        if (parent / "OBLIGATIONS.jsonl").is_file():
            root = parent.parent
            break
    else:
        return [run]
    found, base = [], len(root.parts)
    for directory, subdirs, files in os.walk(root):
        here = Path(directory)
        if "MANIFEST.json" in files and (here / "goals").is_dir():
            found.append(here)
        if len(here.parts) - base >= depth:
            subdirs[:] = []
        subdirs[:] = [d for d in subdirs if d not in ("goals", "_findlib", "leftover", "package", "checks")
                      and not d.startswith("bank")]
    return sorted(found)


def render(e):
    return "### %s\n\n```coq\nLemma %s :\n  %s.\nProof.\n%s\n```\n" % (e["name"], e["name"], e["statement"], e["proof"])


def nearest(index, statement, k=K, max_bytes=None):
    """The K nearest entries [(score, entry)] whose rendered text fits in MAX_BYTES together."""
    own = hashlib.sha256(statement.strip().encode()).hexdigest()
    head, names = keys(statement)
    query = key_set(head, names)
    shapes = set(premise_shapes(statement))
    weights = shape_weights(index["entries"])
    scored = sorted(((jaccard(query, key_set(e["head"], e["names"]))
                      + PREMISE_WEIGHT * premise_bonus(shapes, e.get("premises_used"), weights), e)
                     for e in index["entries"] if e["statement_sha256"] != own),
                    key=lambda pair: (-pair[0], pair[1]["name"]))
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
