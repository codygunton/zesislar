#!/usr/bin/env python3
"""Definitions context for a pure goal (model-free; plan A3, A7 row `need_context`).

    defs.py show --goal GOAL.v --bank BANK [--ocamlpath DIR] [--out DIR] [--max-bytes N]

A goal names project predicates and constants (`decodeItemRejectedFacts`, `decodeItemC1BDomain`)
whose meaning a prover cannot see in the statement. This tool asks Rocq for them, with the goal's own
imports, through the stand-alone check route (one resource-guard scope per compile, falsify.Route):

1. `About` each candidate name (About never fails on an unknown name: it prints "not a defined
   object"). The answer gives the full path, the kind, the type and transparency.
2. `Print` each name that resolved to a transparent project constant or a project inductive.

A name is a *project* name when the first component of its full path is a logical root that the
bank binds with -Q/-R (ZesuSsz, ZesuStock, EvmSail..., IslaTraces, ...); the standard library,
stdpp, Iris and Islaris are library. Context items:
- a transparent project constant or a project inductive: its `Print` text (the body, one level:
  names inside the body are not expanded; a prover asks for them by name);
- an opaque project constant: its statement (the type of `About`), never its proof;
- any other name that resolves (library lemmas, `need_context` requests only): its statement.

Candidate names of a statement, ranked: the conclusion head, the other names of the conclusion in
order, the names of the premises that share a bound variable with the conclusion, then the names of
the remaining premises. Bound variables and keywords are never candidates. `section` keeps the
items in rank order that fit the byte budget (an item that does not fit is skipped, the next one is
tried), so the selection is deterministic for a given statement, imports and budget.

Answers are cached per directory in DEFS.json (keyed by the sha256 of the import header); a name
already answered is never compiled again.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
sys.path.insert(0, str(ROOT / "tools/bench"))
import residual_loop as rl  # noqa: E402
import similar  # noqa: E402
import bench_report  # noqa: E402

SCHEMA = "oblig-defs/1"
HEAD = "\n## Definitions of the names in the goal (Rocq `Print`; statements only for lemmas)\n\n"
ASKED_HEAD = "\n## Definitions and statements you asked for\n\n"
MARK = "@@D "
# A name `About` accepts: dot-separated components, each starting with a letter (`_` alone is a pattern).
QUALID = re.compile(r"^[A-Za-z][\w']*(?:\.[A-Za-z][\w']*)*$")
BINDER = re.compile(r"(?:\bforall\b|\bexists\b|\bfun\b|∀|∃|λ)\s*(.*?)(?:,|=>)", re.S)
KEYWORDS = similar.NOISE | frozenset("""Prop Set Type forall exists fun let in match with end return as
                                        if then else is fix cofix struct""".split())
# Words of `need_context` prose that look like code but name nothing: a name must have an underscore,
# a dot, a digit or an inner capital to be asked for.
CODE_LIKE = re.compile(r"[_.\d]|[a-z][A-Z]")
# Hypothesis names of the goal (H0, Hdom, HarrayFact8) and prose abbreviations name no global.
NOT_ASKED = re.compile(r"^(H[\w']*|i\.e|e\.g|[a-z]\d+)$")


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


# ---- candidate names ----

def bound_names(text):
    """Names bound in TEXT by forall / exists / fun (any depth)."""
    out = set()
    for match in BINDER.finditer(text):
        binders = match.group(1)
        groups = re.findall(r"\(\s*([\w'\s]+?)\s*:", binders)
        for group in groups:
            out |= set(group.split())
        if not groups:
            out |= set(binders.split(":")[0].split())
    return out


def parts(statement):
    """(premises, conclusion) of a statement: binders peeled, premises split at top-level arrows."""
    text, premises = statement, []
    while True:
        text = bench_report.unwrap(text)
        if text.startswith("forall ") or text.startswith("∀"):
            text = ",".join(bench_report.top_level(text, ",")[1:])
            continue
        pieces = bench_report.top_level(text.replace("→", "->"), "->")
        if len(pieces) > 1:
            premises += [p.strip() for p in pieces[:-1]]
            text = pieces[-1]
            continue
        return premises, text.strip()


def names_in(text, bound):
    """Global-looking names of TEXT in order of first occurrence (no bound variables, no keywords)."""
    out = []
    for name in similar.IDENT.findall(text):
        if name not in bound and name not in KEYWORDS and name not in out and not name[0].isdigit():
            out.append(name)
    return out


def ranked_names(statement):
    """Candidate names of STATEMENT in rank order (module docstring)."""
    bound = bound_names(statement)
    premises, conclusion = parts(statement)
    head = similar.head_of(conclusion, bound)
    order = [head] if QUALID.match(head or "") and head not in bound and head not in KEYWORDS else []
    variables = {v for v in bound if re.search(r"(?<![\w'.])%s(?![\w'])" % re.escape(v), conclusion)}
    sharing = [p for p in premises if any(re.search(r"(?<![\w'.])%s(?![\w'])" % re.escape(v), p) for v in variables)]
    rest = [p for p in premises if p not in sharing]
    for text in [conclusion] + sharing + rest:
        for name in names_in(text, bound):
            if name not in order:
                order.append(name)
    return order


def asked_names(needs, exclude=()):
    """Names a `need_context` answer gives: code-like qualified identifiers of its prose (backticks or
    bare), in order, minus EXCLUDE."""
    text = " ".join(needs)
    out = []
    for name in similar.IDENT.findall(text):
        name = name.rstrip(".")
        if (QUALID.match(name) and CODE_LIKE.search(name) and not NOT_ASKED.match(name) and name not in KEYWORDS
                and name not in exclude and name not in out):
            out.append(name)
    return out


# ---- Rocq queries ----

def project_roots(args):
    """Logical roots bound with -Q / -R in the bank's coqc arguments."""
    roots = set()
    for i, arg in enumerate(args):
        if arg in ("-Q", "-R") and i + 2 < len(args):
            roots.add(args[i + 2].split(".")[0])
    return roots


def about_text(header, names):
    lines = list(header) + ["Set Printing Width 100."]
    for name in names:
        lines.append('Goal True. idtac "%sabout %s". Abort.' % (MARK, name))
        lines.append("About %s." % name)
    lines.append('Goal True. idtac "%send". Abort.' % MARK)
    return "\n".join(lines) + "\n"


def print_text(header, names):
    lines = list(header) + ["Set Printing Width 100."]
    for name in names:
        lines.append('Goal True. idtac "%sprint %s". Abort.' % (MARK, name))
        lines.append("Print %s." % name)
    lines.append('Goal True. idtac "%send". Abort.' % MARK)
    return "\n".join(lines) + "\n"


def blocks(log_text, kind):
    """{name: text} of the `@@D <kind> <name>` sections of a compile log (time stamps removed)."""
    out, current = {}, None
    for raw in log_text.split("\n"):
        line = rl.STAMP.sub(r"\2", raw)
        if line.startswith(MARK):
            words = line[len(MARK):].split()
            current = words[1] if len(words) == 2 and words[0] == kind else None
            if current is not None:
                out[current] = []
            continue
        if current is not None and not line.startswith("@@CPU"):
            out[current].append(line)
    return {k: "\n".join(v).strip() for k, v in out.items()}


END = re.compile(r"^(?:\d+\.\d+ )?%send$" % MARK, re.M)
EXPANDS = re.compile(r"Expands to:\s+(Constant|Inductive|Constructor|Notation|Module|Ltac|Syntactic constant)\s+(\S+)")


def parse_about(name, text):
    """The record of one `About` answer: status resolved/unresolved, full path, kind, transparency, type."""
    flat = " ".join(text.split())
    if not text or "not a defined object" in text or "No object of basename" in text:
        return dict(status="unresolved")
    match = EXPANDS.search(flat)
    if match is None:
        return dict(status="unresolved")
    kind, full = match.group(1).lower(), match.group(2)
    typ = text.split("\n\n")[0].strip()
    if kind not in ("constant", "inductive", "constructor") or " : " not in typ.replace("\n", " ") + " ":
        return dict(status="unresolved", kind=kind, full=full)
    opaque = "is opaque" in flat
    return dict(status="resolved", kind=kind, full=full, opaque=opaque, type=typ)


def route_compile(route):
    """COMPILE for a Resolver: the stand-alone check route of falsify.Route (one resource-guard scope per
    compile) booking 1 GiB, the claim of residual_loop.py's checks (measured peak of a query: 0.8 GiB)."""
    if route.direct:
        return route.compile

    def compile(path, tag):
        result = rl.scoped(path, tag, route.args, route.ocamlpath, claim=rl.CHECK_CLAIM)
        return result, Path(result["log"]).read_text(errors="replace")
    return compile


class Resolver:
    """Rocq answers for the names of one goal (header), cached in DIR/DEFS.json. COMPILE(path, tag)
    returns (result dict, log text) (falsify.Route.compile); ROOTS are the project's logical roots (or a
    function that returns them, called on the first compile)."""

    def __init__(self, directory, header, compile, roots, tag="defs"):
        self.dir = Path(directory)
        self.header = list(header)
        self.compile = compile
        self._roots = roots
        self.tag = tag
        self.path = self.dir / "DEFS.json"
        data = rl.read_json(self.path, {}) if self.path.exists() else {}
        key = sha("\n".join(self.header))
        self.data = data if data.get("header_sha256") == key else dict(schema=SCHEMA, header_sha256=key, names={})

    def project(self, record):
        if callable(self._roots):
            self._roots = self._roots()
        return record.get("full", "").split(".")[0] in set(self._roots)

    def resolve(self, names):
        """{name: record} for NAMES; compiles only the names not yet in the cache."""
        names = [n for n in names if QUALID.match(n)]
        known = self.data["names"]
        missing = [n for n in names if n not in known]
        if missing:
            self.dir.mkdir(parents=True, exist_ok=True)
            fresh, todo = {}, list(missing)
            while todo:
                path = self.dir / ("about_%s.v" % sha("\n".join(todo))[:12])
                path.write_text(about_text(self.header, todo))
                result, text = self.compile(path, "%s-about" % self.tag)
                found = blocks(text, "about")
                if result.get("returncode") == 0 and END.search(text):
                    fresh.update({n: parse_about(n, found.get(n, "")) for n in todo})
                    break
                # The query stops at the first name About rejects (a keyword, a tactic notation): keep the
                # answers before it, mark it unresolved, and ask again for the rest.
                opened = [n for n in todo if n in found]
                if not opened:
                    raise DefsError("About query failed (%s): %s" % (path, rl.errors_of(text, limit=8)))
                bad = opened[-1]
                fresh.update({n: parse_about(n, found[n]) for n in opened[:-1]})
                fresh[bad] = dict(status="unresolved", error="About rejected the name")
                todo = todo[todo.index(bad) + 1:]
            for record in fresh.values():
                if record["status"] == "resolved":
                    record["project"] = self.project(record)
            wanted = [n for n, r in fresh.items() if r["status"] == "resolved" and r["project"]
                      and (r["kind"] == "inductive" or (r["kind"] == "constant" and not r["opaque"]))]
            if wanted:
                path = self.dir / ("print_%s.v" % sha("\n".join(wanted))[:12])
                path.write_text(print_text(self.header, wanted))
                result, text = self.compile(path, "%s-print" % self.tag)
                if result.get("returncode") != 0:
                    raise DefsError("Print query failed (%s): %s" % (path, rl.errors_of(text, limit=8)))
                printed = blocks(text, "print")
                for n in wanted:
                    fresh[n]["body"] = printed.get(n, "")
            known.update(fresh)
            rl.write_json(self.path, self.data)
        return {n: known[n] for n in names}


class DefsError(RuntimeError):
    pass


# ---- rendering ----

# The body `Print` shows for a record field: `f = λ d : R, let (_, .., f, ..) := d in f`.
FIELD = re.compile(r"=\s*λ\s*\w+\s*:\s*(\S+),\s*let\s*\(", re.S)


def item_text(name, record):
    """The context text of one resolved name: its definition, or its statement for a lemma (a record
    field: its type and record, since its body is a pattern match)."""
    full = record.get("full", name)
    body = record.get("body") or ""
    field = FIELD.search(body)
    if field:
        return "### %s (`%s`, field of record `%s`)\n\n```coq\n%s\n```\n" % (name, full, field.group(1), record["type"])
    if body:
        return "### %s (`%s`)\n\n```coq\n%s\n```\n" % (name, full, body)
    label = "statement" if record.get("kind") == "constant" else record.get("kind", "")
    return "### %s (`%s`, %s)\n\n```coq\n%s\n```\n" % (name, full, label, record["type"])


def items(records, names, project_only=True, exclude=()):
    """[(name, text)] of NAMES in order: resolved names (project names only when PROJECT_ONLY), one per
    full path, minus EXCLUDE (names, full paths or their last component)."""
    out, seen = [], set()
    for name in names:
        record = records.get(name) or {}
        if record.get("status") != "resolved" or (project_only and not record.get("project")):
            continue
        full = record["full"]
        if name in exclude or full in exclude or full.rsplit(".", 1)[-1] in exclude or full in seen:
            continue
        seen.add(full)
        out.append((name, item_text(name, record)))
    return out


def section(found, max_bytes, head=HEAD):
    """HEAD plus the items in order that fit MAX_BYTES (each skipped item lets the next be tried);
    (text, used names). Empty text when no item fits."""
    text, used = head, []
    for name, item in found:
        if len((text + item + "\n").encode()) <= max_bytes:
            text += item + "\n"
            used.append(name)
    return (text, used) if used else ("", [])


def needs_text(needs, goal_dir, max_bytes):
    """The section for the names a `need_context` answer (NEEDS: list of prose items) gives, for a
    residual_loop goal dir (goal.v; MANIFEST.json two levels up names the bank): the definition or
    statement of each name Rocq resolves with the goal's imports, in order, within MAX_BYTES. "" when
    nothing resolves or fits. Answers are cached in GOAL_DIR/defs/."""
    import falsify
    goal_dir = Path(goal_dir)
    goal_v = (goal_dir / "goal.v").read_text()
    head = rl.goal_head(goal_v)
    header = head[:head.index("\nLemma ")].strip("\n").split("\n")
    names = asked_names(needs, bound_names(similar.goal_statement(goal_dir / "goal.v")))
    if not names:
        return ""
    manifest = rl.read_json(goal_dir.parents[1] / "MANIFEST.json")
    route = falsify.Route(manifest["bank"])
    resolver = Resolver(goal_dir / "defs", header, route_compile(route), project_roots(route.args),
                        tag="defs-" + goal_dir.name)
    text, _ = section(items(resolver.resolve(names), names, project_only=False), max_bytes, head=ASKED_HEAD)
    return text


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    s = sub.add_parser("show")
    s.add_argument("--goal", required=True)
    s.add_argument("--bank", required=True)
    s.add_argument("--ocamlpath")
    s.add_argument("--out", help="cache dir (default: defs/ beside the goal)")
    s.add_argument("--max-bytes", type=int, default=6000)
    a = ap.parse_args(argv)
    import falsify
    import package
    goal_v = Path(a.goal).read_text()
    statement = similar.goal_statement(a.goal)
    route = falsify.Route(a.bank, a.ocamlpath)
    resolver = Resolver(a.out or Path(a.goal).parent / "defs", package.goal_header(goal_v), route_compile(route),
                        project_roots(route.args), tag="defs-" + Path(a.goal).parent.name)
    names = ranked_names(statement)
    text, used = section(items(resolver.resolve(names), names), a.max_bytes)
    print(text, end="")
    print("DEFS names=%d shown=%s" % (len(names), ",".join(used) or "-"), file=sys.stderr)


if __name__ == "__main__":
    main()
