"""Classify non-.v files under tools/, experiments/, ZesuSsz/Evidence/ by use.

For each file: line count, last commit date, references from the Makefile,
dune files, CI workflows, other scripts, and tests, and the last date that the
plans, progress logs, or post-reboot commit messages mention it.

Classes:
  live                          reachable from Makefile/dune/CI (transitively
                                through live scripts; Makefile `unittest
                                discover` makes matching tests entry points)
  referenced after 2026-09-10   no live reference, but a plan/log/commit
                                mention dated on or after the reboot
                                (a data file, i.e. not .py/.sh, committed on or
                                after the reboot also counts: a post-reboot run
                                produced it)
  unused since reboot           neither

Usage: script_refs.py --tree WT --base /home/cody/zesislar --out out.md
"""
import argparse, collections, datetime, glob, os, re, subprocess

REBOOT = "2026-09-10"
DIRS = ["tools", "experiments", "ZesuSsz/Evidence"]
SCRIPT_EXT = {".py", ".sh"}
DATE = re.compile(r"20\d\d-\d\d-\d\d")


def read(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def git(cwd, *args):
    return subprocess.run(["git", "-C", cwd, *args], capture_output=True,
                          text=True).stdout


def patterns(files):
    """Regex per file: rel path, or basename when unique, else parent/basename."""
    count = collections.Counter(os.path.basename(f) for f in files)
    pats = {}
    for f in files:
        base = os.path.basename(f)
        key = base if count[base] == 1 else "/".join(f.split("/")[-2:])
        alts = [re.escape(f), r"(?<![\w-])" + re.escape(key) + r"(?![\w-])"]
        pats[f] = re.compile("|".join(alts))
    return pats


def py_refs(text, stem):
    """Import of `stem` or a spec_from_file_location load by quoted stem."""
    imp = re.search(r"^\s*(from\s+%s\s+import|import\s+%s\b)" % (stem, stem),
                    text, re.M)
    dyn = ("spec_from_file_location" in text
           and re.search(r"""_load\(\s*["']%s["']""" % stem, text))
    return bool(imp or dyn)


def mention_dates(text, pat, fallback):
    """Nearest preceding date for each mention; return the max, or None."""
    dates = [(m.start(), m.group(0)) for m in DATE.finditer(text)]
    best = None
    for m in pat.finditer(text):
        prev = [d for p, d in dates if p < m.start()]
        d = prev[-1] if prev else fallback
        best = max(best or d, d)
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True)
    ap.add_argument("--base", default="/home/cody/zesislar")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    os.chdir(a.tree)
    files = sorted(f for d in DIRS for f in glob.glob(d + "/**/*", recursive=True)
                   if os.path.isfile(f) and not f.endswith(".v")
                   and "__pycache__" not in f and not f.startswith("ZesuSsz/Evidence/debt/"))
    pats = patterns(files)
    texts = {f: read(f) for f in files}
    make = read("Makefile")
    dunes = {d: read(d) for d in glob.glob("**/dune", recursive=True)
             if not d.startswith(("_build", ".worktrees"))}
    ci = {w: read(w) for w in glob.glob(".github/workflows/*")}
    ci_text = "\n".join(ci.values())

    def refs_in(text, f):
        stem, ext = os.path.splitext(os.path.basename(f))
        return bool(pats[f].search(text)) or (ext == ".py" and py_refs(text, stem))

    scripts = [f for f in files if os.path.splitext(f)[1] in SCRIPT_EXT]
    tests = {f for f in scripts if os.path.basename(f).startswith("test_")}
    by = {f: [s for s in scripts if s != f and refs_in(texts[s], f)] for f in files}
    entry = {f: [k for k, t in [("Makefile", make), ("dune", "\n".join(dunes.values())),
                                ("CI", ci_text)] if refs_in(t, f)] for f in files}
    # `unittest discover -s DIR -p 'test_*.py'` in Makefile or CI.
    for d, _ in re.findall(r"discover\s+-s\s+(\S+)\s+-p\s+'([^']+)'", make + ci_text):
        for t in tests:
            if os.path.dirname(t) == d and "Makefile" not in entry[t]:
                entry[t].append("Makefile")
    live = {f for f in files if entry[f]}
    todo = list(live)
    while todo:  # transitive closure: whatever a live script references is live
        s = todo.pop()
        for f in files:
            if f not in live and s in by[f]:
                live.add(f); todo.append(f)

    plans = glob.glob(a.base + "/docs/ai/plan/*.md") + glob.glob(a.base + "/docs/ai/plan/archive/*.md")
    # The sweep's own outputs name every file; they are not evidence of use.
    plans = [p for p in plans if not os.path.basename(p).startswith("TECH_DEBT_")]
    ptexts = {}
    for p in plans:
        m = DATE.search(os.path.basename(p))
        fb = m.group(0) if m else datetime.date.fromtimestamp(os.path.getmtime(p)).isoformat()
        ptexts[p] = (read(p), fb)
    commits = git(a.base, "log", "--all", "--since=" + REBOOT,
                  "--format=%x01%cs%x02%s%n%b").split("\x01")[1:]
    commits = [c.split("\x02", 1) for c in commits]

    rows = []
    for f in files:
        plan_d = max([d for t, fb in ptexts.values() if (d := mention_dates(t, pats[f], fb))] or [""])
        com_d = max([d for d, msg in commits if pats[f].search(msg)] or [""])
        script_refs = [s for s in by[f] if s not in tests]
        test_refs = [s for s in by[f] if s in tests]
        commit = git(".", "log", "-1", "--format=%cs", "--", f).strip()
        data_d = commit if os.path.splitext(f)[1] not in SCRIPT_EXT else ""
        if f in live:
            cls = "live"
        elif max(plan_d, com_d, data_d) >= REBOOT:
            cls = "referenced after 2026-09-10"
        else:
            cls = "unused since reboot"
        rows.append(dict(f=f, lines=len(texts[f].splitlines()),
                         commit=commit,
                         entry=",".join(entry[f]), scripts=script_refs, tests=test_refs,
                         plan=plan_d, msg=com_d, cls=cls))

    out = ["# Script and data references (tree %s)\n" % git(".", "rev-parse", "--short", "HEAD").strip(),
           "## Summary\n", "| dir | class | files | lines |", "|---|---|---|---|"]
    agg = collections.defaultdict(lambda: [0, 0])
    for r in rows:
        d = next(d for d in sorted(DIRS, key=len, reverse=True) if r["f"].startswith(d + "/"))
        for key in [(d, r["cls"]), ("ALL", r["cls"])]:
            agg[key][0] += 1; agg[key][1] += r["lines"]
    for (d, c), (n, l) in sorted(agg.items()):
        out.append("| %s | %s | %d | %d |" % (d, c, n, l))
    out += ["\n## Unused since reboot\n"]
    out += ["- `%s` (%d lines; commit %s; last plan %s)" % (r["f"], r["lines"], r["commit"], r["plan"] or "none")
            for r in rows if r["cls"] == "unused since reboot"]
    out += ["\n## All files\n",
            "| file | lines | last commit | entry | scripts | tests | last plan/log | last commit msg | class |",
            "|---|---|---|---|---|---|---|---|---|"]
    short = lambda xs: "<br>".join(os.path.relpath(x) for x in xs[:4]) + (" +%d" % (len(xs) - 4) if len(xs) > 4 else "")
    for r in rows:
        out.append("| `%s` | %d | %s | %s | %s | %s | %s | %s | %s |" % (
            r["f"], r["lines"], r["commit"], r["entry"], short(r["scripts"]),
            short(r["tests"]), r["plan"], r["msg"], r["cls"]))
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    with open(a.out, "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
