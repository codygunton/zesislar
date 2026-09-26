#!/usr/bin/env python3
"""Classify every branch and worktree of the zesislar repo against a root commit.

For each local branch, each remote-only origin/* branch, and each worktree under
.worktrees/, report the commits ahead of and behind the root, the patch-unique
commits (`git cherry` `+` lines), a status, and the worktree state.

Status rules:
  merged      ahead == 0, or no `+` commit in `git cherry root tip`.
  superseded  every `+` commit subject appears in root history or in a merged branch.
  parked      unique commits, last commit on or after CUTOFF.
  stale       unique commits, last commit before CUTOFF.

Usage: branches.py --root <sha> --out <path>
Read-only: runs only git queries and `du`.
"""
import argparse
import os
import subprocess

REPO = "/home/cody/zesislar"
WT_DIR = os.path.join(REPO, ".worktrees")
CUTOFF = "2026-09-22"
MAIN = "origin/main"


def git(*args, cwd=REPO):
    out = subprocess.run(["git", "-C", cwd, *args], capture_output=True, text=True)
    return out.stdout.strip()


def lines(text):
    return [l for l in text.splitlines() if l]


def worktrees():
    """Map branch name -> worktree path, and list (path, head, branch) entries."""
    entries, cur = [], {}
    for line in git("worktree", "list", "--porcelain").splitlines() + [""]:
        if not line:
            if cur:
                entries.append(cur)
            cur = {}
        elif " " in line:
            key, val = line.split(" ", 1)
            cur[key] = val
        else:
            cur[line] = True
    return entries


def dirty(path):
    """Return (all porcelain lines, lines ignoring untracked _build)."""
    out = lines(git("status", "--porcelain", cwd=path))
    return len(out), len([l for l in out if not l.startswith("?? _build")])


def du_mib(path):
    out = subprocess.run(["du", "-s", "--block-size=1M", path], capture_output=True, text=True)
    return int(out.stdout.split()[0]) if out.stdout else 0


def collect_branches():
    """Return {name: {'local': sha|None, 'origin': sha|None}}."""
    refs = {}
    for line in lines(git("for-each-ref", "--format=%(refname) %(objectname)",
                          "refs/heads", "refs/remotes/origin")):
        ref, sha = line.split()
        if ref.startswith("refs/heads/"):
            refs.setdefault(ref[len("refs/heads/"):], {})["local"] = sha
        elif ref != "refs/remotes/origin/HEAD":
            refs.setdefault(ref[len("refs/remotes/origin/"):], {})["origin"] = sha
    return refs


def analyze(root, tip):
    ahead = int(git("rev-list", "--count", f"{root}..{tip}"))
    behind = int(git("rev-list", "--count", f"{tip}..{root}"))
    plus = [l.split()[1] for l in lines(git("cherry", root, tip)) if l.startswith("+")]
    date = git("log", "-1", "--format=%cs", tip)
    in_main = subprocess.run(["git", "-C", REPO, "merge-base", "--is-ancestor", tip, MAIN]).returncode == 0
    return {"ahead": ahead, "behind": behind, "plus": plus, "date": date, "in_main": in_main}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    root = git("rev-parse", a.root)

    wts = worktrees()
    wt_by_branch = {w["branch"][len("refs/heads/"):]: w["worktree"]
                    for w in wts if "branch" in w and w["worktree"].startswith(WT_DIR + "/")}
    refs = collect_branches()
    rows = {}
    for name, r in refs.items():
        tip = r.get("local") or r["origin"]
        rows[name] = dict(analyze(root, tip), tip=tip, **r)
        if r.get("local") and r.get("origin") and r["origin"] != r["local"]:
            # A diverged origin tip can hold its own unique commits; count both.
            extra = analyze(root, r["origin"])["plus"]
            rows[name]["plus"] += [c for c in extra if c not in rows[name]["plus"]]

    # Subjects available as evidence of supersession: root history + merged branches.
    subjects = set(lines(git("log", "--format=%s", root)))
    for row in rows.values():
        if not row["plus"]:
            for tip in {row.get("local"), row.get("origin")} - {None}:
                subjects.update(lines(git("log", "--format=%s", f"{root}..{tip}")))

    for name, row in rows.items():
        plus = row["plus"]
        subj = [git("log", "-1", "--format=%s", c) for c in plus]
        row["matched"] = sum(s in subjects for s in subj)
        if not plus:
            row["status"] = "merged"
        elif row["matched"] == len(plus):
            row["status"] = "superseded"
        elif row["date"] >= CUTOFF:
            row["status"] = "parked"
        else:
            row["status"] = "stale"
        row["unique"] = row["status"] in ("parked", "stale")
        wt = wt_by_branch.get(name)
        row["wt"] = wt
        row["dirty"], row["dirty_nobuild"] = dirty(wt) if wt else (0, 0)
        row["deletable"] = not row["unique"] and row["dirty"] == 0
        row["removable"] = bool(wt) and not row["unique"] and row["dirty_nobuild"] == 0
        row["mib"] = du_mib(wt) if wt else 0

    out = [f"# Branch and worktree debt against root `{root[:8]}`", "",
           f"Cutoff for parked vs stale: {CUTOFF}. `main` = tip is ancestor of {MAIN}.", "",
           "| branch | tip | ahead | behind | last commit | patch-unique | status | "
           "worktree | dirty | MiB | unique unmerged work |",
           "|---|---|---|---|---|---|---|---|---|---|---|"]
    for name in sorted(rows):
        r = rows[name]
        loc, org = r.get("local"), r.get("origin")
        tip = loc[:8] if loc else f"origin {org[:8]}"
        if loc and org and org != loc:
            tip += f" / origin {org[:8]}"
        status = r["status"] + (f" ({r['matched']}/{len(r['plus'])} subj)" if r["plus"] else "")
        status += " main" if r["in_main"] else ""
        wt = os.path.relpath(r["wt"], REPO) if r["wt"] else "none"
        out.append(f"| {name} | {tip} | {r['ahead']} | {r['behind']} | {r['date']} | "
                   f"{len(r['plus'])} | {status} | {wt} | {r['dirty']} | {r['mib'] or ''} | "
                   f"{'yes' if r['unique'] else 'no'} |")

    # Worktrees with no branch row (detached, or branch not under .worktrees rules).
    extra = [w for w in wts if w["worktree"].startswith(WT_DIR + "/")
             and "branch" not in w]
    for w in extra:
        n, _ = dirty(w["worktree"])
        out.append(f"| (detached) | {w.get('HEAD', '')[:8]} | | | | | detached | "
                   f"{os.path.relpath(w['worktree'], REPO)} | {n} | {du_mib(w['worktree'])} | ? |")

    dele = [n for n, r in rows.items() if r["deletable"]]
    remv = [n for n, r in rows.items() if r["removable"]]
    uniq = sorted(((len(r["plus"]) - r["matched"], len(r["plus"]), n) for n, r in rows.items()
                   if r["unique"]), reverse=True)
    by_status = {}
    for r in rows.values():
        by_status[r["status"]] = by_status.get(r["status"], 0) + 1
    out += ["", "## Summary", "",
            f"- Branches: {len(rows)}; by status: "
            + ", ".join(f"{k} {v}" for k, v in sorted(by_status.items())),
            f"- Branch tips that are ancestors of {MAIN}: {sum(r['in_main'] for r in rows.values())}",
            f"- Branches deletable: {len(dele)}",
            f"- Worktrees removable: {len(remv)} "
            f"({sum(rows[n]['mib'] for n in remv)} MiB reclaimable)",
            f"- Worktrees total: {len(wt_by_branch) + len(extra)} "
            f"({sum(r['mib'] for r in rows.values())} MiB)",
            f"- Removable worktrees: {', '.join(sorted(remv)) or 'none'}", "",
            "## Unique unmerged work (unmatched `+` commits / all `+` commits)", ""]
    out += [f"- {n}: {u} / {p} ({rows[n]['status']}, {rows[n]['date']})" for u, p, n in uniq]
    base = next((w for w in wts if w["worktree"] == REPO), {})
    out += ["", "## Base checkout", "",
            f"- {REPO}: branch {base.get('branch', 'detached')}, "
            f"HEAD {base.get('HEAD', '')[:8]}, dirty {dirty(REPO)[0]}"]
    with open(a.out, "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
