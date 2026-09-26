"""Render TECH_DEBT_INVENTORY.md from the sweep's JSON and the three reports.

  --modules   inventory.py output     --answers  answers.py output
  --branches  branches.py output      --scripts  script_refs.py output
  --closed    closed_cleanup_gap.py output
"""

import argparse
import json
import re
from pathlib import Path

ROOT_LETTERS = {"contract": "C", "main": "M", "shell": "S", "adequacy": "A", "phase_c": "P"}


def short(path):
    return path.replace("ZesuSsz/Proofs/WriteSuccess/", "WS/").replace("ZesuSsz/", "")


def hours(seconds):
    return f"{seconds:,.0f} s ({seconds / 3600:.1f} h)"


def num(t):
    return (f"{t['modules']:,} modules, {t['lines']:,} lines, {t['proofs']:,} proofs, "
            f"{t['hand_lines']:,} hand lines, {t['gate_seconds']:,.0f} gate module-seconds ({t['gate_seconds'] / 3600:.1f} h)")


def section(md, title):
    """The body of `## title` in a Markdown report, without the heading."""
    m = re.search(rf"^## {re.escape(title)}\n(.*?)(?=^## |\Z)", md, re.S | re.M)
    return m.group(1).strip() if m else ""


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("modules", "answers", "branches", "scripts", "closed", "out"):
        p.add_argument(f"--{name}", required=True)
    p.add_argument("--sha", required=True)
    a = p.parse_args()
    R = json.loads(Path(a.modules).read_text())
    A = json.loads(Path(a.answers).read_text())
    branches = Path(a.branches).read_text()
    scripts = Path(a.scripts).read_text()
    closed = Path(a.closed).read_text()
    q1, q2, q3 = A["q1"], A["q2"], A["q3"]
    out = []
    w = out.append

    w("# Tech-debt inventory\n")
    w(f"Root: `origin/islaris-native` at `{a.sha}`, read 2026-09-26. "
      "Plan: `PLAN_TECH_DEBT_SWEEP.md`. Scripts: `ZesuSsz/Evidence/debt/` on branch "
      "`debt-sweep`; `README.md` there gives the commands.\n")
    w("## Method and limits\n")
    w("- Imports come from `coqdep -Q ZesuSsz ZesuSsz` over every `.v` file of the "
      "theory, which is the dependency pass that Dune runs. Text search only cross-checks it.")
    w("- A module is reachable when a root imports it, directly or transitively. The "
      "roots are `Contract.v` (C), `Proofs/Main/Main.v` (M), `Compliance/Shell.v` (S), "
      "`Export/Adequacy.v` (A) and each of the 102 `Proofs/Tests/*` files and "
      "`Tests/IslarisInfrastructure.v`.")
    w("- I added one root that the plan does not name: Phase C (P). It holds the four merged "
      "segment lemmas and the modules that `tools/det` reads as chain inputs "
      "(`open_segments.json`, `chain/*.json`: `like` and `imports`). `Contract.v` still "
      "assumes the tail at `0x15668`, so no listed root imports the merged segments. "
      f"Without P, {q1['without_phase_c_root']['modules']} modules are unreachable, "
      f"not {q1['unreachable']['modules']}.")
    w("- Build cost is the latest successful `coqc` run of each module in the Dune "
      "`trace.csexp` files of all worktrees since 2026-09-20. The gate logs carry no "
      "per-module time. Most latest runs come from 24- to 48-job builds, so the times "
      "include contention. For example, `CarrierChunk14f6cRaw` took 503 CPU s in the "
      "48-job arm build and 161 CPU s alone (BUILDOUT_REPORT). The sums are module-seconds "
      "of work, not wall time: at 24 jobs, the gate wall time is about 1/24 of the sum. "
      f"{len(A['no_cost'])} modules have no record.")
    w("- \"Hand lines\" uses the parser of the hygiene gate (`tools/residual/modules.py`).")
    w("- \"Superseded by\" has two sources. A merged segment's `[entry, exit)` range "
      "supersedes a module whose lemma conclusion `instr_body` lies in that range. For an "
      "unreachable module, a reachable module that proves `instr_body` at the same entry "
      "also supersedes it.")
    w("- Class rules, in order:")
    w("  1. **remove now**: excluded from the Dune theory, or unreachable and not a "
      "benchmark or plan input.")
    w("  2. **remove after CP3**: unreachable but in a frozen benchmark set, or a "
      "reachable per-chunk proof inside a merged segment's range.")
    w("  3. **debt, keep**: reachable on the legacy rule set, over the module limits, "
      "or unreachable but named in an active plan (or an endpoint umbrella).")
    w("  4. **live**: all other modules.\n")

    w("## Summary\n")
    w("| class | modules | lines | proofs | hand lines | gate module-seconds |")
    w("|---|---:|---:|---:|---:|---:|")
    for cls, t in A["classes"].items():
        w(f"| {cls} | {t['modules']:,} | {t['lines']:,} | {t['proofs']:,} | "
          f"{t['hand_lines']:,} | {t['gate_seconds']:,.0f} |")
    t = A["all"]
    w(f"| **all** | {t['modules']:,} | {t['lines']:,} | {t['proofs']:,} | "
      f"{t['hand_lines']:,} | {t['gate_seconds']:,.0f} |\n")
    lg = A["legacy"]
    w(f"The legacy rule set (`AllLegacy`) holds {lg['modules']:,} modules, "
      f"{lg['proofs']:,} proofs, {lg['hand_lines']:,} hand lines and "
      f"{lg['gate_seconds']:,.0f} module-seconds.\n")
    w("| root | modules | lines | module-seconds |")
    w("|---|---:|---:|---:|")
    for k, t in q1["per_root"].items():
        w(f"| {k} ({ROOT_LETTERS[k]}) | {t['modules']:,} | {t['lines']:,} | {t['gate_seconds']:,.0f} |")
    t = q1["tests"]
    w(f"| any test | {t['modules']:,} | {t['lines']:,} | {t['gate_seconds']:,.0f} |\n")

    # Q1
    u = q1["unreachable"]
    w("## 1. Unreachable from every root and every test\n")
    w(f"{num(u)}.\n")
    w("| gate that builds them | modules | lines | module-seconds |")
    w("|---|---:|---:|---:|")
    for g, t in q1["unreachable_by_gate"].items():
        w(f"| {g} | {t['modules']} | {t['lines']:,} | {t['gate_seconds']:,.0f} |")
    w("")
    w(f"`check-iris` builds all of `Proofs/`, so each unreachable proof module costs gate "
      f"time. The unreachable set is {u['gate_seconds'] / A['all']['gate_seconds']:.0%} of "
      f"all recorded module-seconds and {u['lines'] / A['all']['lines']:.0%} of all lines. "
      f"Of these modules, {A['classes']['remove now']['modules']} are \"remove now\". The "
      "other unreachable modules are frozen benchmark inputs, plan inputs, or modules "
      "that those inputs import. "
      f"{q1['tests_only']['modules']} more modules are reachable only from tests.\n")

    # Q2
    w("## 2. Legacy chains that the four merged segments replaced\n")
    pc, sp = q2["per_chunk"], q2["support"]
    w(f"- Per-chunk proofs whose conclusion lies inside a merged segment's range: {num(pc)}.")
    w(f"- Modules that exist only to support them (no import path from a root, a test or "
      f"a segment that avoids the per-chunk set): {num(sp)}.")
    w("- Many of these modules are reachable only through the Phase C root. That root "
      "names `WriteSuccessExactWithdrawalsNativeConnection.v` as the `like` template of "
      "the post-withdrawals segment, so the generator reads it.")
    ext = [r for r in q2["rows"] if r["live_importers"]]
    w(f"- What still imports them from outside the set: {len(ext)} of these modules "
      "has an importer that is reachable and not in the set:")
    for r in ext:
        w(f"  - `{short(r['path'])}` ← " + ", ".join(f"`{short(i)}`" for i in r["live_importers"]))
    w("")
    w("| module | role | conclusion entries | superseded by | class | lines | s |")
    w("|---|---|---|---|---|---:|---:|")
    for r in q2["rows"]:
        sup = ", ".join(short(s) for s in r["superseded_by"][:2])
        if len(r["superseded_by"]) > 2:
            sup += f" +{len(r['superseded_by']) - 2}"
        w(f"| `{short(r['path'])}` | {r['role']} | {' '.join(r['entries'][:3])} | {sup} | "
          f"{r['class']} | {r['lines']} | {r['seconds'] or 0:.0f} |")
    w("")

    # Q3
    groups = q3["groups"]
    sites = sum(len(g["sites"]) for g in groups)
    lem = [g for g in groups if g["family"] == "lemma"]
    w("## 3. Duplicate definitions\n")
    w(f"Normalization: I remove comments, collapse whitespace and replace the declared name "
      f"with `_`. I compare statements of 40 characters or more. {len(groups)} statements "
      f"occur in two or more modules, at {sites} sites: {len(lem)} lemma statements and "
      f"{len(groups) - len(lem)} definitions. {len(q3['same_name_defs'])} definition names "
      "occur in two or more modules. The canonical location is the reachable site in "
      "`Contracts/` or `Automation/` with the most importers, else the most-imported "
      "reachable site. The 25 largest groups:\n")
    w("| sites | live sites | kind | canonical | statement (start) |")
    w("|---:|---:|---|---|---|")
    for g in groups[:25]:
        stmt = g["statement"][:90].replace("|", "\\|")
        w(f"| {len(g['sites'])} | {g['live_sites']} | {g['family']} | `{short(g['canonical'])}` | `{stmt}` |")
    w("\nDefinition names that occur in more than one module:\n")
    w("| name | modules | canonical |")
    w("|---|---:|---|")
    for d in q3["same_name_defs"]:
        w(f"| `{d['name']}` | {len(d['modules'])} | `{short(d['canonical'])}` |")
    w("")

    # Q4
    w("## 4. Modules over the limits\n")
    w("Limit: 300 s or 6 GiB for a proof module. The test uses the CPU seconds and the "
      "peak RSS of the latest recorded run. No module exceeds 6 GiB; the largest peak is "
      f"{max(r['rss_gib'] or 0 for r in R.values()):.1f} GiB.\n")
    w("| module | class | latest CPU s | worst CPU s | GiB | roots | fix |")
    w("|---|---|---:|---:|---:|---|---|")
    for r in A["q4"]:
        fix = "removal" if r["class"].startswith("remove") else "split (reachable)"
        roots = "".join(ROOT_LETTERS[x] for x in r["roots"]) or "-"
        w(f"| `{short(r['path'])}` | {r['class']} | {r['cpu']:.0f} | {r['max_cpu']:.0f} | "
          f"{r['rss_gib']:.1f} | {roots} | {fix} |")
    rem = sum(1 for r in A["q4"] if r["class"].startswith("remove"))
    w(f"\n{rem} of {len(A['q4'])} go with a removal. The {len(A['q4']) - rem} "
      "`SourceAuthorization` modules are on the `Contract.v` path and need a split. "
      "These times come from loaded builds. The Raw carrier chunks passed alone at "
      "103 to 161 CPU s (BUILDOUT_REPORT), so recheck them alone before a split.\n")

    # Q5
    w("## 5. Automation\n")
    q5 = A["q5"]
    legacy_only = [r for r in q5 if r["current_proof_importers"] == 0 and r["legacy_importers"] > 0]
    unused = [r for r in q5 if r["importers"] - r["test_importers"] == 0 or
              (not r["roots"] and not r["reached_by_tests"])]
    w(f"{len(q5)} modules. \"cur\" counts current-style proof modules (`All`, outside "
      "tests) that import the module directly. \"leg\" counts legacy modules. \"tests\" "
      "counts direct test importers. \"reach\" counts tests that reach it transitively.\n")
    w(f"- Used only by legacy proofs ({len(legacy_only)}): " +
      ", ".join(f"`{r['path'][19:]}`" for r in legacy_only) + ".")
    w(f"- Imported only by tests, or by nothing reachable ({len(unused)}): " +
      ", ".join(f"`{r['path'][19:]}`" for r in unused) + ".")
    w("- The arms showed these rules to move nothing: every B1 rule changed zero closed "
      "outcomes on both frozen sets. The CallReturn switch also changed zero classes, and "
      "OutcomeHandoff (B4) changed zero outcomes. Only ExistentialArrayRestore (B4, five "
      "rows to closed) and the v2 bundle moved outcomes. The parked T1-a, T1-b, T2-a, "
      "T3-a, T3-b and T5 candidates are not in the tree.\n")
    w("| module | lines | importers | cur | leg | tests | reach | roots | arm result |")
    w("|---|---:|---:|---:|---:|---:|---:|---|---|")
    for r in q5:
        roots = "".join(ROOT_LETTERS[x] for x in r["roots"]) or "-"
        w(f"| `{r['path'][19:]}` | {r['lines']} | {r['importers']} | {r['current_proof_importers']} | "
          f"{r['legacy_importers']} | {r['test_importers']} | {r['reached_by_tests']} | {roots} | {r['arm']} |")
    w("")

    # Q6
    w("## 6. Scripts not run since the reboot (2026-09-10)\n")
    w(section(scripts, "Summary"))
    w("")
    w(section(scripts, "Unused since reboot"))
    w("")

    # Q7
    w("## 7. Worktrees and branches\n")
    w(section(branches, "Summary"))
    w("")
    w("Do not remove `.worktrees/islaris-native`: it holds the root branch. Its rule row "
      "reads removable only because the branch equals the root.\n")
    w("### Branches with unique unmerged work\n")
    w(section(branches, "Unique unmerged work (unmatched `+` commits / all `+` commits)"))
    w("")

    # Q8
    w("## 8. The 201-proof cleanup\n")
    for title in ("Summary", "Reasons", "Not-replaced proofs",
                  "Closed only in the later corpus `6d8ef58e` (not part of the 217)"):
        body = section(closed, title)
        if body:
            w(f"### {title}\n\n{body}\n")

    # Tables
    w("## Branch table\n")
    table = re.search(r"^\| branch .*?(?=^## )", branches, re.S | re.M)
    w(table.group(0).strip() if table else "")
    w("")
    w("## Module table\n")
    w("Roots: C contract, M main, S shell, A adequacy, P Phase C; T = number of tests that "
      "reach the module. s = wall seconds of the latest run; GiB = its peak RSS.\n")
    w("| module | lines | proofs | hand | rule set | roots | T | importers | nearest live importer | superseded by | s | GiB | class | why |")
    w("|---|---:|---:|---:|---|---|---:|---:|---|---|---:|---:|---|---|")
    order = {"remove now": 0, "remove after CP3": 1, "debt, keep": 2, "live": 3}
    for r in sorted(R.values(), key=lambda r: (order[r["class"]], r["path"])):
        roots = "".join(ROOT_LETTERS[x] for x in r["roots"]) or "-"
        near = r["nearest_live_importer"]
        near = short(near) if near else "none"
        sup = short(r["superseded_by"][0]) if r["superseded_by"] else ""
        if len(r["superseded_by"]) > 1:
            sup += f" +{len(r['superseded_by']) - 1}"
        s = f"{r['seconds']:.0f}" if r["seconds"] is not None else "-"
        g = f"{r['rss_gib']:.1f}" if r["rss_gib"] is not None else "-"
        w(f"| `{short(r['path'])}` | {r['lines']} | {r['proofs']} | {r['hand_lines']} | "
          f"{r['rule_set']} | {roots} | {r['tests']} | {r['importers']} | {near} | {sup} | "
          f"{s} | {g} | {r['class']} | {r['why']} |")
    Path(a.out).write_text("\n".join(out) + "\n")
    print(f"wrote {a.out}: {len(out)} lines")


if __name__ == "__main__":
    main()
