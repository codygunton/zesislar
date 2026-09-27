"""Render TECH_DEBT_PROPOSAL.md: a ranked removal list in three tiers.

Reads the `inventory.py` records and the `answers.py` document of the same
run, plus the branch and script reports. Each row carries the lines and
gate module-seconds it saves and the exact change it needs.
"""

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

from inventory import read_coqdep, reach

BASELINES = ("hygiene_baseline.json", "proof_size_baseline.json",
             "residual_record_baseline.json")
SHARED = ("ZesuSsz/Automation/All.v", "ZesuSsz/Automation/AllLegacy.v",
          "ZesuSsz/Contracts/Endpoints.v", "ZesuSsz/Proofs/WriteSuccess/Interfaces.v",
          "ZesuSsz/Proofs/WriteSuccess/WriteSuccessNativeContract.v")
# Gate wall time of the last cold 24-job `check-iris` with a recorded
# duration (BUILDOUT_REPORT, root 40cdc060, 2026-09-25): 39 min 35 s.
COLD_GATE_S = 2375
JOBS = 24


def family(path):
    """Group name: the module stem with addresses and indices replaced by `*`."""
    stem = Path(path).stem
    stem = re.sub(r"1[0-9a-f]{4}", "*", stem)
    stem = re.sub(r"\d+", "*", stem)
    return str(Path(path).parent / stem).replace("ZesuSsz/Proofs/WriteSuccess/", "WS/") \
        .replace("ZesuSsz/", "")


def baseline_hits(tree, paths):
    hits = {}
    for name in BASELINES:
        data = json.loads((tree / "ZesuSsz/Evidence" / name).read_text())
        keys = set(data.get("files", {})) | set(data.get("legacy_entry_files", []))
        keys |= {k.split(":")[0] for k in data.get("lemmas", [])}
        hits[name] = len(keys & set(paths))
    return hits


def det_set_hits(tree, paths):
    names = {Path(p).name for p in paths}
    hits = {}
    for f in sorted((tree / "ZesuSsz/Evidence/det").glob("*.txt")):
        rows = [ln.split(":")[0].strip() for ln in f.read_text().splitlines() if ":" in ln]
        n = sum(1 for r in rows if r in names)
        if n:
            hits[f.name] = n
    return hits


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("modules", "answers", "branches", "scripts", "out", "sha"):
        p.add_argument(f"--{name}", required=True)
    p.add_argument("--tree", default=".")
    p.add_argument("--coqdep", help="coqdep output; default: beside --modules")
    a = p.parse_args()
    tree = Path(a.tree).resolve()
    R = json.loads(Path(a.modules).read_text())
    A = json.loads(Path(a.answers).read_text())
    deps = read_coqdep(a.coqdep or Path(a.modules).with_name("coqdep.out"))
    branches = Path(a.branches).read_text()
    scripts = Path(a.scripts).read_text()
    out = []
    w = out.append

    tiers = {c: [r for r in R.values() if r["class"] == c]
             for c in ("remove now", "remove after CP3", "debt, keep")}
    all_s = A["all"]["gate_seconds"]

    def groups(rows):
        g = defaultdict(list)
        for r in rows:
            g[family(r["path"])].append(r)
        return sorted(g.items(), key=lambda kv: -sum(r["seconds"] or 0 for r in kv[1]))

    def tot(rows):
        return (len(rows), sum(r["lines"] for r in rows), sum(r["hand_lines"] for r in rows),
                sum(r["seconds"] or 0 for r in rows if r["in_gate"] != "none"))

    # Dependents of shared files, per class: what a shared-file change rebuilds.
    rdeps = defaultdict(set)
    for m, ds in deps.items():
        for d in ds:
            rdeps[d].add(m)
    shared = {}
    for s in SHARED:
        dependents = reach(rdeps, [s]) - {s}
        by = defaultdict(int)
        for m in dependents:
            by[R[m]["class"]] += 1
        shared[s] = (len(dependents), dict(by))

    n1, l1, h1, s1 = tot(tiers["remove now"])
    n2, l2, h2, s2 = tot(tiers["remove after CP3"])
    rn_paths = [r["path"] for r in tiers["remove now"]]
    excluded_rn = [r["path"] for r in tiers["remove now"] if r["excluded"]]

    w("# Tech-debt removal proposal\n")
    w(f"Root `{a.sha[:8]}`. Source: `TECH_DEBT_INVENTORY.md` of the same run; scripts "
      "`ZesuSsz/Evidence/debt/` on branch `debt-sweep`. The sweep deletes nothing. The "
      "lead decides what the builder removes and when.\n")

    w("## Estimate\n")
    frac1, frac2 = s1 / all_s, s2 / all_s
    w(f"The recorded module-seconds of the whole theory ({all_s:,.0f}) divided by 24 jobs "
      f"give {all_s / JOBS / 60:.0f} min. The last cold 24-job `check-iris` with a "
      f"recorded time took {COLD_GATE_S / 60:.0f} min. The gate is therefore bound by "
      f"work, and its time scales with the module-seconds removed. Tier 1 removes "
      f"{n1} modules, {l1:,} lines and {s1:,.0f} module-seconds ({frac1:.0%}). That "
      f"saves about {COLD_GATE_S * frac1 / 60:.0f} min of each cold gate. Tier 2 "
      f"removes {n2} modules, {l2:,} lines and {s2:,.0f} module-seconds ({frac2:.0%}), "
      f"which saves about {COLD_GATE_S * frac2 / 60:.0f} min more after CP3. A warm "
      "preview saves less, because it rebuilds only the dependents of the changed files. "
      "The repair saving is in the table below. A change to a shared file today rebuilds "
      "every dependent, and a failed dependent means a repair round:\n")
    w("| shared file | dependents | in tier 1 | in tier 2 | kept |")
    w("|---|---:|---:|---:|---:|")
    for s, (n, by) in shared.items():
        kept = by.get("debt, keep", 0) + by.get("live", 0)
        w(f"| `{s[8:]}` | {n} | {by.get('remove now', 0)} | {by.get('remove after CP3', 0)} | {kept} |")
    over = A["q4"]
    over1 = sum(1 for r in over if R[r["path"]]["class"] == "remove now")
    dup_all = A["q3"]["groups"]
    dup_left = [g for g in dup_all if sum(1 for m, _ in g["sites"]
                                          if R[m]["class"] in ("debt, keep", "live")) >= 2]
    cut = {k: (by.get("remove now", 0) + by.get("remove after CP3", 0)) / n
           for k, (n, by) in shared.items() if n}
    w(f"\nAfter both tiers, a change to `Automation/All.v` rebuilds "
      f"{cut['ZesuSsz/Automation/All.v']:.0%} fewer modules, and a change to "
      f"`Contracts/Endpoints.v` rebuilds {cut['ZesuSsz/Contracts/Endpoints.v']:.0%} fewer. "
      "A repair round has that many fewer modules that can fail. The two tiers resolve "
      f"{len(dup_all) - len(dup_left)} of the {len(dup_all)} duplicate statements "
      f"(question 3). Tier 1 removes {over1} of the {len(over)} over-limit "
      "modules (question 4). The module times come from loaded builds, like the gate's "
      "own time, so the ratio to the gate time holds.\n")

    # Tier 1
    w("## Tier 1: remove now\n")
    w("### Exact change for every module row\n")
    w("1. `git rm` the modules of the row. The appendix lists the paths.")
    w("2. No module in tier 2, in tier 3 or live imports a tier-1 module. The classifier "
      "checks this closure over the coqdep graph, so no import changes.")
    w("3. Dune needs no change: the theory takes `:standard`. Exception: remove the "
      f"{len(excluded_rn)} excluded names from the `(modules (:standard \\ ...))` list in "
      "`ZesuSsz/dune`: " + ", ".join(f"`{Path(p).stem}`" for p in excluded_rn) + ".")
    hits = baseline_hits(tree, rn_paths)
    w("4. Delete the entries of the removed files from the hygiene baselines in "
      "`ZesuSsz/Evidence/` (" + ", ".join(f"`{k}` {v}" for k, v in hits.items()) +
      "). Otherwise the ratchet reports stale entries.")
    dh = det_set_hits(tree, rn_paths)
    if dh:
        w("5. The measurement sets of the determinism plan name removed modules (" +
          ", ".join(f"`det/{k}` {v} rows" for k, v in dh.items()) + "). Drop those "
          "rows with `refreeze.py` before the removal.")
    else:
        w("5. The benchmark and `det/` measurement sets are re-frozen (`refreeze.py`) "
          "and name no tier-1 module; no set change.")
    w("6. Then run one full preview. `Print Assumptions` of the four roots must not change.\n")
    w("### Ranked module groups\n")
    w("Groups: the module name with addresses and indices replaced by `*`. The rank is "
      "the module-seconds saved.\n")
    w("| rank | group | modules | lines | hand lines | module-s saved | why |")
    w("|---:|---|---:|---:|---:|---:|---|")
    for i, (name, rows) in enumerate(groups(tiers["remove now"]), 1):
        n, l, h, s = tot(rows)
        why = sorted({r["why"] for r in rows})
        w(f"| {i} | `{name}` | {n} | {l:,} | {h:,} | {s:,.0f} | {'; '.join(why)} |")
    w(f"| | **total** | {n1} | {l1:,} | {h1:,} | {s1:,.0f} | |\n")

    w("### Other tier-1 items\n")
    n_del = int(re.search(r"Branches deletable: (\d+)", branches).group(1))
    unused = re.findall(r"^- `([^`]+)` \((\d+) lines", scripts, re.M)
    nix_used = {"generate_level_manifest.py", "qemu_trace_plugin.c",
                "build_level1_proof_map.py", "generate_level_boundary_bindings.py"}
    drop = [(f, int(n)) for f, n in unused if Path(f).name not in nix_used]
    w("| item | count | saved | exact change |")
    w("|---|---:|---|---|")
    w(f"| branches merged or superseded, no patch-unique commit | {n_del} | clutter; {n_del} refs "
      "local and on origin | `git branch -D` and `git push origin --delete`, list in "
      "`branches.md` (status merged or superseded). Check the 19 superseded ones first: "
      "subject match only. |")
    w("| worktrees of those branches, clean | 9 | about 15.4 GiB | `git worktree remove "
      ".worktrees/<name>` for endpoint-step5, islaris-native-auto, "
      "islaris-native-auto-memory, islaris-native-exec-b, -exec-c, -exec-d, "
      "islaris-native-infra, islaris-native-port, islaris-native-tail. Keep "
      "`.worktrees/islaris-native`: it holds the root branch. |")
    w(f"| scripts unused since 2026-09-10 | {len(drop)} | {sum(n for _, n in drop):,} lines | "
      "`git rm` " + ", ".join(f"`{f}`" for f, _ in drop) + ". Keep the four Evidence "
      "scripts that `nix/evidence.nix` uses. |\n")

    # Tier 2
    w("## Tier 2: remove after CP3\n")
    w("Exact change: the same six steps as tier 1, plus two more:\n")
    w("1. Before the removal, re-freeze `Evidence/residuals/benchmark_set.txt` and "
      "`benchmark_set_rule15.txt` without their rows, and record a new baseline arm. "
      "The frozen benchmark is the reason most of these modules stay until CP3.")
    w("2. For a per-chunk proof inside a merged segment's range: after C2 discharges "
      "`□ instr_pre 0x15668` in `Contract.v` from the segment lemmas, the Phase C root "
      "no longer needs the `like` template. Point `open_segments.json` `like` at a "
      "segment module, then remove.\n")
    w("| rank | group | modules | lines | hand lines | module-s saved | why |")
    w("|---:|---|---:|---:|---:|---:|---|")
    for i, (name, rows) in enumerate(groups(tiers["remove after CP3"]), 1):
        n, l, h, s = tot(rows)
        why = sorted({re.sub(r" \(.*", "", r["why"]) for r in rows})
        w(f"| {i} | `{name}` | {n} | {l:,} | {h:,} | {s:,.0f} | {'; '.join(why)} |")
    w(f"| | **total** | {n2} | {l2:,} | {h2:,} | {s2:,.0f} | |\n")

    # Tier 3
    keep = tiers["debt, keep"]
    by_why = defaultdict(list)
    for r in keep:
        by_why[re.sub(r" \(.*", "", r["why"])].append(r)
    w("## Tier 3: keep as debt\n")
    w("These modules stay. Each row names the debt and the change that would retire it.\n")
    w("| rank | debt | modules | lines | hand lines | module-s | change that retires it |")
    w("|---:|---|---:|---:|---:|---:|---|")
    fixes = {
        "legacy rule set": "Re-run each proof by `zesu_block.` under the current rule set as "
                           "Phase C rules land, as A6 did (`tools/det/closed_cleanup_rewrite.py`); "
                           "switch the import from `AllLegacy` to `All` per module. The 23 "
                           "legacy-only Automation modules go when their last importer moves.",
        "over the module limits": "Split at a lemma boundary: the 6 `SourceAuthorization` "
                                  "modules on the `Contract.v` path, 310 to 403 CPU s in a loaded "
                                  "build. Measure each alone first with `tools/coqc_scratch.sh`.",
        "off every root; named in an active plan or an endpoint umbrella":
            "Wire into a root when its plan step lands (Phase 5 executor, endpoint umbrellas), "
            "or drop the plan item.",
        "excluded from the Dune theory; a Makefile input":
            "`Contracts/Machine.v` feeds `tools/machine_config.py`; no change.",
        "imported by": "Goes with its importer.",
    }
    rows = sorted(by_why.items(), key=lambda kv: -sum(r["seconds"] or 0 for r in kv[1]))
    for i, (why, rs) in enumerate(rows, 1):
        n, l, h, s = tot(rs)
        fix = fixes.get(why, fixes["imported by"] if why.startswith("imported by") else "")
        w(f"| {i} | {why} | {n} | {l:,} | {h:,} | {s:,.0f} | {fix} |")
    dup_kept = [g for g in A["q3"]["groups"]
                if sum(1 for m, _ in g["sites"] if R[m]["class"] in ("debt, keep", "live")) >= 2]
    w(f"| {len(rows) + 1} | duplicate statements that survive tiers 1 and 2 | "
      f"{len(dup_kept)} groups | | | | Move each one to its canonical module (inventory "
      "question 3) and import it. Move a definition to `Contracts/` only when two kept "
      "proofs need it (AGENTS.md). |")
    w(f"| {len(rows) + 2} | branches with unique unmerged work | 51 | | | | The lead rules per "
      "branch. `determinism`, `det-rebase-trial`, `builder-memory-budget` and "
      "`builder-a5-prep` hold 193 of the unique commits. |\n")

    # Appendix
    w("## Appendix: tier-1 and tier-2 paths\n")
    for cls in ("remove now", "remove after CP3"):
        w(f"### {cls}\n")
        w("```")
        for r in sorted(tiers[cls], key=lambda r: r["path"]):
            w(r["path"])
        w("```\n")
    Path(a.out).write_text("\n".join(out) + "\n")
    print(f"wrote {a.out}: {len(out)} lines")


if __name__ == "__main__":
    main()
