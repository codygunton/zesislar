"""Answer the sweep questions 1 to 5 from the `inventory.py` records.

Writes one JSON document (`--out`) that `render.py` turns into prose and
tables. Questions 6 to 8 come from `script_refs.py`, `branches.py` and
`closed_cleanup_gap.py`.
"""

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

from inventory import ROOTS, SEGMENTS, read_coqdep, reach

TAIL = (0x15668, 0x15a14)
# Rule arms from docs/ai/plan/BUILDOUT_REPORT.md (B1 table at 9ebff0c6, B4
# table at 40cdc060): outcome moves on the frozen 305- and 48-row sets.
ARMS = {
    "Switches/SpecTail.v": "B1: 0 outcomes; C1 -2 (in v2)",
    "Switches/LookupReduce.v": "B1: 0 outcomes; C3 -1 (in v2)",
    "Switches/SealedOpen.v": "B1: 0 outcomes; C1 -14 (in v2; attribution open)",
    "Switches/WitnessArith.v": "B1: 0 outcomes; C1 -6 (in v2; attribution open)",
    "Switches/CallReturn.v": "B1: 0 outcomes, 0 classes (excluded; opt-in)",
    "Switches/CallReturnSpecTable.v": "B1: part of the zero-row CallReturn arm",
    "Switches/ExistentialArrayRestore.v": "B4: 5 residual->closed (in v2)",
    "Switches/OutcomeHandoff.v": "B4: 0 outcomes; one class (in v2)",
    "SpecTable.v": "B1: 0 outcomes; C1 -15 (excluded from v2)",
    "WordArrayBytes.v": "B1: 0 outcomes; C2 -1 (excluded from v2)",
    "StackArrayLookup.v": "B1: 0 outcomes; C1 -6 (excluded; attribution open)",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modules", required=True)
    parser.add_argument("--coqdep", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    R = json.loads(Path(args.modules).read_text())
    deps = read_coqdep(args.coqdep)
    importers = defaultdict(set)
    for m, ds in deps.items():
        for d in ds:
            importers[d].add(m)

    def secs(rows):
        return round(sum(r["seconds"] or 0 for r in rows), 1)

    def total(rows):
        rows = list(rows)
        return {"modules": len(rows), "lines": sum(r["lines"] for r in rows),
                "proofs": sum(r["proofs"] for r in rows),
                "hand_lines": sum(r["hand_lines"] for r in rows), "seconds": secs(rows),
                "gate_seconds": secs(r for r in rows if r["in_gate"] != "none")}

    out = {"classes": {}, "q1": {}, "q2": {}, "q3": {}, "q4": [], "q5": []}
    for cls in ("remove now", "remove after CP3", "debt, keep", "live"):
        out["classes"][cls] = total(r for r in R.values() if r["class"] == cls)
    out["all"] = total(R.values())
    out["legacy"] = total(r for r in R.values() if r["rule_set"] == "AllLegacy")
    out["no_cost"] = sorted(m for m, r in R.items() if r["seconds"] is None)

    # Q1. Unreachable from every root (the four, Phase C) and every test.
    unreach = [r for r in R.values() if not r["roots"] and not r["tests"]]
    no_pc = [r for r in R.values() if not [x for x in r["roots"] if x != "phase_c"]
             and not r["tests"]]
    out["q1"] = {
        "unreachable": total(unreach),
        "unreachable_by_gate": {g: total(r for r in unreach if r["in_gate"] == g)
                                for g in ("check-iris", "check-fast", "none")},
        "without_phase_c_root": total(no_pc),
        "tests_only": total(r for r in R.values() if not r["roots"] and r["tests"]),
        "per_root": {k: total(r for r in R.values() if k in r["roots"])
                     for k in ("contract", "main", "shell", "adequacy", "phase_c")},
        "tests": total(r for r in R.values() if r["tests"]),
    }

    # Q2. Per-chunk proofs inside a merged segment's range, the modules that
    # exist only for them, and what still imports them.
    sup = {m for m, r in R.items() if any(s[2] in r["superseded_by"] for s in SEGMENTS)}
    live_starts = list(ROOTS.values()) + [s[2] for s in SEGMENTS] + [
        m for m in R if m.startswith(("ZesuSsz/Proofs/Tests/", "ZesuSsz/Tests/"))]
    kept = reach(deps, live_starts, blocked=frozenset(sup))
    support = (reach(deps, sorted(sup)) - kept) - sup
    tail = {m for m, r in R.items()
            if any(TAIL[0] <= int(a, 16) < TAIL[1] for a in r["entries"])}
    seg_reach = set().union(*(reach(deps, [s[2]]) for s in SEGMENTS))
    rows = []
    for m in sorted(sup | support):
        r = R[m]
        live_imp = sorted(i for i in importers[m] if (R[i]["roots"] or R[i]["tests"])
                          and i not in sup | support)
        rows.append({"path": m, "role": "per-chunk" if m in sup else "support",
                     "entries": r["entries"], "superseded_by": r["superseded_by"],
                     "class": r["class"], "lines": r["lines"], "seconds": r["seconds"],
                     "live_importers": live_imp})
    out["q2"] = {"rows": rows, "per_chunk": total(R[m] for m in sup),
                 "support": total(R[m] for m in support),
                 "tail_region_not_in_segments": total(
                     R[m] for m in tail - seg_reach),
                 "tail_region_reachable_outside_segments": sorted(
                     m for m in tail - seg_reach if R[m]["roots"] or R[m]["tests"])}

    # Q3. Duplicate statements, by normalized text with the name removed.
    groups = defaultdict(list)
    names = defaultdict(set)
    for m, r in R.items():
        if R[m]["excluded"]:
            continue
        for kind, name, body in r["decls"]:
            fam = "def" if kind in ("Definition", "Fixpoint", "Inductive", "Record",
                                    "Class", "Program Definition") else "lemma"
            norm = re.sub(rf"\b{re.escape(name)}\b", "_", body)
            if len(norm) >= 40:
                groups[(fam, norm)].append((m, name))
            names[(fam, name)].add(m)

    def canonical(mods):
        def key(m):
            r = R[m]
            return (not (r["roots"] or r["tests"]),
                    not m.startswith(("ZesuSsz/Contracts/", "ZesuSsz/Automation/")),
                    -r["importers"], m)
        return sorted(mods, key=key)[0]

    dups = []
    for (fam, norm), sites in groups.items():
        mods = sorted({m for m, _ in sites})
        if len(mods) < 2:
            continue
        dups.append({"family": fam, "sites": sorted(sites), "canonical": canonical(mods),
                     "live_sites": sum(1 for m in mods if R[m]["roots"] or R[m]["tests"]),
                     "statement": norm[:160]})
    dups.sort(key=lambda d: (-len(d["sites"]), d["statement"]))
    same_name = [{"family": fam, "name": name, "modules": sorted(mods),
                  "canonical": canonical(mods)}
                 for (fam, name), mods in names.items() if len(mods) > 1 and fam == "def"]
    out["q3"] = {"groups": dups, "same_name_defs": sorted(same_name, key=lambda d: -len(d["modules"]))}

    # Q4. Over the limits, by the worst recorded run.
    for m, r in sorted(R.items()):
        if r["over_limit"]:
            out["q4"].append({k: r[k] for k in ("path", "class", "seconds", "cpu", "rss_gib", "max_cpu",
                                                "max_seconds", "max_rss_gib", "lines",
                                                "proofs", "roots", "tests")})

    # Q5. Automation rule modules.
    for m, r in sorted(R.items()):
        if not m.startswith("ZesuSsz/Automation/"):
            continue
        imps = importers[m]
        cur = [i for i in imps if R[i]["rule_set"] == "All" and i.startswith("ZesuSsz/Proofs/")
               and not i.startswith("ZesuSsz/Proofs/Tests/")]
        leg = [i for i in imps if R[i]["rule_set"] == "AllLegacy"]
        tests = [i for i in imps if i.startswith(("ZesuSsz/Proofs/Tests/", "ZesuSsz/Tests/"))]
        rel = m[len("ZesuSsz/Automation/"):]
        out["q5"].append({"path": m, "lines": r["lines"], "importers": len(imps),
                          "current_proof_importers": len(cur),
                          "live_current_importers": sum(1 for i in cur if R[i]["roots"]),
                          "legacy_importers": len(leg), "test_importers": len(tests),
                          "reached_by_tests": r["tests"], "roots": r["roots"],
                          "class": r["class"], "arm": ARMS.get(rel, "")})

    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
