"""Classify every Rocq module of the ZesuSsz theory for the tech-debt sweep.

Inputs:
  --tree       a checkout of the root (the sweep reads, never writes it)
  --coqdep     the output of `coqdep -Q ZesuSsz ZesuSsz <all .v files>`
  --cost       the JSON that `gate_cost.py` writes
Output: one JSON record per module (`--out`), used by `render.py`.

Dependency facts come from coqdep, the tool Dune runs for the theory.
Size facts come from `tools/residual/modules.py`, the parser the hygiene
checker uses, so "hand lines" means the same thing here as in the gate.
"""

import argparse
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path

ROOTS = {
    "contract": "ZesuSsz/Proofs/WriteSuccess/Contract.v",
    "main": "ZesuSsz/Proofs/Main/Main.v",
    "shell": "ZesuSsz/Compliance/Shell.v",
    "adequacy": "ZesuSsz/Export/Adequacy.v",
}
TEST_DIRS = ("ZesuSsz/Proofs/Tests/", "ZesuSsz/Tests/")
CURRENT = "ZesuSsz/Automation/All.v"
LEGACY = "ZesuSsz/Automation/AllLegacy.v"

# The four merged segments of the writeSuccess tail, [entry, exit), and the
# module that proves each. From the segment lemmas' own `instr_body` entry
# and the `instr_pre` exit hypotheses.
SEGMENTS = [
    (0x15668, 0x15694, "ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactPostTransactionsSegment.v"),
    (0x15744, 0x15754, "ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactSuffixEntrySegment.v"),
    (0x159b8, 0x159d8, "ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactTailFieldsThirdSegment.v"),
    (0x159d8, 0x15a14, "ZesuSsz/Proofs/WriteSuccess/WriteSuccessExactEpilogueSegment.v"),
]

DECL = re.compile(
    r"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)*"
    r"(Lemma|Theorem|Corollary|Fact|Definition|Fixpoint|Inductive|Record|"
    r"Class|Instance|Program\s+Definition)\s+([A-Za-z_][\w']*)")
BODY_ENTRY = re.compile(r"instr_body\s+0x([0-9a-fA-F]+)")
COMMENT = re.compile(r"\(\*.*?\*\)", re.S)


def read_coqdep(path):
    """Module -> set of ZesuSsz modules it requires, from coqdep's `.vo` lines."""
    deps = {}
    for line in Path(path).read_text().splitlines():
        head, _, tail = line.partition(": ")
        if not head.endswith(".required_vo"):
            continue
        items = tail.split()
        source = items[0]
        deps[source] = {d[:-1] for d in items[1:]
                        if d.startswith("ZesuSsz/") and d.endswith(".vo")}
    return deps


def dune_excluded(tree):
    """Modules the `ZesuSsz/dune` stanza removes from the theory."""
    text = (tree / "ZesuSsz" / "dune").read_text()
    block = re.search(r"\(:standard\s*\\(.*?)\)\)", text, re.S)
    names = block.group(1).split() if block else []
    return {"ZesuSsz/" + n.replace(".", "/") + ".v" for n in names}


def reach(deps, starts, blocked=frozenset()):
    seen, queue = set(), deque(s for s in starts if s not in blocked)
    while queue:
        node = queue.popleft()
        if node in seen:
            continue
        seen.add(node)
        queue.extend(d for d in deps.get(node, ()) if d not in blocked)
    return seen


def statements(text):
    """(kind, name, normalized statement) for every declaration."""
    text = COMMENT.sub(" ", text)
    out = []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        chunk = []
        for follow in lines[i:i + 80]:
            chunk.append(follow)
            if re.search(r"\.\s*$", follow) or re.match(r"\s*Proof\b", follow):
                break
        body = " ".join(chunk)
        body = re.sub(r"\bProof\b.*$", "", body)
        body = body[m.end():]
        body = re.sub(r"\s+", " ", body).strip().rstrip(".")
        out.append((kind, name, body))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", required=True, type=Path)
    parser.add_argument("--coqdep", required=True)
    parser.add_argument("--cost", required=True)
    parser.add_argument("--plans", nargs="*", default=[],
                        help="active plan files; a module named there is planned")
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    tree = args.tree.resolve()
    sys.path.insert(0, str(tree / "tools" / "residual"))
    from modules import parse_module

    deps = read_coqdep(args.coqdep)
    excluded = dune_excluded(tree)
    cost = json.loads(Path(args.cost).read_text())
    modules = sorted(deps)
    importers = defaultdict(set)
    for mod, ds in deps.items():
        for d in ds:
            importers[d].add(mod)

    tests = [m for m in modules if m.startswith(TEST_DIRS)]
    roots = dict(ROOTS)
    reach_by = {name: reach(deps, [path]) for name, path in roots.items()}
    # Phase C consumes the merged segment lemmas and the chain inputs of
    # `tools/det` (their `like` and `imports`). `Contract.v` does not import
    # them yet, since it assumes the tail at 0x15668, so they form a fifth
    # root, listed separately.
    phase_c = {seg for _, _, seg in SEGMENTS}
    for spec in [tree / "ZesuSsz/Evidence/det/open_segments.json",
                 *sorted((tree / "ZesuSsz/Evidence/det/chain").glob("*.json"))]:
        data = json.loads(spec.read_text())
        for item in data if isinstance(data, list) else [data]:
            names = list(item.get("imports", []))
            if item.get("like"):
                names.append("ZesuSsz.Proofs.WriteSuccess." + item["like"][:-2])
            for n in names:
                path = n.replace(".", "/") + ".v"
                if path in deps:
                    phase_c.add(path)
    reach_by["phase_c"] = reach(deps, sorted(phase_c))
    test_reach = defaultdict(int)
    for t in tests:
        for m in reach(deps, [t]):
            test_reach[m] += 1
    live_roots = list(ROOTS.values()) + sorted(phase_c)
    reachable_roots = set().union(*reach_by.values())
    reachable_any = reachable_roots | set(test_reach)

    legacy = {m for m in modules if LEGACY in deps[m] and m != LEGACY}
    current = {m for m in modules if CURRENT in deps[m]}
    # Reachable from a root without passing through a legacy module.
    clean_reach = reach(deps, live_roots, blocked=frozenset(legacy))

    entries_by_module = {}
    plan_text = "\n".join(Path(p).read_text(errors="replace") for p in args.plans)
    frozen_bench = set()
    for name in ("benchmark_set.txt", "benchmark_set_rule15.txt"):
        for line in (tree / "ZesuSsz/Evidence/residuals" / name).read_text().splitlines():
            if ":" in line and not line.startswith("#"):
                frozen_bench.add(line.split(":")[0].strip())
    makefile = (tree / "Makefile").read_text()
    endpoint_umbrellas = {m for m in modules
                          if re.fullmatch(r"ZesuSsz/Proofs/(\w+)/\1\.v", m)}
    records = {}
    for m in modules:
        text = (tree / m).read_text(errors="replace")
        try:
            proofs = parse_module(tree / m)
        except (OSError, ValueError):
            proofs = []
        decls = statements(text)
        # A lemma's entry is the last `instr_body` of its statement, the
        # conclusion; earlier ones are continuation hypotheses.
        entries = sorted({int(found[-1], 16) for kind, _, body in decls
                          if kind not in ("Definition", "Fixpoint", "Inductive", "Record",
                                          "Class", "Program Definition")
                          for found in [BODY_ENTRY.findall(body)] if found})
        entries_by_module[m] = entries
        records[m] = {
            "path": m,
            "lines": text.count("\n"),
            "proofs": len(proofs),
            "hand_lines": sum(len(p.hand_lines) for p in proofs),
            "rule_set": "AllLegacy" if m in legacy else "All" if m in current else "neither",
            "excluded": m in excluded,
            "roots": [name for name, s in reach_by.items() if m in s],
            "tests": test_reach.get(m, 0),
            "importers": len(importers[m]),
            "entries": [hex(a) for a in entries],
            "decls": decls,
        }

    # Nearest reachable importer (BFS up the reverse graph).
    for m, rec in records.items():
        seen, queue, nearest = {m}, deque([(m, 0)]), None
        while queue and nearest is None:
            node, dist = queue.popleft()
            for imp in sorted(importers[node]):
                if imp in seen:
                    continue
                seen.add(imp)
                if imp in reachable_any:
                    nearest = f"{imp} ({dist + 1})"
                    break
                queue.append((imp, dist + 1))
        rec["nearest_live_importer"] = nearest

    # Superseded by: a merged segment's range, else a reachable module that
    # proves an `instr_body` at the same entry address.
    provers = defaultdict(set)
    for m, entries in entries_by_module.items():
        if m in reachable_any:
            for a in entries:
                provers[a].add(m)
    seg_modules = {s[2] for s in SEGMENTS}
    seg_deps = {s[2]: reach(deps, [s[2]]) for s in SEGMENTS}
    for m, rec in records.items():
        by = set()
        for a in entries_by_module[m]:
            for lo, hi, seg in SEGMENTS:
                if lo <= a < hi and m != seg and m not in seg_deps[seg]:
                    by.add(seg)
            if m not in reachable_any:
                by |= {p for p in provers[a] if p != m}
        if m.startswith(TEST_DIRS):
            by = set()
        rec["superseded_by"] = sorted(by)
        rec["segment_range"] = bool(by & seg_modules)

    for m, rec in records.items():
        c = cost.get(m)
        rec["seconds"] = c["seconds"] if c else None
        rec["cpu"] = c["cpu"] if c else None
        rec["max_cpu"] = c["max_cpu"] if c else None
        rec["rss_gib"] = c["rss_gib"] if c else None
        rec["max_seconds"] = c["max_seconds"] if c else None
        rec["max_rss_gib"] = c["max_rss_gib"] if c else None
        rec["cost_date"] = c["date"] if c else None

        is_proof = m.startswith("ZesuSsz/Proofs/")
        sec_limit, gib_limit = (300, 6) if is_proof else (60, 2)
        # The limit applies to the module's own work: CPU seconds of the
        # latest run. Wall time under a 24-job gate includes contention.
        rec["over_limit"] = bool(c and (c["cpu"] > sec_limit or c["rss_gib"] > gib_limit))
        reachable = m in reachable_any
        base = Path(m).stem
        rec["in_gate"] = ("check-iris" if m.startswith("ZesuSsz/Proofs/") else
                          "check-fast" if m.split("/")[1] in
                          ("Contracts", "Automation", "Export", "Compliance") else "none")
        rec["only_via_legacy"] = m in reachable_roots and m not in clean_reach and m not in legacy
        rec["bench"] = Path(m).name in frozen_bench and m.startswith("ZesuSsz/Proofs/WriteSuccess/")
        rec["planned"] = (m in endpoint_umbrellas or (
            not m.startswith("ZesuSsz/Proofs/WriteSuccess/")
            and re.search(rf"\b{re.escape(base)}(\.v)?\b", plan_text) is not None))
        if m in excluded and base in makefile:
            cls, why = "debt, keep", "excluded from the Dune theory; a Makefile input"
        elif m in excluded:
            cls, why = "remove now", "excluded from the Dune theory"
        elif not reachable and rec["planned"]:
            cls, why = "debt, keep", "off every root; named in an active plan or an endpoint umbrella"
        elif not reachable and rec["bench"]:
            cls, why = "remove after CP3", "off every root; frozen benchmark input"
        elif not reachable:
            cls, why = "remove now", ("superseded" if rec["superseded_by"] else "orphan")
        elif rec["segment_range"]:
            cls, why = "remove after CP3", "per-chunk proof inside a merged segment's range"
        elif m in legacy:
            cls, why = "debt, keep", "legacy rule set"
        elif rec["over_limit"]:
            cls, why = "debt, keep", "over the module limits"
        else:
            cls, why = "live", ""
        rec["class"], rec["why"] = cls, why

    Path(args.out).write_text(json.dumps(records, indent=1) + "\n")
    counts = defaultdict(int)
    for rec in records.values():
        counts[rec["class"]] += 1
    print(len(records), "modules;", dict(counts))


if __name__ == "__main__":
    main()
