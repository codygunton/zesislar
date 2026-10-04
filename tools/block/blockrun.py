#!/usr/bin/env python3
"""Block-run experiment: one zesu_block run per basic block, no hand lines.

Entry state: the merged lemma whose entry is the block leader.  Each interior instr_body/instr_pre premise is dropped.
Variant A keeps successor premises, so the run can stop only at a successor (reached),
on a residual (stalled), or at the limit (timeout).  Run from the worktree.
"""
import argparse, json, os, re, sys
import analyze
import entries
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

W = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(W / "tools"))
sys.path.insert(0, str(W / "tools/det")); sys.path.insert(0, str(W / "tools/residual"))
import probes
import threading
WLOCK = threading.Lock()
import runner
PROFILE = os.environ.get("PROFILE") == "1"
EXTRA_IMPORTS = []
RUNV = os.environ.get("RUNV", "A")
CAP = int(os.environ.get("CAP", "600"))
from infer_boundary import with_standard_code, goal_record, SHELVE_TERM_GOALS, RAW_BEGIN, RAW_END
from call_sites import premises as call_premises
from classify import classify
from goals import conclusion_text
from modules import find_proof

BR = W / "_build/agents/worker-build-2-block"
BUILD = W / "_build/agents" / os.environ.get("BUILD_NAME", "worker-build-2-block")
PROOF_DIR = None
TRACE_IMPORT = None
ADDR = re.compile(r"instr_(?:body|pre)\s+\(?\s*(0x[0-9a-fA-F]+|\d+)")


def drop_premises(lines, drop):
    out, dropping = [], False
    for line in lines:
        ends = line.rstrip().endswith("-∗")
        if dropping:
            dropping = not ends
            continue
        m = ADDR.search(line)
        if m and int(m.group(1), 0) in drop:
            # A premise ends at its separating wand.
            dropping = not ends
            continue
        out.append(line)
    return out


STEPPER_T = r"""
Ltac blk_pc := try (lazymatch goal with
  | |- envs_entails ?D _ => lazymatch D with
      | context [reg_mapsto _ "PC" _ (RVal_Bits ?v)] => idtac "BLK-PC" v
      end end).
Ltac blk_pass :=
  zesu_expose_environment_alias;
  try zesu_prepare_uninit_goal;
  try zesu_normalize_find_mem_address;
  unshelve (repeat (first
    @@LIST@@; blk_pc); liShow;
    try zesu_finish_closed_wand;
    try zesu_finish_framed_wand;
    zesu_finish).
Ltac blk_run :=
  unshelve (repeat progress
    (blk_pass; try zesu_solve_instances; zesu_finish));
  try zesu_solve_instances.
Ltac blk_block :=
  tryif iStartProof then (
    zesu_expose_code_lists;
    repeat first [progress iIntros (?) | progress iIntros "#?" |
      progress iIntros "?"];
    zesu_reduce_introduced_code_lists;
    repeat iDestruct select (_ ∗ _)%I as "[? ?]";
    blk_run)
  else first [solve [zesu_finish] | idtac].
"""


RULES = os.environ.get("RULES", "v2")
if RULES not in ("v2", "call", "legacy"):
    raise ValueError("RULES must be v2, call, or legacy.")
STEPPER = "" if RULES == "legacy" else STEPPER_T.replace(
    "@@LIST@@", "[zesu_array_load_preselect | zesu_array_load_priority | "
    "zesu_conjunct_match_if_enabled | zesu_run_pass_steps | "
    "zesu_open_trace_exist | zesu_rule_set_v2_steps]")


def source(block, lemma, module, variant_run="A"):
    path = PROOF_DIR / f"{module}.v"
    proof = find_proof(path, lemma)
    lines = path.read_text().split("\n")
    stmt = lines[proof.declaration_line:proof.proof_line]
    lo, hi = int(block["leader"], 16), int(block["last"], 16)
    succ = [int(x, 16) for x in block["succ"] if x != "ret"]
    drop = set(range(lo + 4, hi + 4, 4)) - {lo}
    if variant_run == "B":
        drop |= set(succ) - {lo}
    else:
        drop -= set(succ)
    stmt = with_standard_code(drop_premises(stmt, drop))
    stmt = [l.replace(lemma, "block_run", 1) if lemma in l else l for l in stmt]
    have = " ".join(stmt)
    kept = {int(a, 0) for a in ADDR.findall(have)}
    calls, mods, _ = call_premises(lo, hi + 4)
    calls = [c for c in calls if int(c.split()[2], 16) not in kept]
    # Import the contract module only for premises we add: importing it when the
    # lemma already names the call spec changes the search.
    mods = mods if calls else []
    stops = []
    if variant_run == "A":
        # A successor without a merged state gets an abstract exit state: the run
        # stops there, and the residual against BLK_STOP is the inferred state.
        stops = [a for a in succ if a not in kept and not (lo <= a <= hi)]
    sigma = (re.search(r"islaG\s+(\w+)", have) or [None, "Σ"])[1]
    for i, l in enumerate(stmt):
        if l.rstrip().endswith(":") and stops:
            stmt[i] = l.rstrip()[:-1].rstrip() + " " + " ".join(
                f"(BLK_STOP_{a:x} : iProp {sigma})" for a in stops) + " :"
            break
    for i, l in enumerate(stmt):
        if "spec_instr_resources -∗" in l:
            stmt[i + 1:i + 1] = calls + [f"  instr_pre {hex(a)} BLK_STOP_{a:x} -∗" for a in stops]
            break
    body = (["Set Ltac Profiling."] if PROFILE else []) + [f'idtac "{probes.BEGIN}".', "try intros.", ("try (timeout %d blk_block)." % max(CAP - 30, 30)) if PROFILE else ("try zesu_block." if RULES == "legacy" else "try blk_block."),
            r'''all: try (lazymatch goal with
  | |- envs_entails _ ?P => lazymatch P with
      | context [instr_pre ?a] => idtac "BLK-AT-PRE" a
      | context [instr_body ?a] => idtac "BLK-AT-BODY" a
      end end).''',
            'all: idtac "BLK-GOAL".',
            "all: try liShow.",
            f'all: idtac "{RAW_BEGIN}".', "Show.", f'all: idtac "{RAW_END}".',
            SHELVE_TERM_GOALS, "Show."] + (["Show Ltac Profile CutOff 1."] if PROFILE else []) + ["Abort."]
    meta = {"stops": [hex(a) for a in stops], "kept_succ": [hex(a) for a in succ if a in kept]}
    return "\n".join(["Require Import ZesuSsz.Automation.All.", "Set Printing Width 200.", "Require Import isla.isla.",
                      "From iris.proofmode Require Import environments.",
                      f"Require Import {TRACE_IMPORT}."]
                     + lines[:proof.declaration_line]
                     + [f"Require Import {module}." for module in EXTRA_IMPORTS]
                     + [f"Require Import {m}." for m in mods]
                     + ([] if RULES == "legacy" else ["Require Import ZesuSsz.Automation.All.", f"Require Import ZesuSsz.Automation.Sets.{RULES}.",
                        "Require Import ZesuSsz.Automation.ArrayLoadPreselect ZesuSsz.Automation.ArrayLoadPriority ZesuSsz.Automation.ConjunctMatch ZesuSsz.Automation.V2Steps ZesuSsz.Automation.PackedWordValues ZesuSsz.Automation.ResourceGroups ZesuSsz.Automation.Hooks ZesuSsz.Automation.Finish.",
                        STEPPER])
                     + stmt + ["Proof."] + body + probes.END_MARKER
                     + [f"End {n}." for n in reversed(proof.open_blocks)] + [""]), meta


def run_one(job):
    try:
        rec = _run_one(job)
    except Exception as e:  # keep the wave alive; record the failure
        rec = {"variant": job[0], "leader": job[1]["leader"], "n": job[1]["n"], "kind": job[1]["kind"],
               "outcome": "driver-error", "error": repr(e)}
    with WLOCK:
        with open(BR / f"results_{RUNV}{'_prof' if PROFILE else ''}{'' if RULES == 'v2' else '_' + RULES}_{job[0]}.jsonl", "a") as f:
            f.write(json.dumps(rec) + "\n")
    return rec


def _run_one(job):
    variant, block = job
    tag = f"{RUNV}_{variant}_{block['leader']}" + ("_prof" if PROFILE else "") + ("" if RULES == "v2" else "_" + RULES)
    rec = {"variant": variant, **{k: block[k] for k in ("leader", "last", "n", "kind", "succ")}}
    if not block.get("pick"):
        rec["outcome"] = "skipped-no-entry"
        return rec
    lemma, module = block["pick"][0], block["pick"][1]
    rec.update(lemma=lemma, module=module)
    d = BR / "probes"; d.mkdir(exist_ok=True)
    p = d / f"{tag}.v"
    text, meta = source(block, lemma, module, RUNV)
    rec.update(meta, run=RUNV)
    p.write_text(text)
    r = runner.run(p, BUILD, CAP)
    out = (d / f"{tag}.out").read_text()
    rec["raw_path"] = str(d / f"{tag}.out")
    rec.update(seconds=r["wall"], wait_seconds=r["wait"], cpu=r["cpu"], peak_mib=r["peak_mib"], rc=r["rc"],
               rss_samples=r["rss_samples"], cap=CAP)
    rec["limit"] = r["limit"] or ("memory" if r["rc"] in (137, -9) else None)
    pcs = [int(x) for x in re.findall(r"BLK-PC \(bv_to_bvn \(Z_to_bv 64 (\d+)\)\)", out)]
    rec["pcs_seen"] = sorted({hex(x) for x in pcs})
    inblk = [x for x in pcs if int(block["leader"], 16) <= x <= int(block["last"], 16)]
    rec["k_max"] = ((max(inblk) - int(block["leader"], 16)) // 4 + 1) if inblk else 0
    rec["stop_hit"] = "BLK_STOP" in out.split("BOUNDARY-ALL-GOALS-BEGIN")[-1] if "BOUNDARY-ALL-GOALS-BEGIN" in out else False
    rec["at"] = re.findall(r"BLK-AT-(?:PRE|BODY) (\S+)", out)
    rec["goals"] = out.count("BLK-GOAL") if probes.BEGIN in out else None
    if rec["limit"]:
        rec["outcome"] = "timeout" if rec["limit"] == "time" else "memory"
    elif probes.END not in out:
        rec["outcome"] = "error"
        rec["error"] = [l for l in out.split("\n") if "Error" in l][:3]
    else:
        text, details = goal_record(probes.marked(out))
        rec["raw_path"] = str(d / f"{tag}.out")
        if "No more goals" in out or rec["goals"] == 0:
            rec["outcome"] = "closed-all"
        else:
            ctx, concl = conclusion_text(text)
            rec["pred_class"] = classify(text, "residual").pred_class
            rec["conclusion"] = concl[:600]
            rec["outcome"] = "probe"
    print(tag, rec["outcome"], rec.get("seconds"), rec.get("at"), rec.get("pred_class", ""), flush=True)
    return rec


def main():
    global BR, BUILD, PROOF_DIR, EXTRA_IMPORTS, TRACE_IMPORT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cfg", type=Path, default=W / "build/stock-zisk/cfg.json")
    parser.add_argument("--entries", type=Path, default=W / "build/stock-zisk/block_entries.json")
    parser.add_argument("--build-dir", type=Path, default=BUILD)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--states", type=Path, help="Use generated .v entry modules in this directory.")
    parser.add_argument("--leaders", default="")
    parser.add_argument("--compare", type=Path, help="Compare outcomes against a baseline CSV.")
    parser.add_argument("--import-module", action="append", default=[])
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("JOBS", "24")))
    parser.add_argument("--function")
    parser.add_argument("--proof-dir", type=Path)
    parser.add_argument("--trace-import")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 48:
        parser.error("The worker count must be between 1 and 48.")
    if args.states and not args.states.is_dir():
        parser.error(f"The states directory does not exist: {args.states}")
    EXTRA_IMPORTS = args.import_module
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module) for module in EXTRA_IMPORTS):
        parser.error("An import module has an invalid name.")
    if RULES == "call" and not (W / "ZesuSsz/Automation/Sets/call.v").exists():
        print("call set unavailable", flush=True)
        return 0
    for name in ("function", "proof_dir", "trace_import"):
        if getattr(args, name) is None:
            parser.error("--" + name.replace("_", "-") + " is required.")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", args.trace_import):
        parser.error("The trace import has an invalid name.")
    TRACE_IMPORT = args.trace_import
    PROOF_DIR = args.proof_dir.resolve()
    if not PROOF_DIR.is_dir():
        parser.error(f"The proof directory is absent: {PROOF_DIR}")
    BUILD = args.build_dir.resolve()
    BR = (args.output_dir or BUILD).resolve()
    BR.mkdir(parents=True, exist_ok=True)
    selected = json.loads(args.entries.read_text()) if args.entries.exists() else {}
    if args.states:
        PROOF_DIR = args.states.resolve()
        selected = {leader: candidates[0] for leader, candidates in entries.scan(PROOF_DIR).items()}
    data = entries.blocks(args.cfg, selected, args.function)
    only = set(args.leaders.split(",")) if args.leaders else None
    if only and only - {block["leader"] for block in data}:
        parser.error("A requested leader is absent from the CFG.")
    jobs = [("blocks", b) for b in data if not only or b["leader"] in only]
    result_file = BR / f"results_{RUNV}{'' if RULES == 'v2' else '_' + RULES}_blocks.jsonl"
    if result_file.exists():
        parser.error(f"The output already exists: {result_file}")
    with ThreadPoolExecutor(args.jobs) as executor:
        records = list(executor.map(run_one, jobs))
    table = BR / f"table_{RUNV}_{RULES}.csv"
    analyze.write_table(records, data, table)
    if args.compare:
        differences = analyze.compare_table(table, args.compare)
        print(json.dumps({"outcome_differences": differences}), flush=True)
        return bool(differences)
    return any(record["outcome"] in ("error", "driver-error") for record in records)


if __name__ == "__main__":
    sys.exit(main())
