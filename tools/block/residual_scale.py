#!/usr/bin/env python3
"""The residual step at scale: every block of a function through residual_loop.py
(diagnostic only; it calls no model).

    residual_scale.py plan     --function NAME --callers DIR --bank BANK --out RUN [--blocks B,...]
    residual_scale.py export   --run RUN [--jobs N] [--launch-gap S] [--stop-quiet S] [--blocks B,...]
    residual_scale.py bundle   --run RUN
    residual_scale.py collect  --run RUN [--jobs N] [--blocks B,...]
    residual_scale.py rerun    --run RUN [--jobs N] [--launch-gap S] [--blocks B,...]
    residual_scale.py report   --run RUN [--counts-only]
    residual_scale.py bank-targets --run RUN     (Dune targets of a bank for the plan)
    residual_scale.py bank-args --build-dir DIR --out BANK   (BANK/ARGS.json for a Dune build dir)

plan lists the callers of the function (`Caller<block>.v` in DIR) and copies each one
to RUN/blocks/<block>/caller.v; a block's scratch residual module is named from the
function symbol (`Residual_<symbol>_<block>`). export --bank replaces the plan's bank
(the bank can be built after the plan), and a caller whose source changed after the
plan is copied again before its export. export runs `residual_loop.py export` on each block,
in its own run dir RUN/blocks/<block>/loop, at most N at a time and S seconds apart.
That compile is also the rules-only result of the block: it closes, it ends with pure
goals (they become the goals of the block), it ends with only spatial or refused
goals, or it is stopped before the end. bundle writes RUN/bundles/<block>/ for each
block with goals: the goal order, the task files, the answer paths, and the prompt
for the standing agent of the block. collect checks the answers of each block. rerun
registers the passing lemmas of a block in RUN/residuals (scratch, never the source
tree) and compiles the block again. report compares the rules-only closures with the
closures after the rerun; it prints RESULT lines and never proof text, and with
--counts-only it prints counts only (for held-out sets).
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOOP = HERE / "residual_loop.py"
COORD_VARS = ("COORD_AGENT", "COORD_ROOT")
CALLER = re.compile(r"^Caller(\w+)\.v$")


class ScaleError(ValueError):
    pass


def read_json(path, default=None):
    path = Path(path)
    return json.loads(path.read_text()) if path.exists() else default


def write_json(path, data):
    Path(path).write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def clean_env():
    return {k: v for k, v in os.environ.items() if k not in COORD_VARS}


def callers_of(directory, only=None):
    found = {}
    for path in sorted(Path(directory).iterdir()):
        match = CALLER.match(path.name)
        if match:
            found[match[1]] = path
    if only:
        missing = [b for b in only if b not in found]
        if missing:
            raise ScaleError("No caller for block(s) %s in %s." % (", ".join(missing), directory))
        found = {b: found[b] for b in only}
    if not found:
        raise ScaleError("No Caller<block>.v in %s." % directory)
    return found


def module_for(function, block):
    """The scratch residual module of a block, named from the function symbol:
    `Residual_<symbol>_<block>`, with every character that is not a letter, a digit
    or `_` replaced by `_` (rlp.decodeItem becomes rlp_decodeItem)."""
    return "Residual_%s_%s" % (re.sub(r"[^A-Za-z0-9_]", "_", function), re.sub(r"[^A-Za-z0-9_]", "_", block))


def selected(plan, blocks):
    names = [b["block"] for b in plan["blocks"]]
    if not blocks:
        return names
    unknown = [b for b in blocks if b not in names]
    if unknown:
        raise ScaleError("Block(s) not in the plan: %s." % ", ".join(unknown))
    return [b for b in names if b in blocks]


def loop_dir(run, block):
    return Path(run) / "blocks" / block / "loop"


def run_loop(arguments, log):
    """Run residual_loop.py with ARGUMENTS; its output goes to LOG."""
    with Path(log).open("w") as out:
        proc = subprocess.run([sys.executable, str(LOOP)] + arguments, env=clean_env(), stdout=out,
                              stderr=subprocess.STDOUT)
    return proc.returncode


def slice_memory_file():
    return Path(os.environ.get("ZESU_SLICE_MEMORY_FILE",
                               "/sys/fs/cgroup/user.slice/user-%d.slice/memory.current" % os.getuid()))


def slice_gib():
    try:
        return int(slice_memory_file().read_text().split()[0]) / 2**30
    except (OSError, ValueError, IndexError):
        return None


def paced(blocks, work, jobs, gap, hold_above_gib=None, poll=30.0, fast=None):
    """Run WORK(block) for each block, at most JOBS at a time, starts GAP seconds
    apart; results in block order. With HOLD_ABOVE_GIB, no start while the account
    slice uses more memory. FAST = (below_gib, jobs, gap, above_gib) switches to the
    faster setting while the slice is below BELOW_GIB and back above ABOVE_GIB."""
    results, threads, queue = {}, [], list(blocks)
    last, quick = float("-inf"), False
    tick = 0.02 if gap < 1 else min(poll, 5.0)

    def run(block):
        results[block] = work(block)

    while queue or any(thread.is_alive() for thread in threads):
        gib = slice_gib()
        if fast and gib is not None:
            if gib < fast[0]:
                quick = True
            elif gib > fast[3]:
                quick = False
        limit, spacing = (fast[1], fast[2]) if quick else (jobs, gap)
        alive = sum(thread.is_alive() for thread in threads)
        held = hold_above_gib is not None and (gib or 0) > hold_above_gib
        if queue and alive < max(1, limit) and time.monotonic() - last >= spacing and not held:
            thread = threading.Thread(target=run, args=(queue.pop(0),), daemon=True)
            thread.start()
            threads.append(thread)
            last = time.monotonic()
            continue
        time.sleep(tick if not held else min(poll, 30.0))
    return [results[block] for block in blocks]


# ---- block state ----

def block_state(run, block):
    """The rules-only and the after-rerun state of one block, from its loop manifest."""
    manifest = read_json(loop_dir(run, block) / "MANIFEST.json")
    if manifest is None:
        return dict(block=block, rules="not-run", goals=0, final="not-run")
    export = manifest["exports"][0] if manifest["exports"] else {}
    goals = manifest["goals"]
    statuses = [read_json(loop_dir(run, block) / "goals" / g["id"] / "STATUS.json", {}) for g in goals]
    if export.get("stopped"):
        rules = "stopped"
    elif export.get("returncode") == 0 and not goals:
        rules = "closed"
    elif goals:
        rules = "open"
    elif manifest["skipped"]:
        rules = "open-unexported"
    else:
        rules = "failed"
    reruns = manifest.get("reruns", [])
    state = dict(block=block, rules=rules, goals=len(goals),
                 exact=sum(g.get("reparse") == "exact" for g in goals),
                 passed=sum(s.get("result") == "PASS" for s in statuses),
                 failed=sum(s.get("result") == "FAIL" for s in statuses),
                 skipped=len(manifest["skipped"]),
                 skipped_reasons=sorted({s["reason"] for s in manifest["skipped"]}),
                 export_seconds=export.get("seconds"), export_cpu=export.get("cpu_seconds"),
                 attempts=sum(len(s.get("attempts", [])) for s in statuses),
                 tokens=sum(t.get("tokens") or 0 for s in statuses for t in s.get("attempts", [])))
    if reruns:
        last = reruns[-1]
        state.update(rerun="closed" if last["closed"] else "open", rerun_seconds=last["seconds"],
                     rerun_cpu=last.get("cpu_seconds"),
                     open_again=len(last.get("open_again", [])), new_goals=len(last.get("new_goals", [])))
    state["final"] = "closed" if rules == "closed" or state.get("rerun") == "closed" else "open"
    # CPU of the compile that closed the block: the export, or else the rerun.
    state["closing_cpu"] = (state["export_cpu"] if rules == "closed"
                            else state.get("rerun_cpu") if state.get("rerun") == "closed" else None)
    return state


# ---- commands ----

def cmd_plan(a):
    run = Path(a.out)
    if run.exists() and any(run.iterdir()):
        raise ScaleError("The run dir is not empty: %s" % run)
    callers = callers_of(a.callers, [b for b in a.blocks.split(",") if b] if a.blocks else None)
    blocks = []
    for block, path in callers.items():
        d = run / "blocks" / block
        d.mkdir(parents=True)
        shutil.copyfile(path, d / "caller.v")
        blocks.append(dict(block=block, caller=str(path.resolve()), caller_sha256=sha(path),
                           module=module_for(a.function, block)))
    (run / "residuals").mkdir()
    write_json(run / "PLAN.json", dict(function=a.function, callers=str(Path(a.callers).resolve()),
                                       bank=str(Path(a.bank).resolve()), residuals=str((run / "residuals").resolve()),
                                       blocks=blocks))
    print("planned %d block(s) of %s in %s" % (len(blocks), a.function, run))


def refresh_caller(run, entry):
    """Copy the caller again when its source changed after the plan (a re-render)."""
    source, copy = Path(entry["caller"]), Path(run) / "blocks" / entry["block"] / "caller.v"
    if source.exists() and sha(source) != entry["caller_sha256"]:
        shutil.copyfile(source, copy)
        entry["caller_sha256"] = sha(source)
        return True
    return False


def fast_setting(a):
    """--fast BELOW:JOBS:GAP:ABOVE, for example 150:12:120:170."""
    if not getattr(a, "fast", None):
        return None
    below, jobs, gap, above = a.fast.split(":")
    return float(below), int(jobs), float(gap), float(above)


def cmd_export(a):
    run = Path(a.run)
    plan = read_json(run / "PLAN.json")
    if a.bank:
        plan["bank"] = str(Path(a.bank).resolve())
    if not (Path(plan["bank"]) / "ARGS.json").exists():
        raise ScaleError("The bank has no ARGS.json: %s" % plan["bank"])
    blocks = selected(plan, [b for b in (a.blocks or "").split(",") if b])
    entries = {entry["block"]: entry for entry in plan["blocks"]}
    for block in blocks:
        if not (loop_dir(run, block) / "MANIFEST.json").exists() and refresh_caller(run, entries[block]):
            print("refreshed the caller of %s" % block)
    write_json(run / "PLAN.json", plan)

    def export(block):
        out = loop_dir(run, block)
        if (out / "MANIFEST.json").exists():
            return block, "done"
        arguments = ["export", "--block", block, "--caller", str(run / "blocks" / block / "caller.v"),
                     "--bank", plan["bank"], "--out", str(out), "--jobs", "1", "--claim-gib", str(a.claim_gib)]
        if entries[block].get("module"):
            arguments += ["--module", entries[block]["module"]]
        if a.stop_quiet:
            arguments += ["--stop-quiet", str(a.stop_quiet)]
        code = run_loop(arguments, run / "blocks" / block / "export.out")
        return block, "rc=%d" % code

    for block, outcome in paced(blocks, export, a.jobs, a.launch_gap, a.hold_above_gib, fast=fast_setting(a)):
        print("export %s %s" % (block, outcome))
    print_report(run)


BUNDLE = """# Block {block} of {function}: {count} residual goal(s)

You are the standing prover for this block. Prove the goals in the order below, in
this one session: a later goal often reuses what an earlier one needed.

For each goal:
1. Read the task file. It shows the goal after `intros.` and the rules.
2. Write only the proof script (the text after `Proof.`, ending with one `Qed.`) to
   the answer path.
3. The coordinator runs the check (`residual_scale.py collect`); the result is in the
   feedback path: `PASS`, or `FAIL` with the Rocq error. After a FAIL, write a new
   answer to the same path.

Rules: never use Admitted, admit, Axiom, Abort, give_up, Parameter, or a time limit;
name lemmas by their exact full names; clear hypotheses you do not need before a
solver call. A goal may be false: if you find a counterexample, say so instead of an
answer. Report only one line per goal, `RESULT <goal> PASS|FAIL|FALSE`, never proof text.

Environment notes: iris and ssreflect are loaded, so `rewrite lemma by tac` and
`rewrite <- lemma` do not parse; write `rewrite lemma; [|tac]` or `rewrite -lemma`. The
stdpp bit-vector lemmas take their widths as arguments of type `N`, often implicit
(`bv_unsigned_in_range _ b`). Prove a general helper with `assert` and `clear.` inside
it, then apply it to the goal.

Goals:
{goals}
"""

PROMPT = """You are the standing prover for block {block} of {function}. Read {bundle} and
follow it. Use only the Read and Write tools: read the task and feedback files, write
the answer files. Do not run commands. When every goal has an answer, reply with one
`RESULT <goal> ...` line per goal and nothing else.
"""


def cmd_bundle(a):
    run = Path(a.run)
    plan = read_json(run / "PLAN.json")
    written = 0
    for block in selected(plan, []):
        manifest = read_json(loop_dir(run, block) / "MANIFEST.json")
        if manifest is None:
            continue
        loop = loop_dir(run, block)
        goals = [g for g in manifest["goals"] if g.get("reparse") == "exact"
                 and read_json(loop / "goals" / g["id"] / "STATUS.json", {}).get("result") != "PASS"]
        if not goals:
            continue
        d = run / "bundles" / block
        d.mkdir(parents=True, exist_ok=True)
        lines = ["- `%s`: task `%s`; answer `%s`; feedback `%s`" % (
            g["id"], loop / "tasks" / (g["id"] + ".md"), loop / "answers" / (g["id"] + ".v"),
            loop / "feedback" / (g["id"] + ".txt")) for g in goals]
        (d / "README.md").write_text(BUNDLE.format(block=block, function=plan["function"], count=len(goals),
                                                   goals="\n".join(lines)))
        (d / "AGENT_PROMPT.txt").write_text(PROMPT.format(block=block, function=plan["function"],
                                                          bundle=d / "README.md"))
        written += 1
    print("wrote %d bundle(s) in %s" % (written, run / "bundles"))


def cmd_collect(a):
    run = Path(a.run)
    plan = read_json(run / "PLAN.json")
    blocks = [b for b in selected(plan, [x for x in (a.blocks or "").split(",") if x])
              if (loop_dir(run, b) / "MANIFEST.json").exists()]

    def collect(block):
        return block, run_loop(["collect", "--run", str(loop_dir(run, block)), "--jobs", "1"],
                               run / "blocks" / block / "collect.out")

    for block, code in paced(blocks, collect, a.jobs, 0):
        print("collect %s rc=%d" % (block, code))
    print_report(run)


def cmd_rerun(a):
    run = Path(a.run)
    plan = read_json(run / "PLAN.json")
    blocks = []
    for block in selected(plan, [x for x in (a.blocks or "").split(",") if x]):
        state = block_state(run, block)
        if state["passed"]:
            blocks.append(block)

    def rerun(block):
        loop = loop_dir(run, block)
        caller = run / "blocks" / block / "caller.v"
        code = run_loop(["register", "--run", str(loop), "--residuals", plan["residuals"], "--caller", str(caller)],
                        run / "blocks" / block / "register.out")
        if code:
            return block, "register rc=%d" % code
        code = run_loop(["rerun", "--run", str(loop), "--residuals", plan["residuals"], "--caller", str(caller),
                         "--jobs", "1", "--claim-gib", str(a.claim_gib)], run / "blocks" / block / "rerun.out")
        return block, "rerun rc=%d" % code

    for block, outcome in paced(blocks, rerun, a.jobs, a.launch_gap, a.hold_above_gib, fast=fast_setting(a)):
        print("%s %s" % (block, outcome))
    print_report(run)


BANK_BASE = ("ZesuSsz/Automation2/ResidualExportOn.vo", "ZesuSsz/Automation2/ResidualExport.vo")
ZESU_IMPORT = re.compile(r"^(?:From ZesuSsz )?Require (?:Import|Export) ((?:ZesuSsz\.[\w.]+\s*)+)\.$")


def bank_targets(plan):
    """The Dune targets a bank needs for the plan's callers: `@install`, the export
    switch, and every ZesuSsz module that a caller imports."""
    targets = set(BANK_BASE)
    for entry in plan["blocks"]:
        source = Path(entry["caller"])
        if not source.exists():
            continue
        for line in source.read_text().splitlines():
            match = ZESU_IMPORT.match(line.strip())
            if match:
                for module in match[1].split():
                    targets.add(module.replace(".", "/") + ".vo")
    return ["@install"] + sorted(targets)


LOAD_PATH = (("-Q", "ZesuSsz", "ZesuSsz"), ("-Q", "ZesuStock", "ZesuStock"), ("-Q", "InstrSpecs", "InstrSpecs"),
             ("-Q", "Scaffolding", "Scaffolding"), ("-Q", "MachineMap", "ZesuMachineMap"),
             ("-R", "generated/isla-traces", "IslaTraces"),
             ("-Q", "generated/isla-traces/stock-zisk/decodeItem", "ZesuSsz.Stock.DecodeItem"),
             ("-Q", "generated/isla-traces/stock-zisk/closure", "ZesuSsz.Stock.Closure"),
             ("-Q", "generated/isla-traces/stock-zisk/free", "ZesuSsz.Stock.Free"),
             ("-Q", "generated/evm-sail-coq", "EvmSail"), ("-Q", "generated/evm-sail-coq/rlp", "EvmSailRlp"),
             ("-Q", "generated/sail-stdpp", "SailStdpp"))
COQC = "/home/cody/islaris/_opam/bin/coqc"


def bank_args(build_dir):
    """The coqc arguments of a bank: the Dune build dir's `default` tree with the
    project's load path and warning flags."""
    default = Path(build_dir).resolve() / "default"
    if not (default / "ZesuSsz").is_dir():
        raise ScaleError("No ZesuSsz tree in %s." % default)
    args = [COQC]
    for flag, path, name in LOAD_PATH:
        args += [flag, str(default / path), name]
    # Trace theories that bind_traces.py added for other functions (free, hpDecode, ...). Dune does not
    # copy the `dune` file into the build tree, so the theory name comes from a compiled module's `.glob`.
    known = {name for _, _, name in LOAD_PATH}
    for theory_dir in sorted(p for p in (default / "generated/isla-traces/stock-zisk").glob("*") if p.is_dir()):
        for glob in sorted(theory_dir.glob("*.glob")):
            match = re.search(r"^F(ZesuSsz\.Stock\.\w+)\.\w+$", glob.read_text(errors="replace"), re.M)
            if match and match[1] not in known:
                known.add(match[1])
                args += ["-Q", str(theory_dir), match[1]]
    return args + ["-w", "-notation-overridden", "-w", "-redundant-canonical-projection"]


# ---- report ----

def block_lines(state):
    line = "RESULT %s rules=%s goals=%d exact=%d pass=%d fail=%d unexported=%d" % (
        state["block"], state["rules"], state["goals"], state.get("exact", 0), state.get("passed", 0),
        state.get("failed", 0), state.get("skipped", 0))
    if "rerun" in state:
        line += " rerun=%s" % state["rerun"]
    line += " final=%s" % state["final"]
    if state.get("closing_cpu") is not None:
        line += " cpu=%s" % state["closing_cpu"]
    if state.get("tokens"):
        line += " tokens=%d" % state["tokens"]
    return line


def summary(states):
    total = len(states)
    rules = sum(s["rules"] == "closed" for s in states)
    final = sum(s["final"] == "closed" for s in states)
    counts = {}
    for s in states:
        counts[s["rules"]] = counts.get(s["rules"], 0) + 1
    goals = sum(s["goals"] for s in states)
    passed = sum(s.get("passed", 0) for s in states)
    return ("SUMMARY blocks=%d rules-only-closed=%d rules-plus-residual-closed=%d added=%d goals=%d passed=%d %s"
            % (total, rules, final, final - rules, goals, passed,
               " ".join("%s=%d" % kv for kv in sorted(counts.items()))))


def report_lines(run, counts_only=False):
    run = Path(run)
    plan = read_json(run / "PLAN.json")
    states = [block_state(run, block) for block in selected(plan, [])]
    lines = ["FUNCTION %s" % plan["function"]]
    if not counts_only:
        lines += [block_lines(s) for s in states]
        for block in selected(plan, []):
            results = loop_dir(run, block) / "RESULTS.txt"
            if results.exists():
                lines += ["  " + line for line in results.read_text().splitlines() if line.strip()]
    lines.append(summary(states))
    return lines, states


def print_report(run, counts_only=False):
    lines, states = report_lines(run, counts_only)
    Path(run, "REPORT.txt" if not counts_only else "COUNTS.txt").write_text("\n".join(lines) + "\n")
    if not counts_only:
        write_json(Path(run) / "STATES.json", states)
    for line in lines:
        print(line)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--function", required=True)
    p.add_argument("--callers", required=True)
    p.add_argument("--bank", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--blocks")
    for name in ("export", "collect", "rerun"):
        s = sub.add_parser(name)
        s.add_argument("--run", required=True)
        s.add_argument("--jobs", type=int, default=4)
        s.add_argument("--blocks")
        if name != "collect":
            s.add_argument("--launch-gap", type=float, default=0.0)
            s.add_argument("--hold-above-gib", type=float, default=None,
                           help="hold each start while the account slice uses more memory")
            s.add_argument("--fast", help="BELOW:JOBS:GAP:ABOVE: use JOBS and GAP while the slice is below "
                                          "BELOW GiB, and the base setting again above ABOVE GiB")
            s.add_argument("--claim-gib", type=float, default=8.0)
        if name == "export":
            s.add_argument("--stop-quiet", type=float, default=None)
            s.add_argument("--bank", help="the bank to export against (replaces the plan's bank)")
    t = sub.add_parser("bank-targets")
    t.add_argument("--run", required=True)
    g = sub.add_parser("bank-args")
    g.add_argument("--build-dir", required=True)
    g.add_argument("--out", required=True)
    b = sub.add_parser("bundle")
    b.add_argument("--run", required=True)
    r = sub.add_parser("report")
    r.add_argument("--run", required=True)
    r.add_argument("--counts-only", action="store_true")
    a = ap.parse_args(argv)
    try:
        {"plan": cmd_plan, "export": cmd_export, "bundle": cmd_bundle, "collect": cmd_collect,
         "bank-targets": lambda a: print(" ".join(bank_targets(read_json(Path(a.run) / "PLAN.json")))),
         "bank-args": lambda a: (Path(a.out).mkdir(parents=True, exist_ok=True),
                                 write_json(Path(a.out) / "ARGS.json", bank_args(a.build_dir))),
         "rerun": cmd_rerun, "report": lambda a: print_report(a.run, a.counts_only)}[a.command](a)
    except ScaleError as error:
        sys.exit("residual_scale: %s" % error)


if __name__ == "__main__":
    main()
