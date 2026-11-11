#!/usr/bin/env python3
"""The residual step: export pure residual goals, write task files, check answers,
register the lemmas, and rerun the block (diagnostic only; it calls no model).

    residual_loop.py export   --block B --caller FILE --bank BANK --out RUN [--stop-quiet S]
    residual_loop.py collect  --run RUN
    residual_loop.py register --run RUN [--residuals DIR] [--caller FILE]
    residual_loop.py rerun    --run RUN [--residuals DIR] [--caller FILE]
    residual_loop.py results  --run RUN

export compiles a copy of the block caller that imports
`ZesuSsz.Automation2.ResidualExportOn`. The hooks print one `@@X` record for each
pure conjunct that the package route splits off (`split`) and for each goal still
open at the end of `zesu_block2` (`final`). A record holds the exact source of the
goal's statement (ResidualExport.v): every implicit argument, so every literal
width, is explicit, and the premises are only the facts that the conclusion
reaches. The final records are the goals. A run that ends without them closed
the block, unless it was stopped (--stop-quiet: no new record for S seconds after
the first split record), killed or failed; then the split records are the goals.
The compile runs in one guard scope under `tools/run_registry.py`, and a stop goes
through `run_registry.py stop`. --from-log reuses the log of an earlier export run.
For each goal, export writes RUN/goals/<id>/goal.v (statement and PROOF-SLOT) and
check.sh (one scope, 1 GiB booking), checks that the statement reparses to the
same term (print, reparse, print again: the two texts must be equal), and writes
RUN/tasks/<id>.md for the standing agent of the block.

collect checks each new answer RUN/answers/<id>.v (the proof script only, ending
with one `Qed.`): it fills the slot, runs check.sh, and writes the compiler errors
of a FAIL to RUN/feedback/<id>.txt. After a PASS it minimizes the premises: the
facts whose binders the proof term does not use are dropped, and the smaller
statement is checked again with the same script; it replaces the first one only
when that check passes and it reparses exactly.

register adds the passing lemmas to ZesuSsz/Residuals/Block800d<B>.v through
tools/residuals/render_residual_module.py (existing lemmas stay) and adds the
module import to the caller. rerun compiles that module and the caller copy with
the export switch: it records whether the block closes, and the goals still open
become the next round of goals.

results prints one RESULT line per goal: state, reparse, premises, attempts. It
never prints proof text, so the lines can go to rule writers.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import queue
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/residuals"))
sys.path.insert(0, str(ROOT / "tools/block"))
import render_residual_module as rrm  # noqa: E402
import residual_package as pkg  # noqa: E402

SWITCH = "Require Import ZesuSsz.Automation2.ResidualExportOn."
EXPORT_MODULE = "Require Import ZesuSsz.Automation2.ResidualExport."
CORE_IMPORT = "Require Import ZesuSsz.Automation2.All."
SWITCH_MODULES = re.compile(r"ZesuSsz\.Automation2\.(?:DiagnosticsOn|ResidualExportOn)\b")
IMPORT_LINE = re.compile(r"^(?:Require (?:Import|Export) |From \w+ Require )")
SCOPE_LINE = "Local Open Scope Z_scope."
STAMP = re.compile(r"^(\d+\.\d+) (.*)$")
STOP_PREFIXES = ("@@", "Chars ", "Warning", "File ", "Error", "Tactic call", "Finished ", "[", "Closed under",
                 "Axioms:", "1 goal", "No more", "===")
FORBIDDEN = re.compile(r"\b(Admitted|admit|Axiom|Abort|timeout|Timeout|give_up|Parameter)\b")
COORD_VARS = ("COORD_AGENT", "COORD_ROOT")
CHECK_CLAIM = 1 << 30
GUARD = ROOT / "tools/resource_guard.sh"
REGISTRY = ROOT / "tools/run_registry.py"
RESIDUALS = ROOT / "ZesuSsz/Residuals"


class LoopError(ValueError):
    pass


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def read_json(path, default=None):
    path = Path(path)
    return json.loads(path.read_text()) if path.exists() else default


def write_json(path, data):
    Path(path).write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")


# ---- caller text ----

def import_index(lines):
    found = [i for i, line in enumerate(lines) if IMPORT_LINE.match(line)]
    if not found:
        raise LoopError("The caller has no import line.")
    return found[-1]


def export_caller(source, residual=None):
    """The caller with the export switch imported last. RESIDUAL, when given, is
    the import line of the block's residual module copy (replacing any import of
    the block's own residual module)."""
    lines = [line for line in source.split("\n") if not SWITCH_MODULES.search(line)]
    if residual:
        lines = [line for line in lines if not re.match(r"Require Import ZesuSsz\.Residuals\.Block800d", line)]
    last = import_index(lines)
    lines[last + 1:last + 1] = ([residual] if residual else []) + [SWITCH]
    return "\n".join(lines)


def caller_header(source, block):
    """The import lines of a goal file: the caller's imports without the switch
    modules and without the block's own residual module, then Z_scope."""
    own = "Require Import ZesuSsz.Residuals.Block800d%s." % block
    lines = source.split("\n")
    header = [line for line in lines[:import_index(lines) + 1]
              if IMPORT_LINE.match(line) and not SWITCH_MODULES.search(line) and line != own]
    for line in header:
        if not rrm.HEADER_LINE.match(line):
            raise LoopError("The caller import is not a plain import line: %s" % line)
    return header + [SCOPE_LINE]


# ---- export records ----

def records(lines):
    """Join wrapped output lines into one (stamp, text) record per `@@X` line.
    A line printed more than one second after the record started is never part
    of it (for example a guard message after the last record)."""
    current = None
    for raw in lines:
        raw = raw.rstrip("\n")
        match = STAMP.match(raw)
        stamp, text = (float(match.group(1)), match.group(2)) if match else (None, raw)
        later = stamp is not None and current is not None and current[0] is not None and stamp - current[0] > 1.0
        if text.startswith("@@"):
            if current is not None:
                yield current
            current = [stamp, text]
        elif current is not None and text.strip() and not text.startswith(STOP_PREFIXES) and not later:
            current[1] += " " + text.strip()
        else:
            if current is not None:
                yield current
            current = None
    if current is not None:
        yield current


def parse_export(lines):
    """Return the export records of a log: pure goals and skip lines, in log order."""
    out, current = [], None
    for stamp, text in records(lines):
        if not text.startswith("@@X "):
            continue
        body = text[4:]
        if body.startswith("skip "):
            parts = body.split(" ", 2)
            out.append(dict(kind=parts[1], status="skip", reason=parts[2] if len(parts) > 2 else "", stamp=stamp))
        elif body.startswith("begin "):
            current = dict(kind=body[6:].strip(), status="pure", stamp=stamp, binders=[],
                           conclusion_definitions=[], counts={}, statement=None)
        elif current is None:
            continue
        elif body.startswith("binders"):
            current["binders"] = body.split()[1:]
        elif body.startswith("conclusion-definitions"):
            current["conclusion_definitions"] = body.split()[1:]
        elif body.startswith("counts "):
            current["counts"] = {k: int(v) for k, v in (x.split("=") for x in body.split()[1:])}
        elif body.startswith("stmt "):
            current["statement"] = body[5:].strip()
        elif body == "end":
            if current["statement"]:
                out.append(current)
            current = None
    return out


def select_goals(found, block, closed):
    """The goals of one export run. Final records are the goals open at the end.
    A run without them that closed the block has no goals; a run without them that
    did not close it (stopped, killed, or failed) gives its split records.
    Equal statements merge."""
    finals = [r for r in found if r["kind"] == "final"]
    source = "final" if finals or closed else "split"
    goals, seen = [], {}
    for record in found:
        if record["status"] != "pure" or record["kind"] != source:
            continue
        key = sha(record["statement"])
        if key in seen:
            seen[key]["copies"] += 1
            continue
        goal = dict(id=None, name="residual_%s_%s" % (block, key[:16]), statement=record["statement"],
                    source=source, copies=1, binders=record["binders"], counts=record["counts"],
                    conclusion_definitions=record["conclusion_definitions"])
        seen[key] = goal
        goals.append(goal)
    split_only = [r for r in found if r["status"] == "pure" and r["kind"] == "split"
                  and sha(r["statement"]) not in seen]
    return goals, source, len(split_only)


# ---- goal files ----

def goal_text(header, name, statement):
    return "%s\n\nLemma %s :\n  %s.\nProof.\n%s\nAdmitted.\n" % ("\n".join(header), name, statement, pkg.SLOT)


def goal_head(goal_v):
    return goal_v[:goal_v.index("(* PROOF-SLOT")]


def roundtrip_text(header, statement):
    """Reparse STATEMENT and print it again with the exporter, then show the
    goal after `intros.` with the default printer (the named hypotheses that a
    proof starts from). Kept out of goal.v: goal.v holds only the lemma."""
    return ("%s\n%s\nSet Printing Width 120.\nSet Printing Depth 1000000.\nGoal %s.\n"
            "ltac2:(ZesuSsz.Automation2.ResidualExport.zesu_export_roundtrip ()).\nintros.\nShow.\nAbort.\n"
            % ("\n".join(header), EXPORT_MODULE, statement))


def answer_problems(answer):
    if FORBIDDEN.search(answer):
        return "the answer uses a forbidden command"
    if answer.count("Qed.") != 1 or not answer.rstrip().endswith("Qed."):
        return "the answer must end with exactly one Qed."
    if re.search(r"^\s*(Lemma|Theorem|Proof)\b", answer, re.M):
        return "the answer must hold only the proof script"
    return None


def minimize_text(header, name, statement, answer):
    """The checked proof made transparent, then the minimized statement."""
    script = answer.rstrip()
    script = script[:-len("Qed.")] + "Defined."
    return ("%s\n%s\n\nLemma %s :\n  %s.\nProof.\n%s\n\nGoal %s.\nintros.\n"
            "ltac2:(ZesuSsz.Automation2.ResidualExport.zesu_export_minimized_of '(@%s)).\nAbort.\n"
            % ("\n".join(header), EXPORT_MODULE, name, statement, script, statement, name))


def readable(log_text):
    """The goal as `Show` printed it in a round-trip log: the named hypotheses,
    the separator and the conclusion (time stamps removed)."""
    lines = [STAMP.sub(r"\2", line) for line in log_text.split("\n")]
    try:
        start = next(i for i, line in enumerate(lines) if line.strip() == "1 goal")
    except StopIteration:
        return ""
    out = []
    for line in lines[start + 1:]:
        if line.strip() and not line.startswith(" "):
            break
        out.append(line[2:] if line.startswith("  ") else line.strip())
    return "\n".join(out).strip()


def last_record(log_text, label):
    found = [text for _, text in records(log_text.split("\n")) if text.startswith(label)]
    return found[-1][len(label):].strip() if found else None


def first_difference(left, right):
    for i, (a, b) in enumerate(zip(left, right)):
        if a != b:
            return i
    return min(len(left), len(right)) if len(left) != len(right) else None


def errors_of(log_text, limit=40):
    lines = log_text.split("\n")
    keep = [i for i, line in enumerate(lines) if line.startswith(("File ", "Error"))]
    if not keep:
        return "\n".join(lines[-limit:])
    start = keep[0]
    return "\n".join(lines[start:start + limit])


# ---- compiles ----

def bank_args(bank):
    bank = Path(bank)
    args = [a for a in json.loads((bank / "ARGS.json").read_text()) if a != "-time"]
    lib = bank / "install/default/lib"
    if not lib.exists():
        zesu = next(args[i + 1] for i, a in enumerate(args) if a == "-Q" and args[i + 2] == "ZesuSsz")
        lib = Path(zesu).parents[1] / "install/default/lib"
    return args, str(lib)


def clean_env(extra=None):
    env = {k: v for k, v in os.environ.items() if k not in COORD_VARS}
    env.update(extra or {})
    return env


def scoped(path, tag, args, ocamlpath, claim=CHECK_CLAIM, run_id=None, watch=None, extra_args=(), keep=False):
    """Compile PATH in its own guard scope, stamping each output line with the
    seconds since start into PATH.log. WATCH(text, elapsed) may return True to stop
    the run through run_registry.py (RUN_ID required); it is also called with
    text None every few seconds while the compiler prints nothing. Returns a
    result dict."""
    path = Path(path)
    log = path.with_suffix(".log")
    command = [str(GUARD), "scope", tag, "--"] + list(args) + list(extra_args) + [path.name]
    if run_id:
        command = [sys.executable, str(REGISTRY), "run", "--id", run_id, "--kind", "diagnostic",
                   "--owner", "residual-loop", "--"] + command
    env = clean_env(dict(OCAMLPATH=ocamlpath, ZESU_WRITER_ID="residual-loop-" + tag,
                         ZESU_MODULE_CLAIM_BYTES=str(claim)))
    for cache in path.parent.glob(".*.cache"):
        cache.unlink()
    start = time.monotonic()
    stopped = False
    with log.open("w") as out:
        proc = subprocess.Popen(command, cwd=path.parent, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        lines = queue.Queue()

        def read():
            for raw in proc.stdout:
                lines.put(raw)

        reader = threading.Thread(target=read, daemon=True)
        reader.start()
        while True:
            try:
                raw = lines.get(timeout=5)
            except queue.Empty:
                raw = None
                if not reader.is_alive() and lines.empty():
                    break
            elapsed = time.monotonic() - start
            line = None
            if raw is not None:
                line = raw.decode("utf-8", "replace").rstrip("\n")
                out.write("%.3f %s\n" % (elapsed, line))
                out.flush()
            if watch and not stopped and watch(line, elapsed):
                stopped = True
                subprocess.run([sys.executable, str(REGISTRY), "stop", "--run-id", run_id],
                               env=clean_env(), capture_output=True)
        code = proc.wait()
    for suffix in ((".glob",) if keep else (".vo", ".vok", ".vos", ".glob")):
        path.with_suffix(suffix).unlink(missing_ok=True)
    (path.parent / ("." + path.stem + ".aux")).unlink(missing_ok=True)
    for cache in path.parent.glob(".*.cache"):
        cache.unlink()
    return dict(returncode=code, seconds=round(time.monotonic() - start, 1), stopped=stopped, log=str(log))


class QuietWatch:
    """Stop when SECONDS pass with no new `@@X` line after the first split record."""

    def __init__(self, seconds):
        self.seconds, self.seen, self.last = seconds, False, None

    def __call__(self, line, elapsed):
        text = STAMP.sub(r"\2", line or "")
        if "@@X " in text:
            self.last = elapsed
            if "@@X begin split" in text or "@@X skip split" in text:
                self.seen = True
        return self.seen and self.last is not None and elapsed - self.last >= self.seconds


def check_script(gid, args, ocamlpath):
    return pkg.check_sh(gid, args, str(GUARD), os.environ.get("PATH", ""), ocamlpath)


def run_check(directory):
    directory = Path(directory)
    start = time.monotonic()
    proc = subprocess.run(["./check.sh"], cwd=directory, env=clean_env(), capture_output=True, text=True)
    verdict = "PASS" if proc.returncode == 0 and "PASS" in proc.stdout else "FAIL"
    return verdict, round(time.monotonic() - start, 1)


# ---- steps ----

def write_goal(run, goal, header, args, ocamlpath):
    d = Path(run) / "goals" / goal["id"]
    d.mkdir(parents=True, exist_ok=True)
    (d / "goal.v").write_text(goal_text(header, goal["name"], goal["statement"]))
    (d / "roundtrip.v").write_text(roundtrip_text(header, goal["statement"]))
    (d / "check.sh").write_text(check_script(goal["id"], args, ocamlpath))
    (d / "check.sh").chmod(0o755)
    return d


def reparse(directory, tag, statement, args, ocamlpath):
    """Compile roundtrip.v; the statement reparses exactly when the exporter
    prints the reparsed term as the same text."""
    result = scoped(Path(directory) / "roundtrip.v", tag, args, ocamlpath)
    text = Path(result["log"]).read_text(errors="replace")
    again = last_record(text, "@@X roundtrip ")
    if again is None:
        return dict(reparse="fails", seconds=result["seconds"], readable="")
    if again == statement:
        return dict(reparse="exact", seconds=result["seconds"], readable=readable(text))
    return dict(reparse="differs", seconds=result["seconds"], readable=readable(text),
                first_difference=first_difference(statement, again))


TASK = """# Residual goal {id} (block {block})

Write the proof script of the lemma below to `{answer}`: only the text that goes
after `Proof.`, ending with one `Qed.`. The coordinator checks it; a FAIL comes back
in `{feedback}`.

Rules:
- Start with `intros.`: the hypotheses then have the binder names of the statement.
- End with `Qed.`. Never use Admitted, admit, Axiom, Abort, give_up, Parameter, or a time limit.
- Name every lemma by its exact full name. If a name is not found, do not guess a prefix.
- Use only the hypotheses you need: clear the others before a solver call.
- The statement holds only the facts that its conclusion reaches; it is a goal that the
  block automation left open, and it may be false. Say so if you find a counterexample.

Lemma name: `{name}`
Premises: {premises} of {props} facts in the block context ({small} small enough to state).

## Goal after `intros.` (default printer; literal widths may be hidden)

```
{readable}
```

The exact source of the statement, with every width explicit, is in `{goal}`.
Read it only when a literal width matters.

## Imports

```
{header}
```
"""


def write_task(run, block, goal, header):
    run = Path(run)
    (run / "tasks").mkdir(exist_ok=True)
    (run / "answers").mkdir(exist_ok=True)
    (run / "feedback").mkdir(exist_ok=True)
    counts = goal.get("counts", {})
    text = TASK.format(id=goal["id"], block=block, answer=run / "answers" / (goal["id"] + ".v"),
                       feedback=run / "feedback" / (goal["id"] + ".txt"), name=goal["name"],
                       premises=counts.get("kept", "?"), props=counts.get("props", "?"),
                       small=counts.get("small", "?"), readable=goal.get("readable") or "(not available)",
                       goal=run / "goals" / goal["id"] / "goal.v", header="\n".join(header))
    (run / "tasks" / (goal["id"] + ".md")).write_text(text)


def write_task_index(run, manifest):
    """RUN/tasks/README.md: the goals of the block in order, for its standing agent."""
    run = Path(run)
    open_goals = [g for g in manifest["goals"] if g.get("reparse") == "exact"
                  and read_json(run / "goals" / g["id"] / "STATUS.json", {}).get("result") != "PASS"]
    if not open_goals:
        return
    (run / "tasks").mkdir(exist_ok=True)
    lines = ["# Block %s: residual goals" % manifest["block"], "",
             "Prove the goals in this order, one answer file each. Keep this session for all of them.", ""]
    lines += ["- `%s.md` (round %d)" % (g["id"], g.get("round", 1)) for g in open_goals]
    (run / "tasks" / "README.md").write_text("\n".join(lines) + "\n")


def next_ids(goals, block, count):
    used = [int(g["id"].rsplit("-", 1)[1]) for g in goals]
    start = max(used, default=0) + 1
    return ["%s-%d" % (block, start + i) for i in range(count)]


def export_round(run, manifest, caller_source, log_text, closed, jobs):
    """Add the goals of one export log to the manifest; write their files."""
    block = manifest["block"]
    found = parse_export(log_text.split("\n"))
    goals, source, split_only = select_goals(found, block, closed)
    known = {}
    for g in manifest["goals"]:
        known[g["name"]] = g["id"]
        known[g.get("final_name", g["name"])] = g["id"]
    fresh = [g for g in goals if g["name"] not in known]
    again = [known[g["name"]] for g in goals if g["name"] in known]
    for goal, gid in zip(fresh, next_ids(manifest["goals"], block, len(fresh))):
        goal.update(id=gid, round=manifest["rounds"])
    header = caller_header(caller_source, block)
    args, ocamlpath = bank_args(manifest["bank"])

    def prepare(goal):
        d = write_goal(run, goal, header, args, ocamlpath)
        goal.update(reparse(d, "rt-" + goal["id"], goal["statement"], args, ocamlpath))
        if goal["reparse"] == "exact":
            write_task(run, block, goal, header)
        status = dict(attempts=[], result="OPEN" if goal["reparse"] == "exact" else "REFUSED")
        write_json(d / "STATUS.json", status)
        return goal

    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        list(pool.map(prepare, fresh))
    manifest["goals"].extend(fresh)
    manifest["skipped"].extend(dict(kind=r["kind"], reason=r["reason"], round=manifest["rounds"])
                               for r in found if r["status"] == "skip")
    return dict(source=source, records=len(found), new_goals=[g["id"] for g in fresh], open_again=again,
                closed_after_split=split_only if source == "final" else None)


def cmd_export(a):
    run = Path(a.out)
    if run.exists() and any(run.iterdir()):
        raise LoopError("The run dir is not empty: %s" % run)
    (run / "export").mkdir(parents=True)
    caller = Path(a.caller).read_text()
    block = a.block
    manifest = dict(block=block, bank=str(Path(a.bank).resolve()), caller=str(Path(a.caller).resolve()),
                    caller_sha256=sha(caller), rounds=1, goals=[], skipped=[], exports=[], reruns=[])
    target = run / "export" / ("Export%s.v" % block)
    target.write_text(export_caller(caller))
    args, ocamlpath = bank_args(a.bank)
    run_id = "residual-export-%s-%d" % (block, time.time_ns())
    if a.from_log:
        # Reuse the log of an earlier export run that did not close the block.
        shutil.copyfile(a.from_log, target.with_suffix(".log"))
        result = dict(returncode=None, seconds=None, stopped=False, log=str(target.with_suffix(".log")),
                      from_log=str(Path(a.from_log).resolve()))
    else:
        watch = QuietWatch(a.stop_quiet) if a.stop_quiet else None
        result = scoped(target, "export-" + block, args, ocamlpath, claim=int(a.claim_gib * (1 << 30)),
                        run_id=run_id, watch=watch)
    log_text = Path(result["log"]).read_text(errors="replace")
    closed = result["returncode"] == 0 and not result["stopped"]
    summary = export_round(run, manifest, caller, log_text, closed, a.jobs)
    manifest["exports"].append(dict(result, run_id=run_id, round=1, **summary))
    write_json(run / "MANIFEST.json", manifest)
    write_task_index(run, manifest)
    print_results(run)


def cmd_collect(a):
    run = Path(a.run)
    manifest = read_json(run / "MANIFEST.json")
    header = caller_header(Path(manifest["caller"]).read_text(), manifest["block"])
    args, ocamlpath = bank_args(manifest["bank"])

    def collect(goal):
        d = run / "goals" / goal["id"]
        status = read_json(d / "STATUS.json")
        answer_path = run / "answers" / (goal["id"] + ".v")
        if goal["reparse"] != "exact" or not answer_path.exists():
            return
        answer = answer_path.read_text()
        digest = sha(answer)
        if any(t["sha256"] == digest for t in status["attempts"]):
            return
        meta = read_json(answer_path.with_suffix(".json"), {})
        problem = answer_problems(answer)
        if problem:
            verdict, seconds = "FAIL", 0.0
            (run / "feedback" / (goal["id"] + ".txt")).write_text("FAIL: %s\n" % problem)
        else:
            (d / "proof.v").write_text(goal_head((d / "goal.v").read_text()) + answer.strip() + "\n")
            verdict, seconds = run_check(d)
            log = (d / "check.log").read_text(errors="replace") if (d / "check.log").exists() else ""
            (run / "feedback" / (goal["id"] + ".txt")).write_text(
                "PASS\n" if verdict == "PASS" else "FAIL\n" + errors_of(log) + "\n")
        status["attempts"].append(dict(sha256=digest, result=verdict, seconds=seconds,
                                       tokens=meta.get("tokens")))
        if verdict == "PASS":
            status["result"] = "PASS"
            status["minimized"] = minimize(run, d, goal, answer, header, args, ocamlpath)
        elif status["result"] != "PASS":
            status["result"] = "FAIL"
        write_json(d / "STATUS.json", status)

    with ThreadPoolExecutor(max_workers=max(1, a.jobs)) as pool:
        list(pool.map(collect, manifest["goals"]))
    write_json(run / "MANIFEST.json", manifest)
    print_results(run)


def minimize(run, d, goal, answer, header, args, ocamlpath):
    """Drop the premises that the proof term does not use, and check again."""
    m = d / ("min-" + sha(answer)[:12])
    m.mkdir(exist_ok=True)
    (m / "minimize.v").write_text(minimize_text(header, goal["name"], goal["statement"], answer))
    result = scoped(m / "minimize.v", "min-" + goal["id"], args, ocamlpath)
    text = Path(result["log"]).read_text(errors="replace")
    smaller = last_record(text, "@@X minimized ")
    binders = (last_record(text, "@@X binders") or "").split()
    if smaller is None:
        return dict(state="not-run", seconds=result["seconds"])
    if smaller == goal["statement"]:
        return dict(state="unchanged", binders=len(goal["binders"]))
    name = "residual_%s_%s" % (goal["id"].split("-")[0], sha(smaller)[:16])
    (m / "goal.v").write_text(goal_text(header, name, smaller))
    (m / "proof.v").write_text(goal_head((m / "goal.v").read_text()) + answer.strip() + "\n")
    (m / "roundtrip.v").write_text(roundtrip_text(header, smaller))
    (m / "check.sh").write_text(check_script(goal["id"] + "-min", args, ocamlpath))
    (m / "check.sh").chmod(0o755)
    verdict, _ = run_check(m)
    trip = reparse(m, "rt-" + goal["id"] + "-min", smaller, args, ocamlpath)
    state = dict(state="kept" if verdict == "PASS" and trip["reparse"] == "exact" else "rejected",
                 check=verdict, reparse=trip["reparse"], binders_before=len(goal["binders"]),
                 binders_after=len(binders), name=name)
    if state["state"] == "kept":
        for f in ("goal.v", "proof.v"):
            shutil.copyfile(d / f, d / ("full-" + f))
            shutil.copyfile(m / f, d / f)
        goal.update(final_name=name, final_statement=smaller)
    return state


def module_path(residuals, block):
    return Path(residuals) / ("%s.v" % rrm.module_name(block))


def module_text(block, existing, goal_dirs):
    """The residual module with the lemmas of GOAL_DIRS added to EXISTING (text or None)."""
    if existing:
        _, header, rows = rrm.parse_module(existing)
    else:
        header, rows = None, []
    names = {row["name"] for row in rows}
    labels = {row["goal"] for row in rows}
    used = [int(label.rsplit("-", 1)[1]) for label in labels]
    own = "Require Import ZesuSsz.Residuals.%s." % rrm.module_name(block)
    added = []
    for directory in goal_dirs:
        imports, lemma, goal_sha, proof_sha = rrm.read_goal(Path(directory))
        imports = [line for line in imports if line != own]
        header = imports if header is None else rrm.merged_header(header, imports, Path(directory).name)
        name = re.match(r"Lemma (\S+)", lemma)[1]
        if name in names:
            continue
        label = Path(directory).name
        if label in labels:
            label = "%s-%d" % (block, max(used, default=0) + 1)
        used.append(int(label.rsplit("-", 1)[1]))
        labels.add(label)
        names.add(name)
        rows.append(dict(goal=label, goal_sha=goal_sha, proof_sha=proof_sha, name=name, body=lemma))
        added.append(name)
    if not rows:
        raise LoopError("No lemma to register.")
    text = rrm.render_module(block, rrm.pin_shared_modules(header, rows), rows)
    rrm.parse_module(text)
    return text, added


def cmd_register(a):
    run = Path(a.run)
    manifest = read_json(run / "MANIFEST.json")
    block = manifest["block"]
    passing = [g for g in manifest["goals"]
               if read_json(run / "goals" / g["id"] / "STATUS.json", {}).get("result") == "PASS"]
    target = module_path(a.residuals, block)
    existing = target.read_text() if target.exists() else None
    text, added = module_text(block, existing, [run / "goals" / g["id"] for g in passing])
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
    caller = Path(a.caller or manifest["caller"])
    source = caller.read_text()
    line = "Require Import ZesuSsz.Residuals.%s." % rrm.module_name(block)
    if line not in source.split("\n"):
        lines = source.split("\n")
        lines.insert(import_index(lines) + 1, line)
        caller.write_text("\n".join(lines))
    manifest.setdefault("registered", []).append(dict(module=str(target), caller=str(caller), added=added))
    write_json(run / "MANIFEST.json", manifest)
    print("registered %d lemma(s) in %s" % (len(added), target))


def cmd_rerun(a):
    run = Path(a.run)
    manifest = read_json(run / "MANIFEST.json")
    block = manifest["block"]
    k = len(manifest["reruns"]) + 1
    d = run / ("rerun-%d" % k)
    (d / "lib").mkdir(parents=True)
    module = rrm.module_name(block)
    source_module = module_path(a.residuals, block)
    args, ocamlpath = bank_args(manifest["bank"])
    extra = []
    residual = None
    if source_module.exists():
        shutil.copyfile(source_module, d / "lib" / (module + ".v"))
        extra = ["-Q", str(d / "lib"), "ResidualLoop"]
        build = scoped(d / "lib" / (module + ".v"), "rerun-lib-" + block, args, ocamlpath,
                       extra_args=extra, keep=True)
        if build["returncode"] != 0:
            raise LoopError("The residual module does not compile: %s" % build["log"])
        residual = "Require Import ResidualLoop.%s." % module
    caller = Path(a.caller or manifest["caller"]).read_text()
    target = d / ("Rerun%s.v" % block)
    target.write_text(export_caller(caller, residual))
    result = scoped(target, "rerun-" + block, args, ocamlpath, claim=int(a.claim_gib * (1 << 30)),
                    run_id="residual-rerun-%s-%d" % (block, time.time_ns()), extra_args=extra)
    log_text = Path(result["log"]).read_text(errors="replace")
    closed = result["returncode"] == 0
    manifest["rounds"] += 1
    summary = export_round(run, manifest, caller, log_text, closed, a.jobs) if not closed else {}
    manifest["reruns"].append(dict(result, round=manifest["rounds"], closed=closed, **summary))
    write_json(run / "MANIFEST.json", manifest)
    write_task_index(run, manifest)
    print_results(run)


def result_lines(run):
    run = Path(run)
    manifest = read_json(run / "MANIFEST.json")
    lines = []
    for goal in manifest["goals"]:
        status = read_json(run / "goals" / goal["id"] / "STATUS.json", {})
        attempts = status.get("attempts", [])
        tokens = [t.get("tokens") for t in attempts if t.get("tokens") is not None]
        minimized = status.get("minimized") or {}
        used = minimized.get("binders_after") if minimized.get("state") == "kept" else None
        tier = "local-definition" if goal.get("conclusion_definitions") else "matchable"
        lines.append("RESULT %s %s source=%s reparse=%s binders=%d%s attempts=%d tokens=%s tier=%s" % (
            goal["id"], status.get("result", "OPEN"), goal["source"], goal["reparse"], len(goal["binders"]),
            " minimized=%d" % used if used is not None else "", len(attempts),
            sum(tokens) if tokens else "-", tier))
    for rerun in manifest["reruns"]:
        state = "closed" if rerun["closed"] else "open open_again=%s new=%s" % (
            ",".join(rerun.get("open_again", [])) or "-", ",".join(rerun.get("new_goals", [])) or "-")
        lines.append("RESULT %s rerun round=%d %s seconds=%s" % (
            manifest["block"], rerun["round"], state, rerun["seconds"]))
    return lines


def print_results(run):
    lines = result_lines(run)
    Path(run, "RESULTS.txt").write_text("\n".join(lines) + "\n")
    for line in lines:
        print(line)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    e = sub.add_parser("export")
    e.add_argument("--block", required=True)
    e.add_argument("--caller", required=True)
    e.add_argument("--bank", required=True)
    e.add_argument("--out", required=True)
    e.add_argument("--stop-quiet", type=float, default=None)
    e.add_argument("--from-log", help="reuse the log of an earlier export run instead of compiling")
    e.add_argument("--claim-gib", type=float, default=8.0)
    e.add_argument("--jobs", type=int, default=8)
    c = sub.add_parser("collect")
    c.add_argument("--run", required=True)
    c.add_argument("--jobs", type=int, default=8)
    r = sub.add_parser("register")
    r.add_argument("--run", required=True)
    r.add_argument("--residuals", default=str(RESIDUALS))
    r.add_argument("--caller")
    rr = sub.add_parser("rerun")
    rr.add_argument("--run", required=True)
    rr.add_argument("--residuals", default=str(RESIDUALS))
    rr.add_argument("--caller")
    rr.add_argument("--claim-gib", type=float, default=8.0)
    rr.add_argument("--jobs", type=int, default=8)
    s = sub.add_parser("results")
    s.add_argument("--run", required=True)
    a = ap.parse_args(argv)
    try:
        {"export": cmd_export, "collect": cmd_collect, "register": cmd_register, "rerun": cmd_rerun,
         "results": lambda a: print_results(a.run)}[a.command](a)
    except LoopError as error:
        sys.exit("residual_loop: %s" % error)


if __name__ == "__main__":
    main()
