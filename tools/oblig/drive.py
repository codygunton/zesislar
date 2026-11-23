#!/usr/bin/env python3
"""Production driver of one function's obligations, model-free half (plan A7). It calls no model:
tools/oblig/drive_kernel.py spawns the provers and calls `step` to check their answers.

    drive.py step --function F --run RUN [--limit N] [--jobs J]

step loops over `route.py next` until a pass changes nothing, and performs every routed action
that needs no model:
- unblock: a `goal` or `meaning` obligation `blocked-on` a closed obligation is blocked on its next
  unmet dependency, or becomes `derived` (a `meaning` goal's dependencies are the `deps` of its
  MANIFEST row; goal.v states them as hypotheses `<dep>_statement`, so the goal is not rewritten).
  When goal.v is unchanged since it was filed, the `derived` event carries the last falsity verdict
  (tier `falsify`, its report as artifact), so the check does not run twice on one statement.
- falsify: tools/oblig/falsify.py on goal.v (on FALSIFY.v when the goal dir holds one: the
  statement without the dependency hypotheses); tier `falsify`, state `false` on a kernel-checked
  hit, class `unchecked` when the binder types are outside its range and the goal has no class.
- mechanical: the attempt `mechanical` (CONTROL_TACTIC of tools/residuals/residual_package.py) is
  registered and written as a `proved` answer, then checked like a model's.
- check: every `running` attempt whose answer (RUN.../answers/<goal>.json, written by `answer` of
  this module with the attempt's prompt_sha256) is in: `proved` goes through
  `residual_loop.py collect` (the stand-alone check.sh route) and becomes `closed` or `failed`
  compile_error; `false` is checked with falsify.py's kernel refutation on the binder values the
  answer names (`false`, else failed bad_counterexample).
The actions rerun, derive, package, test, check (decisions), decide, diagnose, reconsider, owner
and spin are listed for the region owner or the coordinator, never executed.

Output: one `done` line with the counts of this call, then one line per item left:
`MODEL <id> tier=<tier> <why>` (for drive_kernel.run_round), `RUNNING <id> tier=<tier>` (an attempt
without its answer), `LIST <id> <action> [tier=<tier>] <why>` (not this driver's), and `UNLOCATED <id>`
(no residual_loop run dir under RUN holds the goal).

Obligation files: every residual_loop.py run dir under RUN (MANIFEST.json and goals/). A goal of a
block run is `<F>/goal/<block>-<16 hex of sha256(statement)>`; a goal of a run whose block is
`meaning` is `<F>/meaning/<goal name>`. Its task file is RUN.../package/<goal>/TASK-<tier>.md
(package.py) when present, else RUN.../tasks/<goal>.md; prompts sent are kept in
RUN.../prompts/<goal>/<tier>-<attempt>.md.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys
import threading

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
import store  # noqa: E402
import route  # noqa: E402
import package  # noqa: E402
import replay  # noqa: E402
import residual_loop as rl  # noqa: E402

MECHANICAL = "mechanical"
MECHANICAL_PROOF = replay.MECHANICAL_PROOF
MAX_PASSES = 20
FAILED_VERDICTS = ("give_up", "need_context", "malformed")
EXACT_HEADING = "## Lemma (exact source of goal.v)"
NO_TOOLS = """You are a Rocq prover. Everything you need is in this message: do not call any tool and do not
read or write any file. Where the task below says to write the proof script to a file, put that
text in the `proof` field of your answer instead. Your whole reply is one JSON object in the answer
form at the end, with no other text and no code fence.

"""
ERROR_HEAD = "\n## Your previous answer failed\n\n"
CONTEXT_HEAD = "\n## Context you asked for\n\n"
TRUNCATED = "\n[... truncated]"
MALFORMED_LINE = "Reply with the bare JSON object only.\n\n"
TOO_LARGE = "too-large"


def sha(text):
    return store.sha256_bytes(text.encode())


def tier_rows(path=route.TIERS_FILE):
    data = store.read_json(path) or {}
    return {row["name"]: row for row in data.get("tiers", [])}


def max_prompt_bytes(tier, cls=None):
    """The prompt bound of goal class CLS at TIER (replay.prompt_bound: the class's routing.json
    `max_prompt_bytes` capped by the tier's `max_class_prompt_bytes`, else the tier's bound)."""
    try:
        return int(replay.prompt_bound(tier, cls))
    except replay.ReplayError:
        return package.MAX_PROMPT_BYTES


# ---- obligation files ----

class Located:
    """The residual_loop run dir D and the MANIFEST row GOAL of one obligation."""

    def __init__(self, d, goal):
        self.d, self.goal = Path(d), goal
        self.gid = goal["id"]
        self.goal_dir = self.d / "goals" / self.gid
        self.answer_json = self.d / "answers" / (self.gid + ".json")
        self.answer_v = self.d / "answers" / (self.gid + ".v")
        self.feedback = self.d / "feedback" / (self.gid + ".txt")
        self.status = self.goal_dir / "STATUS.json"

    def prompt_path(self, tier, attempt):
        return self.d / "prompts" / self.gid / ("%s-%d.md" % (tier, attempt))

    def manifest(self):
        return store.read_json(self.d / "MANIFEST.json", {})


def locate(run, function):
    """{obligation id: Located} over the residual_loop run dirs under RUN."""
    out = {}
    for d in store.residual_runs(run):
        manifest = store.read_json(d / "MANIFEST.json", {})
        if manifest.get("function") not in (None, function):
            continue
        block = manifest.get("block")
        for goal in manifest.get("goals", []):
            if block == "meaning" or goal.get("source") == "meaning":
                identifier = store.meaning_id(function, goal["name"])
            elif block and goal.get("statement"):
                identifier = store.goal_id(function, block, goal["statement"])
            else:
                continue
            out[identifier] = Located(d, goal)
    return out


def dependencies(function, item, where):
    """The obligation ids the goal states as hypotheses (`deps` of a meaning goal's MANIFEST row)."""
    if where is None or item["kind"] != "meaning":
        return []
    return [store.meaning_id(function, dep) for dep in where.goal.get("deps", [])]


def fold(run):
    return store.fold(store.read_events(run))


def base_event(item, **fields):
    return store.event(id=item["id"], function=item["function"], kind=item["kind"], parent=item["parent"],
                       head=store.git_head(), **fields)


def last_attempt_event(item):
    rows = [row for row in item["events"] if row.get("attempt") is not None]
    return rows[-1] if rows else None


# ---- prompts ----

def task_text(where, tier):
    """(text, packaged) of the goal's task: package.py's bounded task (TASK-<tier>.md, the tier-less
    TASK.md, another tier's TASK-*.md) when the goal has a package, else the residual_loop task."""
    packaged = where.d / "package" / where.gid
    for path in [packaged / ("TASK-%s.md" % tier), packaged / "TASK.md", *sorted(packaged.glob("TASK-*.md"))]:
        if path.is_file():
            return path.read_text(), True
    path = where.d / "tasks" / (where.gid + ".md")
    return (path.read_text(), False) if path.is_file() else (None, False)


def clip(text, limit):
    data = text.encode()
    if len(data) <= limit:
        return text
    keep = max(0, limit - len(TRUNCATED.encode()))
    return data[:keep].decode(errors="ignore") + TRUNCATED if keep else ""


def base_prompt(where, tier):
    """The no-tools prompt of an attempt without feedback: the task file, the exact source of
    goal.v when a residual_loop task only names its path (a package task is already bounded and
    is sent as written), and the answer form."""
    text, packaged = task_text(where, tier)
    if text is None:
        return None
    if not packaged and EXACT_HEADING not in text and (where.goal_dir / "goal.v").is_file():
        goal_v = (where.goal_dir / "goal.v").read_text()
        text += "\n%s\n\n```coq\n%s\n```\n" % (EXACT_HEADING, goal_v[:goal_v.index("Proof.")].rstrip()
                                                 if "Proof." in goal_v else goal_v.rstrip())
    if "## Answer form" not in text:
        text += "\n" + package.ANSWER_FORM.format(answer=where.answer_v)
    return NO_TOOLS + text


def error_section(where, budget):
    """The previous proof and the compiler errors, cut to BUDGET bytes (the errors first)."""
    proof = where.answer_v.read_text() if where.answer_v.is_file() else ""
    errors = where.feedback.read_text(errors="replace") if where.feedback.is_file() else "(no compiler output)"
    head = ERROR_HEAD + "Rocq rejected this proof:\n\n```coq\n%s```\n\nCompiler output:\n\n```\n%s\n```\n\nSend a corrected proof.\n"
    fixed = len((head % ("", "")).encode())
    room = budget - fixed
    if room <= 0:
        return None
    errors = clip(errors.rstrip(), max(room // 2, room - len(proof.encode())))
    # One byte is kept for the newline that closes the proof before the fence.
    proof = clip(proof, room - len(errors.encode()) - 1)
    return head % (proof if proof.endswith("\n") or not proof else proof + "\n", errors)


def sibling_runs(goal_dir):
    """The residual_loop run dirs beside the goal's own (the other goals of its function or block)."""
    return store.residual_runs(Path(goal_dir).parents[2], depth=2)


def named_entries(needs, goal_dir):
    """(name, text) of each item the NEEDS name that the model-free sources hold: closed lemmas of the
    similar-lemma index, then the statements of the goals beside GOAL_DIR."""
    import similar
    text = " ".join(needs)

    def named(name):
        return re.search(r"(?<![\w'.])%s(?:_statement)?(?![\w'])" % re.escape(name), text)
    runs = sibling_runs(goal_dir)
    found, seen = [], set()
    for entry in similar.build_index(runs=runs)["entries"]:
        if named(entry["name"]) and entry["name"] not in seen:
            seen.add(entry["name"])
            found.append((entry["name"], similar.render(entry)))
    for d in runs:
        for goal in store.read_json(d / "MANIFEST.json", {}).get("goals", []):
            goal_v = d / "goals" / goal["id"] / "goal.v"
            name = goal.get("name")
            if name and name not in seen and named(name) and goal_v.is_file():
                seen.add(name)
                source = goal_v.read_text()
                body = source[source.index("Lemma "):source.index("Proof.")].rstrip() if "Lemma " in source else source
                found.append((name, "### %s\n\n```coq\n%s\n```\n" % (name, body)))
    return found


def definitions_text(needs, goal_dir, max_bytes):
    """The Rocq `About`/`Print` answers of tools/oblig/defs.py (`needs_text`) for the names in NEEDS, or
    "" when that source is absent or cannot answer (a failed query, no bank)."""
    try:
        import defs
        needs_text = defs.needs_text
    except (ImportError, AttributeError):
        return ""
    try:
        return needs_text(needs, goal_dir, max_bytes) or ""
    except (getattr(defs, "DefsError", RuntimeError), OSError, KeyError):
        return ""


def needs_section(needs, goal_dir, budget):
    """(text, used item names) of the need_context retry: the named items of the model-free sources,
    the definitions source, and a note naming what is not available; ("", []) when nothing is."""
    parts, used = [], []
    for name, entry in named_entries(needs, goal_dir):
        if len((CONTEXT_HEAD + "".join(parts) + entry).encode()) <= budget:
            parts.append(entry)
            used.append(name)
    definitions = definitions_text(needs, goal_dir, budget - len((CONTEXT_HEAD + "".join(parts)).encode()))
    if definitions:
        used.append("definitions")
    if not used:
        return "", []
    text = CONTEXT_HEAD + "".join(parts) + definitions
    missing = [need for need in needs if not any(re.search(re.escape(name), need) for name in used)]
    if missing and not definitions:
        text += clip("Not available here: %s. Prove it without them or answer give_up.\n" % "; ".join(missing),
                     max(0, budget - len(text.encode())))
    return text, used


def resolve_needs(needs, goal_dir, max_bytes=package.MAX_PROMPT_BYTES):
    """The context text for the items a `need_context` answer names, "" when none can be supplied."""
    return needs_section(needs, goal_dir, max_bytes)[0]


def prompt_for(run, function, identifier, tier, located=None, state=None):
    """(prompt text, context items) of the next attempt of IDENTIFIER at TIER, or (None, reason).
    After a compile error at this tier the prompt adds the previous proof and the compiler output;
    after need_context it adds the named items (reason `missing_context` when none can be supplied);
    after a malformed reply it starts with MALFORMED_LINE."""
    located = locate(run, function) if located is None else located
    state = fold(run) if state is None else state
    where, item = located.get(identifier), state.get(identifier)
    if where is None or item is None:
        return None, "unlocated"
    limit = max_prompt_bytes(tier, item["goal_class"])
    base = base_prompt(where, tier)
    if base is None:
        return None, "no task file"
    last = item["last_attempt"]
    text, items = base, ["task"]
    if last and last["tier"] == tier and last["failure"] == "compile_error":
        extra = error_section(where, limit - len(base.encode()))
        if extra is None:
            return None, "%s: %d bytes of task leave no room under %d" % (TOO_LARGE, len(base.encode()), limit)
        text, items = base + extra, ["task", "feedback"]
    elif last and last["tier"] == tier and last["failure"] == "need_context":
        needs = store.read_json(where.answer_json, {}).get("needs") or []
        extra, used = needs_section(needs, where.goal_dir, limit - len(base.encode()))
        if not extra:
            return None, "missing_context"
        text, items = base + extra, ["task"] + ["context:" + name for name in used] + ["need_context"]
    elif last and last["tier"] == tier and last["failure"] == "malformed":
        text, items = MALFORMED_LINE + base, ["task", "malformed"]
    if len(text.encode()) > limit:
        return None, "%s: %d > %d bytes" % (TOO_LARGE, len(text.encode()), limit)
    return text, items


def file_missing_context(run, identifier, tier):
    """Append `failed` class missing_context at TIER (no attempt): route.py then escalates the goal
    without spending the tier's next attempt."""
    item = fold(run)[identifier]
    store.append(run, base_event(item, state="failed", **{"class": "missing_context"}, tier=tier))


def file_too_large(run, identifier, tier, reason, located=None):
    """Append `failed` class too_large at TIER (no attempt): route.py skips the tier. When every model
    tier of the goal's ladder is too small for its prompt, the goal becomes `waiting-decision`, its
    artifact TOO-LARGE.json naming each tier's size and bound. Returns True for waiting-decision."""
    item = fold(run)[identifier]
    where = (located or locate(run, item["function"])).get(identifier)
    path = (where.d / "prompts" / where.gid if where else Path(run) / "prompts") / "TOO-LARGE.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    reasons = store.read_json(path, {})
    reasons[tier] = reason
    rl.write_json(path, reasons)
    store.append(run, base_event(item, state="failed", **{"class": "too_large"}, tier=tier))
    item = fold(run)[identifier]
    rungs = [name for name, _ in route.ladder(item["goal_class"], route.load_tiers(), route.load_routing())
             if name != MECHANICAL]
    if not rungs or not set(rungs) <= route.marked_tiers(item, ("too_large",)):
        return False
    store.append(run, base_event(item, state="waiting-decision", **{"class": item["goal_class"]},
                                 artifact=store.artifact_of(path)))
    return True


def file_repeated_prompt(run, identifier, tier):
    """Append `failed` class repeated_prompt at TIER (no attempt): the store refused the prompt as sent
    before to this tier (after a reset whose prompt did not change, as the fixed `mechanical` one);
    route.py skips the tier until the next reset."""
    item = fold(run)[identifier]
    store.append(run, base_event(item, state="failed", **{"class": "repeated_prompt"}, tier=tier))


# ---- attempts and answers ----

def register_attempt(run, function, identifier, tier, prompt, context_items=None, located=None):
    """Append the attempt's `running` event and keep the prompt; store.Rejected when the
    (prompt_sha256, tier) pair was sent before for this obligation. Returns the attempt number."""
    located = locate(run, function) if located is None else located
    item = fold(run)[identifier]
    attempt = item["tier_attempts"].get(tier, 0) + 1
    store.append(run, base_event(item, state="running", **{"class": item["goal_class"]}, tier=tier,
                                 attempt=attempt, prompt_sha256=sha(prompt), prompt_bytes=len(prompt.encode()),
                                 context_items=context_items))
    where = located.get(identifier)
    if where is not None:
        path = where.prompt_path(tier, attempt)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(prompt)
    return attempt


def answer(run, function, identifier, tier, attempt, prompt, reply, extra=None, located=None):
    """Write the reply of one attempt with package.write_answer (answers/<goal>.json and .v); the
    JSON also records the attempt, prompt_sha256, agent id and resolved model. A give_up,
    need_context or malformed reply appends its `failed` event at once; `proved` and `false` wait
    for `step`. Returns the verdict."""
    located = locate(run, function) if located is None else located
    where = located[identifier]
    extra = dict(extra or {})
    data, raw = replay.parse_reply(reply if reply is not None else "")
    verdict = None
    if data is not None:
        try:
            verdict, _ = package.write_answer(where.d, where.gid, data, raw, tier, extra.get("tokens_in"),
                                              extra.get("tokens_out"))
        except package.PackageError as error:
            extra["malformed"] = str(error)
    if verdict is None:
        verdict = "malformed"
        where.answer_json.parent.mkdir(parents=True, exist_ok=True)
        (where.d / "answers" / (where.gid + ".raw")).write_text(raw)
        rl.write_json(where.answer_json, dict(verdict="malformed", tier=tier, answer_bytes=len(raw.encode()),
                                              tokens_in=extra.get("tokens_in"), tokens_out=extra.get("tokens_out")))
    meta = store.read_json(where.answer_json, {})
    meta.update(attempt=attempt, prompt_sha256=sha(prompt), prompt_bytes=len(prompt.encode()),
                **{k: extra[k] for k in ("agent_id", "resolved_model", "model_mismatch", "error", "malformed")
                   if k in extra})
    rl.write_json(where.answer_json, meta)
    if verdict in FAILED_VERDICTS:
        item = fold(run)[identifier]
        store.append(run, attempt_event(item, meta, "failed", verdict))
    return verdict


def attempt_event(item, meta, state, cls, **fields):
    return base_event(item, state=state, **{"class": cls}, tier=meta["tier"], attempt=meta["attempt"],
                      prompt_sha256=meta["prompt_sha256"], prompt_bytes=meta.get("prompt_bytes"),
                      answer_bytes=meta.get("answer_bytes"), tokens_in=meta.get("tokens_in"),
                      tokens_out=meta.get("tokens_out"), **fields)


# ---- the kernel side of step (compiles) ----

class Kernel:
    """The compiles of step; the tests replace it."""

    def check(self, d, gids, jobs):
        """{goal: PASS or FAIL} of the current answers/<goal>.v of each GID in run dir D, through
        `residual_loop.py collect` (check.sh in one guard scope, then the premise minimiser)."""
        subprocess.run([sys.executable, str(ROOT / "tools/block/residual_loop.py"), "collect", "--run", str(d),
                        "--jobs", str(max(1, jobs))], capture_output=True, text=True, env=rl.clean_env())
        out = {}
        for gid in gids:
            text = (Path(d) / "answers" / (gid + ".v")).read_text()
            status = store.read_json(Path(d) / "goals" / gid / "STATUS.json", {})
            found = [a for a in status.get("attempts", []) if a.get("sha256") == rl.sha(text)]
            out[gid] = found[-1]["result"] if found else None
        return out

    def route_of(self, d):
        import falsify
        return falsify.Route(store.read_json(Path(d) / "MANIFEST.json", {})["bank"])

    def falsify(self, where, out, run):
        import falsify
        exec_dir = Path(run) / "exec"
        block = where.manifest().get("block")
        offset = block if block and re.fullmatch(r"[0-9a-f]{4}", block) else None
        goal = where.goal_dir / "FALSIFY.v"
        goal = goal if goal.is_file() else where.goal_dir / "goal.v"
        return falsify.check(goal, self.route_of(where.d), out, exec_dir=exec_dir if exec_dir.is_dir() else None,
                             offset=offset)

    def refute(self, where, text, out):
        """True when the kernel accepts `~ statement` on the binder values the counterexample names."""
        import falsify
        route_ = self.route_of(where.d)
        goal = where.goal_dir / "FALSIFY.v"
        goal = goal if goal.is_file() else where.goal_dir / "goal.v"
        out.mkdir(parents=True, exist_ok=True)
        goal_preamble, statement, _ = falsify.read_goal(goal)
        pre = falsify.preamble(goal_preamble, statement, route_.args, route_.coqlib)
        (out / "probe.v").write_text(falsify.probe_text(pre, statement))
        result, log = route_.compile(out / "probe.v", "drive-probe-" + where.gid)
        binders, ended = falsify.parse_binders(falsify.records(log))
        if result["returncode"] != 0 or not ended or any(b["kind"] not in falsify.CHECKED_KINDS for b in binders):
            return False
        try:
            values = replay.counterexample_values(text, binders)
        except ValueError:
            return False
        (out / "refute.v").write_text(falsify.refute_text(pre, statement, binders, values))
        result, _ = route_.compile(out / "refute.v", "drive-refute-" + where.gid)
        return result["returncode"] == 0


# ---- step ----

def unblock(function, run, state, located, counts):
    rows = []
    for item in state.values():
        if item["state"] != "blocked-on" or item["kind"] not in ("goal", "meaning"):
            continue
        blocker = state.get(item["blocked_by"])
        if not blocker or blocker["state"] != "closed":
            continue
        where = located.get(item["id"])
        unmet = [dep for dep in dependencies(function, item, where)
                 if (state.get(dep) or {}).get("state") != "closed"]
        if unmet:
            rows.append(base_event(item, state="blocked-on", **{"class": unmet[0]}, artifact=item["artifact"]))
            counts.bump("reblocked")
            continue
        carried = carried_falsity(item, where)
        rows.append(base_event(item, state="derived", **{"class": item["goal_class"]},
                               tier="falsify" if carried else None, artifact=carried or item["artifact"]))
        counts.bump("unblocked")
    if rows:
        store.append(run, rows)
    return len(rows)


def carried_falsity(item, where):
    """The artifact of the last falsity check when goal.v is unchanged since the goal was filed."""
    if where is None or not (where.goal_dir / "goal.v").is_file():
        return None
    filed = [row["artifact"] for row in item["events"]
             if row.get("artifact") and row["artifact"]["path"].endswith("/goal.v")]
    checked = [row["artifact"] for row in item["events"] if row.get("tier") == "falsify" and row.get("artifact")]
    if not filed or not checked or store.sha256_file(where.goal_dir / "goal.v") != filed[-1]["sha256"]:
        return None
    path = Path(checked[-1]["path"])
    return store.artifact_of(path) if path.is_file() else None


def check_answers(function, run, state, located, kernel, counts, jobs):
    """Check the answers of the running attempts; append each closed/failed/false event."""
    pending = {}
    for item in state.values():
        last = last_attempt_event(item)
        if item["state"] != "running" or last is None or item["id"] not in located:
            continue
        where = located[item["id"]]
        meta = store.read_json(where.answer_json, {})
        if (meta.get("prompt_sha256"), meta.get("attempt"), meta.get("tier")) != (
                last["prompt_sha256"], last["attempt"], last["tier"]):
            continue
        pending.setdefault(where.d, []).append((item, where, meta))
    if not pending:
        return 0
    rows = []

    def run_dir(entry):
        d, group = entry
        proved = [where.gid for item, where, meta in group if meta.get("verdict") == "proved"]
        results = kernel.check(d, proved, jobs) if proved else {}
        out = []
        for item, where, meta in group:
            if meta.get("verdict") == "proved":
                out.append(proved_event(item, where, meta, results.get(where.gid), counts))
            elif meta.get("verdict") == "false":
                hit = kernel.refute(where, meta.get("counterexample") or "",
                                    where.d / "checks" / where.gid / ("%s-%d" % (meta["tier"], meta["attempt"])))
                counts.bump("false" if hit else "bad_counterexample")
                out.append(attempt_event(item, meta, "false", item["goal_class"]) if hit else
                           attempt_event(item, meta, "failed", "bad_counterexample"))
        return out
    with ThreadPoolExecutor(max_workers=max(1, min(jobs, len(pending)))) as pool:
        for out in pool.map(run_dir, sorted(pending.items(), key=lambda kv: str(kv[0]))):
            rows += out
    if rows:
        store.append(run, rows)
    return len(rows)


def proved_event(item, where, meta, result, counts):
    if result == "PASS":
        counts.bump("closed")
        proof = where.goal_dir / "proof.v"
        supplied = [name[len("context:"):] for name in (last_attempt_event(item) or {}).get("context_items") or []
                    if name.startswith("context:")]
        text = where.answer_v.read_text() if where.answer_v.is_file() else ""
        return attempt_event(item, meta, "closed", item["goal_class"],
                             context_used=[name for name in supplied if name in text] if supplied else None,
                             artifact=store.artifact_of(proof) if proof.is_file() else None)
    counts.bump("compile_error" if result == "FAIL" else "reparse")
    return attempt_event(item, meta, "failed", "compile_error" if result == "FAIL" else "reparse",
                         artifact=store.artifact_of(where.feedback) if where.feedback.is_file() else None)


def run_falsify(run, state, located, kernel, todo, counts, jobs):
    def one(identifier):
        item, where = state[identifier], located[identifier]
        report = kernel.falsify(where, where.goal_dir / "falsify", run)
        verdict = report.get("verdict")
        path = where.goal_dir / "falsify" / "FALSIFY.json"
        artifact = store.artifact_of(path) if path.is_file() else None
        counts.bump("falsify_" + str(verdict))
        if verdict == "false":
            return base_event(item, state="false", **{"class": item["goal_class"]}, tier="falsify", artifact=artifact)
        cls = item["goal_class"] or ("unchecked" if verdict == "unchecked" else None)
        return base_event(item, state="derived", **{"class": cls}, tier="falsify", artifact=artifact)
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        rows = list(pool.map(one, todo))
    if rows:
        store.append(run, rows)
    return len(rows)


def run_mechanical(function, run, located, todo, counts):
    done = 0
    for identifier in todo:
        try:
            attempt = register_attempt(run, function, identifier, MECHANICAL, MECHANICAL_PROOF, located=located)
        except store.Rejected:
            file_repeated_prompt(run, identifier, MECHANICAL)
            counts.bump("repeated_prompt")
            done += 1
            continue
        answer(run, function, identifier, MECHANICAL, attempt, MECHANICAL_PROOF,
               dict(verdict="proved", proof=MECHANICAL_PROOF), located=located)
        counts.bump("mechanical")
        done += 1
    return done


class Counts(dict):
    """Counts of one step call, bumped from the worker threads."""

    def __init__(self):
        super().__init__()
        self.lock = threading.Lock()

    def bump(self, key):
        with self.lock:
            self[key] = self.get(key, 0) + 1


def escalate_unpromptable(function, run, located, free, counts):
    """For each model attempt route.py assigns, before any model sees it (no model):
    - a goal whose package (package.py PACKAGE.json) has class ADDRESS gets that class (`derived`
      class ADDRESS, the package record as artifact), so route.py sends it to the statement owner;
    - a need_context retry whose named items no source can supply files `missing_context`;
    - a prompt over the tier's bound files `too_large` (file_too_large)."""
    state, filed = fold(run), 0
    for identifier, action, tier, _ in route.next_items(run, function):
        if action != "prove" or tier in (None, MECHANICAL) or identifier not in free:
            continue
        where = located[identifier]
        record = where.d / "package" / where.gid / "PACKAGE.json"
        if store.read_json(record, {}).get("class") == "ADDRESS" and state[identifier]["goal_class"] != "ADDRESS":
            store.append(run, base_event(state[identifier], state="derived", **{"class": "ADDRESS"},
                                         artifact=store.artifact_of(record)))
            counts.bump("address")
            filed += 1
            continue
        text, reason = prompt_for(run, function, identifier, tier, located=located, state=state)
        if text is not None:
            continue
        if reason == "missing_context":
            file_missing_context(run, identifier, tier)
            counts.bump("missing_context")
        elif reason.startswith(TOO_LARGE):
            counts.bump("waiting_decision_too_large" if file_too_large(run, identifier, tier, reason, located)
                        else "too_large")
        else:
            continue
        filed += 1
    return filed


def step(function, run, limit=None, jobs=8, kernel=None):
    """Perform every model-free routed action until a pass changes nothing; return
    (counts, [(id, action, tier, why)] left, running ids, unlocated ids)."""
    run = Path(run)
    kernel = kernel or Kernel()
    counts = Counts()
    for _ in range(MAX_PASSES):
        located = locate(run, function)
        progress = check_answers(function, run, fold(run), located, kernel, counts, jobs)
        # Unblock before routing: route.py routes a goal blocked on a closed obligation as if it were free.
        progress += unblock(function, run, fold(run), located, counts)
        state = fold(run)
        free = {i for i in located if state.get(i, {}).get("state") != "blocked-on"}
        falsify_ids = [i for i, action, tier, _ in route.next_items(run, function) if action == "falsify" and i in free]
        progress += run_falsify(run, state, located, kernel, falsify_ids, counts, jobs) if falsify_ids else 0
        mechanical = [i for i, action, tier, _ in route.next_items(run, function)
                      if action == "prove" and tier == MECHANICAL and i in free]
        progress += run_mechanical(function, run, located, mechanical, counts)
        progress += escalate_unpromptable(function, run, located, free, counts)
        if not progress:
            break
    located = locate(run, function)
    state = fold(run)
    left = [row for row in route.next_items(run, function, limit)]
    running = [(item["id"], item["tier"]) for item in state.values() if item["state"] == "running"]
    unlocated = sorted(i for i, action, tier, _ in left
                       if action in ("falsify", "prove") and i not in located)
    return counts, left, running, unlocated


def model_items(run, function, tier=None):
    """[(id, tier, why)] of the prover attempts route.py assigns to a model tier."""
    return [(identifier, t, why) for identifier, action, t, why in route.next_items(run, function)
            if action == "prove" and t not in (None, MECHANICAL) and (tier is None or t == tier)]


def report_lines(counts, left, running, unlocated):
    lines = ["done %s" % (" ".join("%s=%d" % kv for kv in sorted(counts.items())) or "nothing")]
    for identifier, action, tier, why in left:
        if identifier in unlocated:
            lines.append("UNLOCATED %s" % identifier)
        elif action == "prove" and tier != MECHANICAL:
            lines.append("MODEL %s tier=%s %s" % (identifier, tier, why))
        else:
            lines.append("LIST %s %s%s %s" % (identifier, action, " tier=" + tier if tier else "", why))
    lines += ["RUNNING %s tier=%s" % pair for pair in running]
    return lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("step")
    command.add_argument("--function", required=True)
    command.add_argument("--run", type=Path)
    command.add_argument("--limit", type=int, default=None)
    command.add_argument("--jobs", type=int, default=8)
    options = parser.parse_args(argv)
    run = options.run or store.default_run(options.function)
    try:
        counts, left, running, unlocated = step(options.function, run, options.limit, options.jobs)
    except store.Rejected as error:
        print("rejected: %s" % error, file=sys.stderr)
        return 1
    text = "".join(line + "\n" for line in report_lines(counts, left, running, unlocated))
    sys.stdout.write(text)
    store.record_coordinator_read(run, "drive.step", text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
