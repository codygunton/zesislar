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
  registered and written as a `proved` answer, then checked like a model's. When CONTROL_TACTIC
  changes, route.py offers it again to every goal whose mechanical attempts all used an older text.
- check: every `running` attempt whose answer (RUN.../answers/<goal>.json, written by `answer` of
  this module with the attempt's prompt_sha256) is in: `proved` goes through
  `residual_loop.py collect` (the stand-alone check.sh route) and becomes `closed` or `failed`
  compile_error; `false` is checked with falsify.py's kernel refutation on the binder values the
  answer names (`false`, else failed bad_counterexample).
The actions rerun, derive, package, test, check (decisions), decide, diagnose, reconsider, owner
and spin are listed for the region owner or the coordinator, never executed. Superseded obligations
(store.py) get no action.

Output: one `done` line with the counts of this call, then one line per item left:
`MODEL <id> tier=<tier> <why>` (for drive_kernel.run_round), `RUNNING <id> tier=<tier>` (an attempt
without its answer), `LIST <id> <action> [tier=<tier>] <why>` (not this driver's), and `UNLOCATED <id>`
(no residual_loop run dir under RUN holds the goal).

Obligation files: every residual_loop.py run dir under RUN (MANIFEST.json and goals/). A goal of a
block run is `<F>/goal/<block>-<16 hex of sha256(statement)>`; a goal of a run whose block is
`meaning` is `<F>/meaning/<goal name>`. Its task file is RUN.../package/<goal>/TASK-<tier>.md
(package.py) when present, else RUN.../tasks/<goal>.md; prompts sent are kept in
RUN.../prompts/<goal>/<tier>-<attempt>.md.

Prover tools (tiers.json `check_tool` + `check_calls`, `lookup_calls`, `counterexample_calls`): a tier
with tools gets the TOOLS_HEAD preamble listing them and their rules instead of NO_TOOLS, and
drive_kernel.py hands each of its provers, bound to that one goal and attempt:
- check_proof (ProofProbe): compiles a proposed proof with the goal's stand-alone check route
  (residual_loop.py check.sh, resource guard scope) in a scratch dir
  RUN.../probes/<goal>/<tier>-<attempt>/<call>/, never in goals/, answers/ or the store, and answers
  {ok, error, remaining}: the compiler errors and the goal state before the failing sentence, clipped
  to CHECK_ERROR_BYTES, and the calls left of the attempt's budget;
- lookup(name) and search(pattern) (LookupProbe, one budget): the definition or statement of a name
  (defs.py About/Print) and Rocq `Search`, with the goal's imports, clipped to LOOKUP_BYTES, cached per
  goal (defs/) and per attempt (a repeat is free);
- check_counterexample(assignment) (CounterexampleProbe): falsify.py's kernel refutation at the values
  named; it says when the binder types are outside falsify.py's range. With this tool, a `false` answer
  whose counterexample it did not confirm is refused (`failed` unconfirmed_false, no kernel call).
The answer is still checked by `step`; the attempt's result event carries `check_calls:<n>`,
`lookup_calls:<n>`, `search_calls:<n>`, `counterexample_calls:<n>` in context_items.

Best-of-N (tiers.json or routing.json `samples`): drive_kernel.py sends N samples of one goal per round,
their prompts varied by sample_prompt; settle_round submits one (the first whose proof the kernel
accepts) and records the others; route.py counts the round as one attempt.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import uuid

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
TOOLS_HEAD = """You are a Rocq prover. Everything you need is in this message or behind the tools listed here (each is
in your tool list under a name that starts with the name given); call no other tool. Do not read or write any
file. Where the task below says to write the proof script to a file, put that text in the `proof` field of your
answer instead. Your whole reply is one JSON object in the answer form at the end, with no other text and no
code fence.

Tools:
"""
CHECK_LINE = """- check_proof(proof): compiles the lemma below with your proof script (the text of your `proof` field,
  ending with `Qed.`) and returns `ok`, the compiler error with the goal state before the failing sentence,
  and the calls left (%d per attempt). Check your proof before you answer `proved`.
"""
LOOKUP_LINE = """- lookup(name): the definition of one identifier (for a lemma or an opaque constant: its statement) with
  this goal's imports. search(pattern): Rocq `Search <pattern>` with this goal's imports, e.g.
  `(_ * 32)%%Z` or `bv_unsigned "shiftl"` (no final dot). Together at most %d calls per attempt; asking
  for a name again is free.
"""
COUNTEREXAMPLE_LINE = """- check_counterexample(assignment): asks the kernel whether the lemma is false at the values you give,
  written `x = 5, w = 0xff, b = true` (the lemma's universally quantified variables; a variable you do not
  name takes a default value). Returns `confirmed` true or false and why; at most %d calls per attempt.
"""
LOOKUP_RULE = ("- Never answer need_context before you have called lookup or search for what you miss; answer\n"
               "  need_context only for an item they cannot give.\n")
FALSE_RULE = ("- Never answer false unless check_counterexample confirmed the exact assignment you put in\n"
              "  `counterexample`: an unconfirmed false is refused and counts as a failed attempt.\n")
UNCHECKED_RULE = ("- The variable types of this lemma are outside the counterexample checker's range: answer false is\n"
                  "  not allowed for it.\n")
ERROR_HEAD = "\n## Your previous answer failed\n\n"
CONTEXT_HEAD = "\n## Context you asked for\n\n"
TRUNCATED = "\n[... truncated]"
MALFORMED_LINE = "Reply with the bare JSON object only.\n\n"
TOO_LARGE = "too-large"
CHECK_TOOL = "check_proof"
LOOKUP_TOOL = "lookup"
SEARCH_TOOL = "search"
COUNTEREXAMPLE_TOOL = "check_counterexample"
CHECK_CALLS = 6  # check_proof calls per attempt (tiers.json `check_calls` replaces it)
CHECK_ERROR_BYTES = 1500  # error text of one check_proof answer
LOOKUP_BYTES = 3000  # text of one lookup or search answer
UNCONFIRMED_FALSE = "unconfirmed_false"
TOOL_COUNTS = ("check_calls", "lookup_calls", "search_calls", "counterexample_calls")
# Peak resident memory of one check_proof call (its check.sh compile, then the goal-state compile), rounded
# up from the measured peaks (2026-11-23: 0.78 GiB keysToOwnedSlice block goal 0098, 0.58 GiB Sail meaning
# lemma alDecodeWord); parallel calls are bounded by 70% of the available memory over it (AGENTS.md).
CHECK_PEAK_BYTES = 1 << 30
CHECK_MEMORY_SHARE = 0.7


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


def tier_cap(tier):
    """The largest prompt a tier takes (tiers.json `max_class_prompt_bytes`)."""
    row = tier_rows().get(tier, {})
    return int(row.get("max_class_prompt_bytes", row.get("max_prompt_bytes", package.MAX_PROMPT_BYTES)))


def large_bound(where, tier):
    """The bound of a goal re-packaged at the tier cap (PACKAGE.json `prompt_bound`, capped by TIER's), or
    None: such a goal is sent at that size, its attempts carrying `prompt_bound:<bytes>`."""
    bound = store.read_json(where.d / "package" / where.gid / "PACKAGE.json", {}).get("prompt_bound")
    return min(int(bound), tier_cap(tier)) if bound else None


def check_tool(tier):
    """(enabled, calls per attempt) of TIER's check_proof tool (tiers.json `check_tool`, `check_calls`;
    a tier without a model never has it)."""
    row = tier_rows().get(tier, {})
    enabled = bool(row.get("agent")) and bool(row.get("check_tool", False))
    return enabled, int(row.get("check_calls", CHECK_CALLS)) if enabled else 0


def tool_budgets(tier):
    """{tool: calls per attempt} of TIER's prover tools (tiers.json `check_calls` with `check_tool`,
    `lookup_calls` for lookup and search together, `counterexample_calls`); a tool with 0 calls or a
    tier without a model has none."""
    row = tier_rows().get(tier, {})
    if not row.get("agent"):
        return {}
    out = {CHECK_TOOL: check_tool(tier)[1], LOOKUP_TOOL: int(row.get("lookup_calls", 0)),
           COUNTEREXAMPLE_TOOL: int(row.get("counterexample_calls", 0))}
    return {name: calls for name, calls in out.items() if calls > 0}


def samples(tier, cls=None):
    """Parallel samples of one best-of-N round of a goal of class CLS at TIER: the class's routing.json
    `samples` row (as `attempts`: class, prefix, default), else tiers.json `samples`, else 1."""
    for row in route.class_rows(route.load_routing(), cls):
        if isinstance(row.get("samples"), dict) and tier in row["samples"]:
            return max(1, int(row["samples"][tier]))
    return max(1, int(tier_rows().get(tier, {}).get("samples", 1)))


def preamble(tier, unchecked=False):
    """The first lines of every prompt of TIER: NO_TOOLS without tools, else TOOLS_HEAD with one entry per
    tool of tool_budgets and the rules of the tools it has (UNCHECKED_RULE when the goal's binder types are
    outside falsify.py's range and the tier has check_counterexample)."""
    budgets = tool_budgets(tier)
    if not budgets:
        return NO_TOOLS
    text = TOOLS_HEAD
    if CHECK_TOOL in budgets:
        text += CHECK_LINE % budgets[CHECK_TOOL]
    if LOOKUP_TOOL in budgets:
        text += LOOKUP_LINE % budgets[LOOKUP_TOOL]
    if COUNTEREXAMPLE_TOOL in budgets:
        text += COUNTEREXAMPLE_LINE % budgets[COUNTEREXAMPLE_TOOL]
    rules = (LOOKUP_RULE if LOOKUP_TOOL in budgets else "") + (
        (UNCHECKED_RULE if unchecked else FALSE_RULE) if COUNTEREXAMPLE_TOOL in budgets else "")
    return text + ("\nRules:\n" + rules if rules else "") + "\n"


RETRY_ROOM = 2000  # bytes a retry prompt keeps for the compiler errors or the asked-for context


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


def last_since_reset(item):
    """The goal's last attempt since its last reset (store.fold's `last_attempt` form), or None: a reset
    runs the ladder again, so its first prompt is no retry of an attempt made before it."""
    rows = [row for row in route.since_reset(item) if row.get("attempt") is not None]
    if not rows:
        return None
    row = rows[-1]
    return dict(tier=row["tier"], attempt=row["attempt"], state=row["state"],
                failure=row["class"] if row["state"] == "failed" else None)


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


def base_prompt(where, tier, unchecked=False):
    """The prompt of an attempt without feedback: the tier's preamble, the task file, the exact source
    of goal.v when a residual_loop task only names its path (a package task is already bounded and
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
    return preamble(tier, unchecked) + text


# ---- best-of-N samples ----

SIMILAR_HEADING = "## Similar closed lemmas"
ANSWER_HEADING = "## Answer form"
SAMPLE_ROOM = 700  # bytes a sample's section may add to a prompt (package bounds leave it free)
# The first-tactic families a sample suggests, rotated over the samples of one goal.
FAMILIES = (
    "arithmetic first: unfold the names the conclusion uses, then try `lia` or `nia`; for bit vectors turn "
    "`bv_unsigned` terms into Z facts (or try `bv_simplify` / `bv_solve`) and finish with `lia`.",
    "rewriting first: `subst`, `rewrite` with the hypotheses and `simpl in *` until the conclusion matches a "
    "hypothesis or is plain arithmetic, then close it.",
    "case analysis first: `destruct` (or `case_eq`, `induction`) the variable, option or disjunction the "
    "conclusion depends on, then close each case.",
)


def rotate_similar(text, shift):
    """TEXT with the entries (`### ` sections) of its similar-lemma section rotated left by SHIFT."""
    start = text.find(SIMILAR_HEADING)
    if start < 0:
        return text
    body_start = text.find("\n", start) + 1
    end = text.find("\n## ", body_start)
    end = len(text) if end < 0 else end + 1
    body = text[body_start:end]
    first = body.find("### ")
    if first < 0:
        return text
    entries = body[first + len("### "):].split("\n### ")
    entries = ["### " + entry if entry.endswith("\n") else "### " + entry + "\n" for entry in entries]
    shift %= len(entries)
    return text[:body_start] + body[:first] + "".join(entries[shift:] + entries[:shift]) + text[end:]


def sample_prompt(text, identifier, index, count):
    """The prompt of sample INDEX (0-based) of COUNT of one best-of-N round: TEXT with its similar lemmas
    rotated by INDEX and a section naming the sample and its suggested first approach (FAMILIES, rotated
    from a hash of IDENTIFIER), before the answer form; deterministic in (goal, sample index), and
    different for each index of one round. COUNT 1 leaves TEXT unchanged."""
    if count <= 1:
        return text
    family = FAMILIES[(int(sha(identifier)[:8], 16) + index) % len(FAMILIES)]
    section = "\n## Sample %d of %d\n\nSuggested first approach for this sample: %s\n" % (index + 1, count, family)
    text = rotate_similar(text, index)
    at = text.rfind(ANSWER_HEADING)
    if at < 0:
        return text + section
    return text[:at].rstrip("\n") + "\n" + section + "\n" + text[at:]


def unchecked_goal(where):
    """True when the goal's falsity check (RUN.../goals/<goal>/falsify/FALSIFY.json, drive's
    run_falsify) found binder types outside falsify.py's range: no counterexample can be confirmed."""
    report = store.read_json(where.goal_dir / "falsify" / "FALSIFY.json", {}) or {}
    return report.get("verdict") == "unchecked"


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


def prompt_for(run, function, identifier, tier, located=None, state=None, sample=None):
    """(prompt text, context items) of the next attempt of IDENTIFIER at TIER, or (None, reason).
    After a compile error at this tier the prompt adds the previous proof and the compiler output;
    after need_context it adds the named items (reason `missing_context` when none can be supplied);
    after a malformed reply it starts with MALFORMED_LINE. SAMPLE (index, count) of a best-of-N round
    varies the prompt with sample_prompt (context item `sample:<index+1>/<count>`)."""
    located = locate(run, function) if located is None else located
    state = fold(run) if state is None else state
    where, item = located.get(identifier), state.get(identifier)
    if where is None or item is None:
        return None, "unlocated"
    limit = max_prompt_bytes(tier, item["goal_class"])
    large = large_bound(where, tier)
    if large and large > limit:
        limit = large
    base = base_prompt(where, tier, unchecked_goal(where))
    if base is None:
        return None, "no task file"
    if sample and sample[1] > 1:
        base = sample_prompt(base, identifier, *sample)
    # The feedback of the last attempt since the goal's last reset; right after a reset, that of the attempt
    # before it is carried when it can be built (the prompt then differs from the one sent before the reset),
    # and dropped when it cannot: a reset runs the ladder again, it never escalates for want of feedback.
    last = last_since_reset(item)
    carried = last is None and item["last_attempt"] is not None
    last = item["last_attempt"] if carried else last
    text, items = base, ["task"]
    # A retry needs room for the compiler errors or the asked-for context, and a meaning lemma has no
    # package to re-package smaller: both may use the tier cap, recorded as `prompt_bound:<bytes>` on
    # the attempt like a goal re-packaged at the cap.
    retry = bool(last and last["tier"] == tier and last["failure"] in ("compile_error", "need_context", "malformed"))
    unpackaged = "/meaning/" in identifier
    if (retry or unpackaged) and tier_cap(tier) > limit and len(base.encode()) + (RETRY_ROOM if retry else 0) > limit:
        limit = large = tier_cap(tier)
    if last and last["tier"] == tier and last["failure"] == "compile_error":
        extra = error_section(where, limit - len(base.encode()))
        if extra is not None:
            text, items = base + extra, ["task", "feedback"]
        elif not carried:
            return None, "%s: %d bytes of task leave no room under %d" % (TOO_LARGE, len(base.encode()), limit)
    elif last and last["tier"] == tier and last["failure"] == "need_context":
        needs = store.read_json(where.answer_json, {}).get("needs") or []
        extra, used = needs_section(needs, where.goal_dir, limit - len(base.encode()))
        if extra:
            text, items = base + extra, ["task"] + ["context:" + name for name in used] + ["need_context"]
        elif not carried:
            return None, "missing_context"
    elif last and last["tier"] == tier and last["failure"] == "malformed":
        text, items = MALFORMED_LINE + base, ["task", "malformed"]
    if len(text.encode()) > limit:
        return None, "%s: %d > %d bytes" % (TOO_LARGE, len(text.encode()), limit)
    if large and large == limit:
        items = items + ["prompt_bound:%d" % limit]
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


def answer(run, function, identifier, tier, attempt, prompt, reply, extra=None, located=None, confirmed=None):
    """Write the reply of one attempt with package.write_answer (answers/<goal>.json and .v); the
    JSON also records the attempt, prompt_sha256, agent id, resolved model and the prover tool calls. A
    give_up, need_context or malformed reply appends its `failed` event at once; `proved` and `false`
    wait for `step`. CONFIRMED, the assignments the attempt's check_counterexample confirmed (None when
    the attempt had no such tool): a `false` whose counterexample is not one of them is refused at once
    (`failed` class unconfirmed_false, no kernel call). Returns the verdict (UNCONFIRMED_FALSE for a
    refused false)."""
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
                   + TOOL_COUNTS if k in extra})
    if verdict == "false" and confirmed is not None and normal(meta.get("counterexample")) not in confirmed:
        meta["refused"] = UNCONFIRMED_FALSE
    rl.write_json(where.answer_json, meta)
    if verdict in FAILED_VERDICTS or meta.get("refused"):
        item = fold(run)[identifier]
        store.append(run, attempt_event(item, meta, "failed", meta.get("refused") or verdict))
    return meta.get("refused") or verdict


def attempt_event(item, meta, state, cls, **fields):
    """The result event of the attempt META names; an attempt with prover tools (meta `check_calls`,
    `lookup_calls`, `search_calls`, `counterexample_calls`) carries its running event's context_items
    plus `<tool count>:<n>` for each."""
    counts = [key for key in TOOL_COUNTS if meta.get(key) is not None]
    if counts and "context_items" not in fields:
        running = [row for row in item["events"] if row["state"] == "running"
                   and (row.get("tier"), row.get("attempt")) == (meta["tier"], meta["attempt"])]
        fields["context_items"] = list((running[-1].get("context_items") or []) if running else []) + [
            "%s:%d" % (key, meta[key]) for key in counts]
    return base_event(item, state=state, **{"class": cls}, tier=meta["tier"], attempt=meta["attempt"],
                      prompt_sha256=meta["prompt_sha256"], prompt_bytes=meta.get("prompt_bytes"),
                      answer_bytes=meta.get("answer_bytes"), tokens_in=meta.get("tokens_in"),
                      tokens_out=meta.get("tokens_out"), **fields)


# ---- best-of-N rounds ----

SUPERSEDED = "superseded"


def settle_round(run, function, identifier, tier, samples, located=None):
    """Record the replies of one best-of-N round of IDENTIFIER at TIER. SAMPLES, in sample order:
    dict(attempt, prompt, reply, extra, proof=ProofProbe or None, counterexample=CounterexampleProbe or
    None), each attempt registered `running` before its agent was spawned. One sample is the round's
    answer, written with `answer` for `step` to check:
    1. the first `proved` sample, in sample order, whose proof the kernel accepts (ProofProbe.final_check:
       a check_proof call of that sample accepted the same text, else one compile);
    2. else the first `false` sample whose counterexample its check_counterexample confirmed;
    3. else the first `proved` sample (its compile error feeds the retry), the first need_context sample
       (its named items feed the retry), else the first sample.
    Every other sample gets its result event at once, before the answer: `failed` with its own verdict
    (give_up, need_context, malformed), compile_error (a proof the kernel rejected), unconfirmed_false,
    or superseded (a proof or a confirmed counterexample not needed: an earlier sample won). The chosen
    sample's running event is then announced again (store.py accepts the events of an open attempt), so
    it is the goal's last attempt. Each reply is kept in RUN.../samples/<goal>/<tier>-<attempt>.json.
    Returns the verdict of each sample in order. One sample is plain `answer`."""
    located = locate(run, function) if located is None else located
    if len(samples) == 1:
        s = samples[0]
        return [answer(run, function, identifier, tier, s["attempt"], s["prompt"], s["reply"], s.get("extra"),
                       located=located, confirmed=s["counterexample"].confirmed if s.get("counterexample") else None)]
    where = located[identifier]
    parsed = []
    for s in samples:
        data, raw = replay.parse_reply(s["reply"] if s["reply"] is not None else "")
        data = data if isinstance(data, dict) else {}
        verdict = data.get("verdict") if data.get("verdict") in package.VERDICTS else "malformed"
        parsed.append((s, data, raw, verdict))
        record = where.d / "samples" / where.gid / ("%s-%d.json" % (tier, s["attempt"]))
        record.parent.mkdir(parents=True, exist_ok=True)
        rl.write_json(record, dict(attempt=s["attempt"], tier=tier, verdict=verdict, reply=raw,
                                   prompt_sha256=sha(s["prompt"]),
                                   **{k: v for k, v in (s.get("extra") or {}).items() if k in TOOL_COUNTS}))
    outcome, chosen = {}, None
    for s, data, raw, verdict in parsed:
        if verdict != "proved":
            continue
        if chosen is not None:
            outcome[s["attempt"]] = SUPERSEDED
            continue
        probe = s.get("proof") or ProofProbe(where, tier, s["attempt"], calls=0)
        if probe.final_check(data.get("proof")):
            chosen = s
        else:
            outcome[s["attempt"]] = "compile_error"
    confirmed = [s for s, data, _, verdict in parsed if verdict == "false" and s.get("counterexample")
                 and s["counterexample"].accepts(data.get("counterexample"))]
    if chosen is None:
        chosen = next(iter(confirmed + [s for s, _, _, v in parsed if v == "proved"]
                           + [s for s, _, _, v in parsed if v == "need_context"]), samples[0])
    item = fold(run)[identifier]
    rows = []
    for s, data, raw, verdict in parsed:
        if s is chosen:
            continue
        if verdict == "false":
            cls = SUPERSEDED if any(s is c for c in confirmed) else UNCONFIRMED_FALSE
        else:
            cls = outcome.get(s["attempt"], verdict)
        extra = s.get("extra") or {}
        meta = dict(tier=tier, attempt=s["attempt"], prompt_sha256=sha(s["prompt"]),
                    prompt_bytes=len(s["prompt"].encode()), answer_bytes=len(raw.encode()),
                    tokens_in=extra.get("tokens_in"), tokens_out=extra.get("tokens_out"),
                    **{k: extra[k] for k in TOOL_COUNTS if k in extra})
        rows.append(attempt_event(item, meta, "failed", cls))
    running = [row for row in item["events"] if row["state"] == "running"
               and (row.get("tier"), row.get("attempt")) == (tier, chosen["attempt"])]
    rows.append(dict(running[-1], head=store.git_head()))
    store.append(run, rows)
    verdicts = {id(s): verdict for s, _, _, verdict in parsed}
    verdicts[id(chosen)] = answer(run, function, identifier, tier, chosen["attempt"], chosen["prompt"],
                                  chosen["reply"], chosen.get("extra"), located=located,
                                  confirmed=chosen["counterexample"].confirmed if chosen.get("counterexample") else None)
    for s, _, _, verdict in parsed:
        if s is not chosen and verdict == "false":
            verdicts[id(s)] = SUPERSEDED if any(s is c for c in confirmed) else UNCONFIRMED_FALSE
    return [verdicts[id(s)] for s in samples]


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

    def repackage(self, run, function, where, tier, bound, reason):
        """package.py's task of a goal again at BOUND (the tier cap) less package_reserve(TIER) (the
        preamble and best-of-N section the prompt adds), with the definitions context and the hint pack of
        RUN when present; the record keeps `prompt_bound` (BOUND), `reserve` and `bound_reason`."""
        import falsify
        import similar
        manifest = where.manifest()
        bank = manifest.get("bank")
        route_ = falsify.Route(bank) if bank and (Path(bank) / "ARGS.json").is_file() else None
        hints = Path(run) / "hints"
        reserve = package_reserve(tier)
        record = package.package_goal(where.d, manifest, where.goal, function, tier, bound - reserve,
                                      similar.build_index(runs=similar.sibling_runs(where.d)),
                                      hints if hints.is_dir() else None,
                                      defs_route=route_, symbol_route=route_)
        record.update(prompt_bound=bound, reserve=reserve, bound_reason=reason)
        return package.write_record(where.d / "package" / where.gid, record)

    def refute(self, where, text, out):
        """True when the kernel accepts `~ statement` on the binder values the counterexample names."""
        return self.refutation(where, text, out)[0]

    def refutation(self, where, text, out, binders=None):
        """(confirmed, reason, binders) of the counterexample TEXT: confirmed when the kernel accepts
        `~ statement` on the binder values it names (falsify.py's refutation, compiled in OUT); BINDERS,
        the goal's parsed binders of an earlier call, spare the binder probe compile. Not confirmed when
        a binder type is outside falsify.py's range (reason says so: no `false` can be confirmed), the
        text names no binder, or the kernel rejects the refutation."""
        import falsify
        route_ = self.route_of(where.d)
        goal = where.goal_dir / "FALSIFY.v"
        goal = goal if goal.is_file() else where.goal_dir / "goal.v"
        out.mkdir(parents=True, exist_ok=True)
        goal_preamble, statement, _ = falsify.read_goal(goal)
        pre = falsify.preamble(goal_preamble, statement, route_.args, route_.coqlib)
        if binders is None:
            (out / "probe.v").write_text(falsify.probe_text(pre, statement))
            result, log = route_.compile(out / "probe.v", "drive-probe-" + where.gid)
            binders, ended = falsify.parse_binders(falsify.records(log))
            if result["returncode"] != 0 or not ended:
                return False, "the checker could not read the lemma's variables", None

        def refute(values):
            (out / "refute.v").write_text(falsify.refute_text(pre, statement, binders, values))
            return route_.compile(out / "refute.v", "drive-refute-" + where.gid)[0]["returncode"] == 0
        return refutation_of(binders, text, refute)


def package_reserve(tier):
    """Bytes a task packaged for TIER leaves free for what the prompt adds: the longer of the tier's two
    preambles (drive.preamble with either false rule) and, with best-of-N samples, SAMPLE_ROOM."""
    return (max(len(preamble(tier).encode()), len(preamble(tier, True).encode()))
            + (SAMPLE_ROOM if samples(tier) > 1 else 0))


def short_reserve(where, tier):
    """True when the goal's package at the tier cap (PACKAGE.json `prompt_bound`) left less room than
    package_reserve(TIER) asks now (a record without `reserve` was cut for the shorter tool-less preamble)."""
    record = store.read_json(where.d / "package" / where.gid / "PACKAGE.json", {}) or {}
    return bool(record.get("prompt_bound")) and int(record.get("reserve", 0)) < package_reserve(tier)


def refutation_of(binders, text, refute):
    """(confirmed, reason, binders) of the counterexample TEXT over the goal's BINDERS (falsify.py's
    parse_binders); REFUTE(values) -> bool compiles `~ statement` at those values."""
    import falsify
    other = [b for b in binders if b["kind"] not in falsify.CHECKED_KINDS]
    if other:
        return False, ("unsupported: the variable types of this lemma (%s) are outside the checker's range "
                       "(Z, nat, N, bv n, list byte, bool); answer false is not allowed for it."
                       % ", ".join("%s : %s" % (b["name"], b.get("type", b["kind"])) for b in other[:4])), binders
    data = [b for b in binders if b["kind"] != "prop"]
    named = {name for name, _ in replay.VALUE.findall(text)}
    if data and not named & {b["name"] for b in data}:
        return False, "names none of the lemma's variables (%s): write `name = value, ...`" % ", ".join(
            b["name"] for b in data[:8]), binders
    try:
        values = replay.counterexample_values(text, binders)
    except ValueError as error:
        return False, "a value could not be read: %s" % error, binders
    if refute(values):
        return True, "the kernel accepts the negated lemma at these values", binders
    return False, "the kernel rejects the negated lemma at these values: the lemma holds there", binders


# ---- the prover check tool (check_proof) ----

LOCATION = re.compile(r'File "[^"]*proof\.v", line (\d+), characters (\d+)-\d+:')
GOALS_LINE = re.compile(r"^(?:\d+ (?:focused )?goals?\b|No more goals|This subproof is complete|There are unfocused goals)")
SENTENCE_END = re.compile(r"\.(?=\s)")
SENTENCE_LEAD = re.compile(r"\s*(?:(?:[-+*]+|[{}])\s*)*")
STATE_HEAD = "\n\nGoal state before the failing sentence:\n"
STATE_CUT = "[... cut]\n"
_SLOTS = []
_SLOTS_LOCK = threading.Lock()


def memory_available():
    """Bytes this account may still use: MemAvailable, less when the user slice's memory.max leaves less."""
    found = []
    try:
        found += [int(line.split()[1]) * 1024 for line in Path("/proc/meminfo").read_text().splitlines()
                  if line.startswith("MemAvailable:")]
    except OSError:
        pass
    user = Path("/sys/fs/cgroup/user.slice/user-%d.slice" % os.getuid())
    try:
        limit = (user / "memory.max").read_text().strip()
        if limit != "max":
            found.append(int(limit) - int((user / "memory.current").read_text()))
    except (OSError, ValueError):
        pass
    return min(found) if found else CHECK_PEAK_BYTES


def check_parallel(available=None):
    """Parallel check_proof compiles: 70% of the available memory over the measured peak of one call."""
    available = memory_available() if available is None else available
    return max(1, int(available * CHECK_MEMORY_SHARE) // CHECK_PEAK_BYTES)


def check_slots(renew=False):
    """The semaphore every check_proof compile of this process holds, sized by check_parallel at its first
    use; RENEW sizes it again from the memory available now (drive_kernel.run_round, before its waves)."""
    with _SLOTS_LOCK:
        if renew or not _SLOTS:
            _SLOTS[:] = [threading.BoundedSemaphore(check_parallel())]
        return _SLOTS[0]


def show_text(proof_v, log, head):
    """proof.v cut before the sentence the first error of LOG names (its leading bullets and braces kept),
    then `Show.` and `Abort.`; None when the error lies outside the proof script."""
    match = LOCATION.search(log)
    if not match:
        return None
    lines = proof_v.encode().split(b"\n")
    line, column = int(match.group(1)), int(match.group(2))
    if line > len(lines):
        return None
    before = b"\n".join(lines[:line - 1] + [lines[line - 1][:column]]).decode(errors="ignore")
    if len(before) < len(head):
        return None
    start = max([len(head)] + [m.end() for m in SENTENCE_END.finditer(before) if m.end() >= len(head)])
    start += SENTENCE_LEAD.match(proof_v, start).end() - start
    return proof_v[:start].rstrip() + "\nShow.\nAbort.\n"


def shown_goals(log):
    """The goals `Show.` printed at the end of a compile log (time stamps and @@ records removed)."""
    lines = [rl.STAMP.sub(r"\2", line) for line in log.split("\n")]
    lines = [line for line in lines if not line.startswith("@@")]
    found = [i for i, line in enumerate(lines) if GOALS_LINE.match(line)]
    return "\n".join(lines[found[-1]:]).strip() if found else ""


def error_text(errors, state, limit):
    """The compiler errors, then the goal state (its end kept: the conclusion), within LIMIT bytes."""
    if not state:
        return clip(errors, limit)
    errors = clip(errors, max(limit * 2 // 3, limit - len(STATE_HEAD.encode()) - len(state.encode())))
    room = limit - len(errors.encode()) - len(STATE_HEAD.encode())
    if room < 2 * len(STATE_CUT):
        return errors
    data = state.encode()
    if len(data) > room:
        tail = data[len(data) - room + len(STATE_CUT):].decode(errors="ignore")
        state = STATE_CUT + (tail[tail.index("\n") + 1:] if "\n" in tail else tail)
    return errors + STATE_HEAD + state


def probe_compile(where, out, proof):
    """(ok, error) of PROOF for the goal of WHERE, compiled in the scratch dir OUT: goal.v copied, proof.v
    filled as `residual_loop.py collect` fills it, and a check.sh of the goal's bank under a scope of its
    own; on a failure ERROR is (compiler errors, goal state before the failing sentence from a second
    compile)."""
    out.mkdir(parents=True, exist_ok=True)
    goal_v = (where.goal_dir / "goal.v").read_text()
    head = rl.goal_head(goal_v)
    proof_v = head + proof.strip() + "\n"
    (out / "goal.v").write_text(goal_v)
    (out / "proof.v").write_text(proof_v)
    args, ocamlpath = rl.bank_args(where.manifest()["bank"])
    tag = "probe-" + uuid.uuid4().hex[:12]
    (out / "check.sh").write_text(rl.check_script(tag, args, ocamlpath))
    (out / "check.sh").chmod(0o755)
    verdict, _ = rl.run_check(out)
    if verdict == "PASS":
        return True, ""
    log = (out / "check.log").read_text(errors="replace") if (out / "check.log").is_file() else ""
    errors = rl.errors_of(log).strip() or "the check failed with no compiler output"
    show = show_text(proof_v, log, head)
    state = ""
    if show is not None:
        (out / "show.v").write_text(show)
        result = rl.scoped(out / "show.v", tag + "-show", args, ocamlpath)
        state = shown_goals(Path(result["log"]).read_text(errors="replace")) if result["returncode"] == 0 else ""
    return False, (errors, state)


class ProofProbe:
    """check_proof of one goal for one attempt: at most CALLS compiles of a proposed proof in the scratch
    dir RUN.../probes/<goal>/<tier>-<attempt>/<call>/ (never goals/, answers/ or the store), each under
    check_slots(). Thread-safe: an agent may call it in parallel. COMPILE(where, out, proof) -> (ok,
    error text or (errors, goal state)) replaces probe_compile in the tests."""

    def __init__(self, where, tier, attempt, calls=CHECK_CALLS, error_bytes=CHECK_ERROR_BYTES, compile=None,
                 slots=None):
        self.where, self.error_bytes = where, error_bytes
        self.scratch = where.d / "probes" / where.gid / ("%s-%d" % (tier, attempt))
        self.left, self.calls = calls, 0
        self.accepted = set()
        self.compile = compile or probe_compile
        self.slots = slots
        self.lock = threading.Lock()

    def __call__(self, proof):
        with self.lock:
            if self.left <= 0:
                return dict(ok=False, error="No check_proof calls left: send your answer.", remaining=0)
            self.left -= 1
            self.calls += 1
            call, remaining = self.calls, self.left
        if not isinstance(proof, str):
            return dict(ok=False, error="proof must be a string", remaining=remaining)
        problem = rl.answer_problems(proof.strip() + "\n")
        if problem:
            return dict(ok=False, error=problem, remaining=remaining)
        out = self.scratch / str(call)
        if out.exists():
            shutil.rmtree(out)
        with (self.slots or check_slots()):
            try:
                ok, error = self.compile(self.where, out, proof)
            except (OSError, subprocess.SubprocessError, KeyError, ValueError) as failure:
                ok, error = False, "check_proof could not run the check: %r" % failure
        if ok:
            with self.lock:
                self.accepted.add(proof.strip())
        if not ok and isinstance(error, tuple):
            error = error_text(error[0], error[1], self.error_bytes)
        return dict(ok=bool(ok), error="" if ok else clip(error, self.error_bytes), remaining=remaining)

    def final_check(self, proof):
        """True when the kernel accepts PROOF for this goal: at once when a check_proof call of this attempt
        accepted the same text, else one compile in the scratch dir `final/` (outside the call budget)."""
        if not isinstance(proof, str) or rl.answer_problems(proof.strip() + "\n"):
            return False
        if proof.strip() in self.accepted:
            return True
        out = self.scratch / "final"
        if out.exists():
            shutil.rmtree(out)
        with (self.slots or check_slots()):
            try:
                return bool(self.compile(self.where, out, proof)[0])
            except (OSError, subprocess.SubprocessError, KeyError, ValueError):
                return False


_GOAL_LOCKS = {}
_GOAL_LOCKS_LOCK = threading.Lock()


def goal_lock(where):
    """The lock of one goal's defs/ cache, shared by the samples of a round."""
    with _GOAL_LOCKS_LOCK:
        return _GOAL_LOCKS.setdefault(str(where.goal_dir), threading.Lock())


class LookupProbe:
    """lookup and search of one goal for one attempt: CALLS answers in all, each clipped to LOOKUP_BYTES; a
    name or pattern asked again in the attempt is answered from the attempt's cache and costs no call. The
    answers come from tools/oblig/defs.py with the goal's imports (defs.goal_resolver: About/Print or
    Search compiles under check_slots(), cached per goal in its defs/ dir, one query of a goal at a time).
    LOOKUP(name) and SEARCH(pattern) -> text replace defs.lookup_text and defs.search in the tests."""

    def __init__(self, where, calls, lookup=None, search=None, slots=None):
        self.where, self.left, self.slots = where, calls, slots
        self.lookups = self.searches = 0
        self.cache = {}
        self.lock = threading.Lock()
        self._lookup, self._search = lookup, search
        self._resolver = None

    def resolver(self):
        import defs
        if self._resolver is None:
            self._resolver = defs.goal_resolver(self.where.goal_dir)
        return self._resolver

    def answer(self, kind, key, fn):
        key = " ".join(str(key).split()) if isinstance(key, str) else None
        if not key:
            return dict(text="Give one non-empty string.", remaining=self.left)
        with self.lock:
            if (kind, key) in self.cache:
                return dict(text=self.cache[(kind, key)], remaining=self.left)
            if self.left <= 0:
                return dict(text="No lookup or search calls left: send your answer.", remaining=0)
            self.left -= 1
            if kind == LOOKUP_TOOL:
                self.lookups += 1
            else:
                self.searches += 1
            remaining = self.left
        import defs
        try:
            with goal_lock(self.where), (self.slots or check_slots()):
                text = fn(key)
        except (defs.DefsError, OSError, KeyError, ValueError, subprocess.SubprocessError) as failure:
            text = "%s could not run: %s" % (kind, failure)
        text = clip(text, LOOKUP_BYTES)
        with self.lock:
            self.cache[(kind, key)] = text
        return dict(text=text, remaining=remaining)

    def lookup(self, name):
        import defs
        return self.answer(LOOKUP_TOOL, name, self._lookup or (lambda n: defs.lookup_text(self.resolver(), n)))

    def search(self, pattern):
        import defs
        return self.answer(SEARCH_TOOL, pattern, self._search or (lambda p: defs.search(self.resolver(), p)))


def normal(text):
    return " ".join(str(text or "").split())


class CounterexampleProbe:
    """check_counterexample of one goal for one attempt: at most CALLS kernel refutations (Kernel.refutation,
    falsify.py's evaluator) in the scratch dir RUN.../probes/<goal>/<tier>-<attempt>/cex-<call>/. The goal's
    binders are probed once; when their types are outside falsify.py's range every call answers so (and
    costs no call after the first). `accepts(text)` is True only for an assignment a call confirmed.
    REFUTATION(where, text, out, binders) -> (confirmed, reason, binders) replaces it in the tests."""

    def __init__(self, where, tier, attempt, calls, refutation=None, slots=None):
        self.where, self.left, self.slots = where, calls, slots
        self.scratch = where.d / "probes" / where.gid / ("%s-%d" % (tier, attempt))
        self.refutation = refutation or Kernel().refutation
        self.calls, self.binders, self.unsupported = 0, None, None
        self.confirmed = []
        self.lock = threading.Lock()

    def __call__(self, assignment):
        if not isinstance(assignment, str) or not assignment.strip():
            return dict(confirmed=False, reason="assignment must be a non-empty string", remaining=self.left)
        with self.lock:
            if self.unsupported:
                return dict(confirmed=False, reason=self.unsupported, remaining=self.left)
            if self.left <= 0:
                return dict(confirmed=False, reason="No check_counterexample calls left: send your answer.",
                            remaining=0)
            self.left -= 1
            self.calls += 1
            call, remaining, binders = self.calls, self.left, self.binders
        out = self.scratch / ("cex-%d" % call)
        try:
            with (self.slots or check_slots()):
                ok, reason, binders = self.refutation(self.where, assignment, out, binders)
        except (OSError, subprocess.SubprocessError, KeyError, ValueError) as failure:
            ok, reason = False, "check_counterexample could not run the check: %r" % failure
        with self.lock:
            if binders is not None:
                self.binders = binders
            if reason.startswith("unsupported"):
                self.unsupported = reason
            if ok:
                self.confirmed.append(normal(assignment))
        return dict(confirmed=bool(ok), reason=reason, remaining=remaining)

    def accepts(self, text):
        return normal(text) in self.confirmed


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


def reopen(function, run, identifiers):
    """Reset each goal of IDENTIFIERS that is `failed` or `waiting-decision` with a `derived` event (its
    falsity verdict carried as `unblock` carries it): route.py runs its ladder again from the first tier,
    as after a changed task (here: the prompts a tier with the check tool sends). Returns the ids reset."""
    state, located = fold(run), locate(run, function)
    rows = []
    for identifier in identifiers:
        item = state.get(identifier)
        if item is None or item["kind"] not in ("goal", "meaning") or item["state"] not in ("failed",
                                                                                         "waiting-decision"):
            continue
        carried = carried_falsity(item, located.get(identifier))
        rows.append(base_event(item, state="derived", **{"class": item["goal_class"]},
                               tier="falsify" if carried else None, artifact=carried or item["artifact"]))
    if rows:
        store.append(run, rows)
    return [row["id"] for row in rows]


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


def sync_package_class(function, run, located, counts):
    """Bring a goal's class to its package record (package.py PACKAGE.json), no model: a package of class
    ADDRESS files `derived` class ADDRESS (route.py sends it to the statement owner); a goal filed ADDRESS
    whose package now has no class (its address literals became symbol notations, `symbols` in the
    record) files `derived` with its leftover class (replay.goal_class), so the ladder runs."""
    state, filed = fold(run), 0
    for identifier, item in state.items():
        where = located.get(identifier)
        if item["kind"] != "goal" or where is None or item["state"] in ("closed", "running", "superseded"):
            continue
        path = where.d / "package" / where.gid / "PACKAGE.json"
        record = store.read_json(path)
        if not record:
            continue
        if record.get("class") == "ADDRESS" and item["goal_class"] != "ADDRESS":
            cls = "ADDRESS"
        elif record.get("class") is None and record.get("symbols") and item["goal_class"] == "ADDRESS":
            cls = replay.goal_class(where.goal["statement"])
        else:
            continue
        store.append(run, base_event(item, state="derived", **{"class": cls}, artifact=store.artifact_of(path)))
        counts.bump("address" if cls == "ADDRESS" else "symbolized")
        filed += 1
    return filed


def escalate_unpromptable(function, run, located, free, counts, kernel):
    """For each model attempt route.py assigns, before any model sees it (no model):
    - a need_context retry whose named items no source can supply files `missing_context`;
    - a goal whose smallest task is over the default bound is re-packaged once at the tier cap
      (tiers.json `max_class_prompt_bytes`; PACKAGE.json `prompt_bound`, `bound_reason`) and then sent
      at that size, its attempts carrying `prompt_bound:<bytes>` in context_items;
    - a prompt over the bound it may use files `too_large` (file_too_large): waiting-decision with
      TOO-LARGE.json once every model tier is too small."""
    state, filed = fold(run), 0
    for identifier, action, tier, _ in route.next_items(run, function):
        if action != "prove" or tier in (None, MECHANICAL) or identifier not in free:
            continue
        count = samples(tier, state[identifier]["goal_class"])
        # Every sample of a best-of-N round must fit (their sections differ in length).
        for index in range(count):
            text, reason = prompt_for(run, function, identifier, tier, located=located, state=state,
                                      sample=(index, count))
            if text is None:
                break
        if text is not None:
            continue
        if reason == "missing_context":
            file_missing_context(run, identifier, tier)
            counts.bump("missing_context")
        elif reason.startswith(TOO_LARGE):
            where = located[identifier]
            if (state[identifier]["kind"] == "goal" and (large_bound(where, tier) is None or short_reserve(where, tier))
                    and tier_cap(tier) > max_prompt_bytes(tier, state[identifier]["goal_class"])):
                # Once per goal and reserve: package.py again at the tier cap less the prompt's additions;
                # the goal is then sent at that size.
                kernel.repackage(run, function, where, tier, tier_cap(tier), "smallest task over the "
                                 "default bound (%s)" % reason)
                counts.bump("repackaged_large")
                filed += 1
                continue
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
        progress += sync_package_class(function, run, located, counts)
        progress += escalate_unpromptable(function, run, located, free, counts, kernel)
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
