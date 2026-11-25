"""Kernel-side production driver of one function's obligations (plan A7). Load it in the coordinator's
Python eval kernel:

    import os; os.environ["ZESU_OBLIG_DIR"] = "<checkout>/tools/oblig"
    %load "<checkout>/tools/oblig/drive_kernel.py"

    run_round(function, run, tier=None, limit=16, concurrency=16, jobs=8)

run_round first runs `drive.step` (every routed action that needs no model: unblock, falsify,
mechanical, kernel checks), then takes the prover attempts `route.py next` assigns to a model tier
and drive's screen gate passes (drive.model_items; the summary's `held` counts the others by screen
verdict), only TIER when given, else every tier with an agent, at most LIMIT. For each it builds the prompt
from the obligation's task file
(drive.prompt_for: the answer form of package.py, the compiler errors after a compile error at the
same tier, the named items after need_context), registers the attempt in the store BEFORE spawning
(store.py refuses a (prompt_sha256, tier) pair sent before), spawns `agent(prompt, agent=<tier agent>,
label=..., model=<tier model when the row says per_call_model>)` (dispatch_kernel.spawn_options; the Haiku
tiers run the agent `rocq-prover` of .omp/agents/ at a per-call model) at most CONCURRENCY at a time,
and writes each reply with drive.answer (package.write_answer)
with its prompt and answer bytes, tokens and resolved model (the session log reading of
dispatch_kernel.usage). Then it runs `drive.step` again, which kernel-checks the answers. Decision,
diagnosis and reconsider items (opus-medium) are not run here: the summary lists them.

A tier with prover tools in tiers.json (drive.tool_budgets) gets drive.TOOLS_HEAD as its preamble,
and each of its agents gets kernel tools of its own (`tool(fn, name=...)`, passed in `agent(...,
tools=[names])`, undefined when the batch ends), bound to that agent's goal and attempt and run in this
kernel's threads under drive.check_slots(): `check_proof_<n>` (drive.ProofProbe, `check_calls`),
`lookup_<n>` and `search_<n>` (drive.LookupProbe, `lookup_calls` together), `check_counterexample_<n>`
(drive.CounterexampleProbe, `counterexample_calls`). A tier with `samples` N spawns N agents per goal
(prompts varied by drive.sample_prompt, registered as one round), settled by drive.settle_round. The
reply is still checked by `drive.step`; the tool calls go to the answer record and to the attempt's
result event (`check_calls:<n>`, `lookup_calls:<n>`, `search_calls:<n>`, `counterexample_calls:<n>`
in context_items).

It is the only code of this loop that spawns models; it uses the kernel helpers `agent`, `wait` and
`tool`, and shares the live-handle list of dispatch_kernel.
"""
import itertools
import os
from pathlib import Path
import re
import sys

if __name__ == "drive_kernel" or not os.environ.get("ZESU_OBLIG_DIR"):
    _OBLIG = Path(__file__).resolve().parent
else:  # %load executes the text in the kernel's namespace, whose __file__ is not this file
    _OBLIG = Path(os.environ["ZESU_OBLIG_DIR"]).resolve()
while str(_OBLIG) in sys.path:
    sys.path.remove(str(_OBLIG))
sys.path.insert(0, str(_OBLIG))
# A module of another checkout already imported in this kernel would shadow this one's.
for _name in ("dispatch_kernel", "drive", "store", "route", "package", "replay", "falsify", "similar",
              "residual_loop", "residual_package", "render_residual_module"):
    _module = sys.modules.get(_name)
    if _module is not None and _OBLIG.parent not in Path(getattr(_module, "__file__", "/")).resolve().parents:
        del sys.modules[_name]
import dispatch_kernel as _dk  # noqa: E402
import drive as _drive  # noqa: E402
import store as _store  # noqa: E402

DEFERRED = ("decide", "diagnose", "reconsider")
CHECK_DESCRIPTION = (
    "Compile a proof script of your lemma. Argument `proof`: the text of your answer's `proof` field (the proof "
    "script only, ending with exactly one `Qed.`). Returns {ok, error, remaining}: ok true when Rocq accepts "
    "the lemma with this proof; else error holds the compiler error and the goal state before the failing "
    "sentence (clipped); remaining is the number of calls left.")
LOOKUP_DESCRIPTION = (
    "The definition of one identifier of your lemma's world (for a lemma or an opaque constant: its statement), "
    "with the lemma's own imports. Argument `name`: one qualified identifier, e.g. `arrayListLength` or "
    "`Z.mul_comm`. Returns {text, remaining}; asking for a name again is free.")
SEARCH_DESCRIPTION = (
    "Rocq `Search <pattern>` with your lemma's own imports. Argument `pattern`: the pattern only, without a final "
    "dot, e.g. `(_ * 32)%Z` or `bv_unsigned \"shiftl\"`. Returns {text, remaining} (at most 40 lines); shares "
    "the budget of lookup.")
COUNTEREXAMPLE_DESCRIPTION = (
    "Ask the kernel whether your lemma is false at given values. Argument `assignment`: `x = 5, w = 0xff, b = "
    "true`, one value per universally quantified variable (a variable you do not name takes a default value). "
    "Returns {confirmed, reason, remaining}; answer `false` only with an assignment this tool confirmed.")
_TOOL_COUNT = itertools.count(1)
# The prover answer form (package.py) as the agent's output schema: an agent whose own schema wraps its
# reply (scout: architecture, files, report) answers in this form instead.
ANSWER_SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string", "enum": list(_drive.package.VERDICTS)},
        "proof": {"type": "string"},
        "needs": {"type": "array", "items": {"type": "string"}},
        "counterexample": {"type": "string"},
    },
    "required": ["verdict"],
}
resolve_needs = _drive.resolve_needs


class DriveError(RuntimeError):
    pass


def _helper(name):
    """A kernel helper (agent, wait, tool): the coordinator's kernel defines them as globals."""
    found = globals().get(name)
    if found is None:
        raise DriveError("No kernel helper `%s`: load this file in the coordinator's eval kernel." % name)
    return found


def _label(tier, identifier, attempt):
    name = re.sub(r"[^A-Za-z0-9]+", "-", identifier.rsplit("/", 1)[-1]).strip("-")
    return ("%s-%s-a%d" % (tier, name, attempt))[:48]


def _tools(row, where, attempt):
    """(tool names, probes) of the prover tools of one attempt at the tier ROW (drive.tool_budgets): a
    check_proof (drive.ProofProbe), lookup and search (one drive.LookupProbe) and check_counterexample
    (drive.CounterexampleProbe) bound to the goal of WHERE and this attempt; check_proof first. Each is a
    kernel tool of its own (`<tool>_<n>`), undefined when its batch ends."""
    budgets = _drive.tool_budgets(row["name"])
    define = _helper("tool") if budgets else None
    names, probes = [], {}
    number = next(_TOOL_COUNT)
    if _drive.CHECK_TOOL in budgets:
        probe = probes["proof"] = _drive.ProofProbe(where, row["name"], attempt, calls=budgets[_drive.CHECK_TOOL])

        def check_proof(proof: str) -> dict:
            return probe(proof)
        names.append(_define(define, check_proof, _drive.CHECK_TOOL, number, CHECK_DESCRIPTION))
    if _drive.LOOKUP_TOOL in budgets:
        found = probes["lookup"] = _drive.LookupProbe(where, budgets[_drive.LOOKUP_TOOL])

        def lookup(name: str) -> dict:
            return found.lookup(name)

        def search(pattern: str) -> dict:
            return found.search(pattern)
        names.append(_define(define, lookup, _drive.LOOKUP_TOOL, number, LOOKUP_DESCRIPTION))
        names.append(_define(define, search, _drive.SEARCH_TOOL, number, SEARCH_DESCRIPTION))
    if _drive.COUNTEREXAMPLE_TOOL in budgets:
        refuter = probes["counterexample"] = _drive.CounterexampleProbe(
            where, row["name"], attempt, budgets[_drive.COUNTEREXAMPLE_TOOL])

        def check_counterexample(assignment: str) -> dict:
            return refuter(assignment)
        names.append(_define(define, check_counterexample, _drive.COUNTEREXAMPLE_TOOL, number,
                             COUNTEREXAMPLE_DESCRIPTION))
    return names, probes


def _define(define, fn, tool, number, description):
    name = "%s_%d" % (tool, number)
    fn.__doc__ = description
    define(fn, name=name, description=description)
    return name


def _tool_counts(probes):
    """The tool-call fields of an attempt's answer record (drive.TOOL_COUNTS) for the probes it had."""
    out = {}
    if "proof" in probes:
        out["check_calls"] = probes["proof"].calls
    if "lookup" in probes:
        out.update(lookup_calls=probes["lookup"].lookups, search_calls=probes["lookup"].searches)
    if "counterexample" in probes:
        out["counterexample_calls"] = probes["counterexample"].calls
    return out


def _spawn(tier, prompt, label, tool_names=()):
    options = dict(tools=list(tool_names)) if tool_names else {}
    handle = _helper("agent")(prompt, label=label, schema=ANSWER_SCHEMA, **_dk.spawn_options(tier), **options)
    _dk._STATE["live"].append((tier, handle))
    return handle


def _usage(handle):
    agent_id = getattr(handle, "id", None)
    extra = _dk.usage(agent_id)
    extra["agent_id"] = agent_id
    return extra


def _register_samples(run, function, identifier, name, located, refused):
    """[(attempt, prompt)] of the samples of one round of IDENTIFIER at tier NAME (drive.samples), each
    registered running with context items `sample:<i>/<n>` and `round:<first attempt>` when n > 1. A
    refusal of the first sample is filed as before (missing_context, too_large, repeated_prompt) and
    listed in REFUSED; a later sample the store or the prompt bound refuses is left out of the round."""
    state = _drive.fold(run)
    item = state[identifier]
    count = _drive.samples(name, item["goal_class"])
    first = item["tier_attempts"].get(name, 0) + 1
    out = []
    for index in range(count):
        # Every sample's prompt follows the goal's state before the round (its last result, not a sibling).
        prompt, context = _drive.prompt_for(run, function, identifier, name, located=located, state=state,
                                            sample=(index, count))
        if prompt is None:
            if index == 0:
                if context == "missing_context":
                    _drive.file_missing_context(run, identifier, name)
                elif context.startswith(_drive.TOO_LARGE):
                    _drive.file_too_large(run, identifier, name, context, located)
                refused.append((identifier, name, context))
            break
        if count > 1:
            context = list(context) + ["sample:%d/%d" % (index + 1, count), "round:%d" % first]
        try:
            out.append((_drive.register_attempt(run, function, identifier, name, prompt, context, located=located),
                        prompt))
        except _store.Rejected as error:
            if index == 0:
                _drive.file_repeated_prompt(run, identifier, name)
                refused.append((identifier, name, str(error)))
                break
    return out


def run_round(function, run, tier=None, limit=16, concurrency=16, jobs=8, kernel=None, only=None):
    """One prover round; returns a summary dict (also the step counts before and after). ONLY, when
    given, limits the prover attempts to those obligation ids (a probe round). KERNEL replaces
    drive.Kernel (the compiles of step) in the tests. LIMIT counts goals; a goal at a tier with
    `samples` N gets N agents (drive.sample_prompt), settled by drive.settle_round; CONCURRENCY counts
    agents."""
    run = Path(run)
    rows = _drive.tier_rows()
    before = _drive.step(function, run, jobs=jobs, kernel=kernel)[0]
    items = [item for item in _drive.model_items(run, function, tier) if only is None or item[0] in set(only)]
    skipped = {}
    allowed = []
    for name in dict.fromkeys(t for _, t, _ in items):
        row = rows.get(name)
        if row is None or not row.get("agent"):
            skipped[name] = "no agent for tier %s in tiers.json" % name
        else:
            allowed.append(name)
    if tier is not None and tier in skipped:
        raise DriveError("tier %s: %s" % (tier, skipped[tier]))
    chosen = [item for item in items if item[1] in allowed][:limit]
    located = _drive.locate(run, function)
    started, refused, groups = [], [], []
    for identifier, name, _ in chosen:
        group = []
        for attempt, prompt in _register_samples(run, function, identifier, name, located, refused):
            entry = dict(identifier=identifier, row=rows[name], attempt=attempt, prompt=prompt)
            group.append(entry)
            started.append(entry)
        if group:
            groups.append(group)
    verdicts, mismatched, calls = {}, [], {key: 0 for key in _drive.TOOL_COUNTS}
    wait = _helper("wait") if started else None
    if started:
        _drive.check_slots(renew=True)
    try:
        for start in range(0, len(started), max(1, concurrency)):
            batch = started[start:start + concurrency]
            names, handles = [], []
            try:
                for entry in batch:
                    tool_names, entry["probes"] = _tools(entry["row"], located[entry["identifier"]], entry["attempt"])
                    names += tool_names
                    handles.append(_spawn(entry["row"], entry["prompt"],
                                          _label(entry["row"]["name"], entry["identifier"], entry["attempt"]),
                                          tool_names))
                replies = wait(handles, raise_errors=False)
            finally:
                for tool_name in names:
                    _helper("tool").undefine(tool_name)
            for entry, handle, reply in zip(batch, handles, replies):
                extra = _usage(handle)
                if isinstance(reply, BaseException):
                    extra["error"] = repr(reply)
                    reply = ""
                row = entry["row"]
                if row.get("model") and extra.get("resolved_model") and extra["resolved_model"] != row["model"]:
                    extra["model_mismatch"] = True
                    mismatched.append(entry["identifier"])
                extra.update(_tool_counts(entry["probes"]))
                for key in _drive.TOOL_COUNTS:
                    calls[key] += extra.get(key, 0)
                entry.update(reply=reply, extra=extra)
        for group in groups:
            samples = [dict(attempt=e["attempt"], prompt=e["prompt"], reply=e.get("reply", ""), extra=e.get("extra"),
                            proof=e.get("probes", {}).get("proof"),
                            counterexample=e.get("probes", {}).get("counterexample")) for e in group]
            for verdict in _drive.settle_round(run, function, group[0]["identifier"], group[0]["row"]["name"],
                                               samples, located=located):
                verdicts[verdict] = verdicts.get(verdict, 0) + 1
    finally:
        _dk._prune()
    after, left, running, unlocated = _drive.step(function, run, jobs=jobs, kernel=kernel)
    by_tier = {}
    for identifier, action, name, _ in left:
        if action == "prove" and name != _drive.MECHANICAL and identifier not in unlocated:
            by_tier[name] = by_tier.get(name, 0) + 1
    return dict(function=function, tiers=allowed, skipped=skipped, started=len(started), goals=len(groups),
                refused=refused, verdicts=verdicts, model_mismatch=mismatched, step_before=dict(before),
                step_after=dict(after), next_model=by_tier, held=_drive.held_counts(left),
                deferred=[(i, a, t) for i, a, t, _ in left if a in DEFERRED],
                listed=sum(1 for _, a, _, _ in left if a not in DEFERRED and a not in ("prove", _drive.HELD)),
                running=running, unlocated=unlocated, check_calls=calls["check_calls"], tool_calls=calls)


def next_tier(function, run):
    """The cheapest tier route.py assigns a prover attempt to, or None."""
    order = list(_drive.tier_rows())
    tiers = {t for _, t, _ in _drive.model_items(run, function)}
    return next((name for name in order if name in tiers), None)
