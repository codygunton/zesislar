"""Kernel-side production driver of one function's obligations (plan A7). Load it in the coordinator's
Python eval kernel:

    import os; os.environ["ZESU_OBLIG_DIR"] = "<checkout>/tools/oblig"
    %load "<checkout>/tools/oblig/drive_kernel.py"

    await set_tier_override(tier)        the scout tiers (haiku-medium, haiku-high) need it before their round
    run_round(function, run, tier=None, limit=16, concurrency=16, jobs=8)

run_round first runs `drive.step` (every routed action that needs no model: unblock, falsify,
mechanical, kernel checks), then takes the prover attempts `route.py next` assigns to a model tier
(only TIER when given; without it every tier whose agent needs no override, plus the override tier
set last), at most LIMIT. For each it builds the no-tools prompt from the obligation's task file
(drive.prompt_for: the answer form of package.py, the compiler errors after a compile error at the
same tier, the named items after need_context), registers the attempt in the store BEFORE spawning
(store.py refuses a (prompt_sha256, tier) pair sent before), spawns `agent(prompt, agent=<tier agent>,
label=...)` at most CONCURRENCY at a time, and writes each reply with drive.answer (package.write_answer)
with its prompt and answer bytes, tokens and resolved model (the session log reading of
dispatch_kernel.usage). Then it runs `drive.step` again, which kernel-checks the answers. Decision,
diagnosis and reconsider items (opus-medium) are not run here: the summary lists them.

It is the only code of this loop that spawns models; it uses the kernel helpers `agent`, `wait` and
`tool`, and shares the tier-override state of dispatch_kernel (one override tier per wave).
"""
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


class DriveError(RuntimeError):
    pass


def _helper(name):
    """A kernel helper (agent, wait, tool): the coordinator's kernel defines them as globals."""
    found = globals().get(name)
    if found is None:
        raise DriveError("No kernel helper `%s`: load this file in the coordinator's eval kernel." % name)
    return found


async def set_tier_override(tier_name):
    """dispatch_kernel.set_tier_override with this kernel's `tool` helper."""
    _dk.tool = _helper("tool")
    return await _dk.set_tier_override(tier_name)


def _override_problem(tier):
    """Why a wave of TIER may not start now, or None."""
    if not tier.get("override"):
        return None
    if _dk._STATE.get("current", {}).get(tier["agent"]) != tier["name"]:
        return "run `await set_tier_override(%r)` before this round" % tier["name"]
    busy = [t for t, h in _dk._prune() if t["agent"] == tier["agent"] and t["name"] != tier["name"]]
    if busy:
        return "%d %s handles of tier %s are unfinished" % (len(busy), tier["agent"], busy[0]["name"])
    return None


def _label(tier, identifier, attempt):
    name = re.sub(r"[^A-Za-z0-9]+", "-", identifier.rsplit("/", 1)[-1]).strip("-")
    return ("%s-%s-a%d" % (tier, name, attempt))[:48]


def _spawn(tier, prompt, label):
    handle = _helper("agent")(prompt, agent=tier["agent"], label=label)
    _dk._STATE["live"].append((tier, handle))
    return handle


def _usage(handle):
    agent_id = getattr(handle, "id", None)
    extra = _dk.usage(agent_id)
    extra["agent_id"] = agent_id
    return extra


def run_round(function, run, tier=None, limit=16, concurrency=16, jobs=8, kernel=None):
    """One prover round; returns a summary dict (also the step counts before and after). KERNEL
    replaces drive.Kernel (the compiles of step) in the tests."""
    run = Path(run)
    rows = _drive.tier_rows()
    before = _drive.step(function, run, jobs=jobs, kernel=kernel)[0]
    items = _drive.model_items(run, function, tier)
    skipped = {}
    allowed = []
    for name in dict.fromkeys(t for _, t, _ in items):
        row = rows.get(name)
        problem = ("no agent for tier %s in tiers.json" % name if row is None or not row.get("agent")
                   else _override_problem(row))
        if problem:
            skipped[name] = problem
        else:
            allowed.append(name)
    if tier is not None and tier in skipped:
        raise DriveError("tier %s: %s" % (tier, skipped[tier]))
    chosen = [item for item in items if item[1] in allowed][:limit]
    located = _drive.locate(run, function)
    started, refused = [], []
    for identifier, name, _ in chosen:
        prompt, context = _drive.prompt_for(run, function, identifier, name, located=located)
        if prompt is None:
            refused.append((identifier, name, context))
            continue
        try:
            attempt = _drive.register_attempt(run, function, identifier, name, prompt, context, located=located)
        except _store.Rejected as error:
            refused.append((identifier, name, str(error)))
            continue
        started.append((identifier, rows[name], attempt, prompt))
    verdicts, mismatched = {}, []
    wait = _helper("wait") if started else None
    try:
        for start in range(0, len(started), max(1, concurrency)):
            batch = started[start:start + concurrency]
            handles = [_spawn(row, prompt, _label(row["name"], identifier, attempt))
                       for identifier, row, attempt, prompt in batch]
            replies = wait(handles, raise_errors=False)
            for (identifier, row, attempt, prompt), handle, reply in zip(batch, handles, replies):
                extra = _usage(handle)
                if isinstance(reply, BaseException):
                    extra["error"] = repr(reply)
                    reply = ""
                if row.get("model") and extra.get("resolved_model") and extra["resolved_model"] != row["model"]:
                    extra["model_mismatch"] = True
                    mismatched.append(identifier)
                verdict = _drive.answer(run, function, identifier, row["name"], attempt, prompt, reply, extra,
                                        located=located)
                verdicts[verdict] = verdicts.get(verdict, 0) + 1
    finally:
        _dk._prune()
    after, left, running, unlocated = _drive.step(function, run, jobs=jobs, kernel=kernel)
    by_tier = {}
    for identifier, action, name, _ in left:
        if action == "prove" and name != _drive.MECHANICAL and identifier not in unlocated:
            by_tier[name] = by_tier.get(name, 0) + 1
    return dict(function=function, tiers=allowed, skipped=skipped, started=len(started), refused=refused,
                verdicts=verdicts, model_mismatch=mismatched, step_before=dict(before), step_after=dict(after),
                next_model=by_tier, deferred=[(i, a, t) for i, a, t, _ in left if a in DEFERRED],
                listed=sum(1 for _, a, _, _ in left if a not in DEFERRED and a != "prove"),
                running=running, unlocated=unlocated)


def next_tier(function, run):
    """The cheapest tier route.py assigns a prover attempt to, or None."""
    order = list(_drive.tier_rows())
    tiers = {t for _, t, _ in _drive.model_items(run, function)}
    return next((name for name in order if name in tiers), None)
