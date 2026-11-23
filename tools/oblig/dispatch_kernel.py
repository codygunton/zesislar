"""Kernel-side driver of the tier replay and of prover waves (plan A5). Load it in the coordinator's Python
eval kernel:

    import os; os.environ["ZESU_OBLIG_DIR"] = "<checkout>/tools/oblig"
    %load "<checkout>/tools/oblig/dispatch_kernel.py"

It is the only code that spawns models; tools/oblig/*.py call none. It uses the kernel helpers
`agent(prompt, agent=..., label=...)` (a handle with `.id`, `.wait(timeout)`, `.done()`), `wait(handles,
raise_errors=False)` and `tool.write(...)`.

    await set_tier_override(tier)   session task.agentModelOverrides for the tier's agent (the scout tiers);
                                    refuses while handles of another tier of that agent are unfinished
    run_wave(corpus, tier, recipe="similar", ids=None, sets=("known",), concurrency=16)
    retry_wave(corpus, tier, recipe="similar", ids=None, concurrency=16, attempt=2, resolver_for=None)

A tier maps to an agent through tools/oblig/tiers.json (`mechanical` runs no model). A wave registers each
attempt in the store before it spawns (store.py refuses a (prompt_sha256, tier) pair sent before),
spawns at most CONCURRENCY agents at a time, and writes each reply with package.write_answer
(replay.record_answer). Per answer it records prompt and answer bytes, and tokens and the resolved model
from the agent's session log (`~/.omp/agent/sessions/**/<id>.jsonl`: `usage` of each assistant message,
`resolvedModel` of session_init); a reply whose resolved model is not the tier's model is flagged
`model_mismatch` in WAVE.json. Check the answers afterwards with `replay.py check`; retry_wave writes the
second-attempt prompts (previous prompt plus the compiler errors, or the asked-for context: the definitions
or statements Rocq resolves for the names a `need_context` answer gives, and the closed lemmas it names;
replay.retry_plan) first. The Rocq queries of that step run in the calling process (stand-alone check
route, one guard scope each), before any agent starts.
"""
import json
import os
from pathlib import Path
import re
import sys

try:
    _OBLIG = Path(__file__).resolve().parent
except NameError:  # %load executes the text without __file__
    _OBLIG = Path(os.environ.get("ZESU_OBLIG_DIR", "tools/oblig")).resolve()
if str(_OBLIG) not in sys.path:
    sys.path.insert(0, str(_OBLIG))
import replay  # noqa: E402

SESSIONS = Path(os.environ.get("ZESU_AGENT_SESSIONS", str(Path.home() / ".omp/agent/sessions")))
WAIT_SECONDS = 3600
_STATE = {"overrides": {}, "live": []}


def base_overrides(root=None):
    """task.agentModelOverrides of the project config (.omp/config.yml of the main checkout)."""
    root = Path(root) if root else replay.main_checkout()
    text = (root / ".omp/config.yml").read_text() if (root / ".omp/config.yml").exists() else ""
    out, inside = {}, False
    for line in text.splitlines():
        if re.match(r"^\s+agentModelOverrides:\s*$", line):
            inside = True
            continue
        if inside:
            match = re.match(r"^\s{4,}([\w-]+):\s*(\S+)\s*$", line)
            if not match:
                break
            out[match[1]] = match[2]
    return out


def _finished(handle):
    """True when the handle is done, or the kernel no longer knows it (its result expired)."""
    try:
        return bool(handle.done())
    except Exception:  # RuntimeError('unknown agent handle ...; result expired') and the like
        return True


def _prune():
    """Drop finished (or expired) handles from the live list; returns the rest."""
    _STATE["live"] = [(tier, handle) for tier, handle in _STATE["live"] if not _finished(handle)]
    return _STATE["live"]


def _unfinished(agent_name, tier_name):
    """Live handles that run AGENT_NAME under another tier."""
    return [(t, h) for t, h in _prune() if t["agent"] == agent_name and t["name"] != tier_name]


async def set_tier_override(tier_name, tiers=None):
    """Point the tier's agent at its model for this session (cfg://task/agentModelOverrides)."""
    tier = replay.tier_row(tier_name, tiers)
    if not tier.get("override"):
        return None
    busy = _unfinished(tier["agent"], tier_name)
    if busy:
        raise replay.ReplayError("%d %s handles of tier %s are unfinished; wait for them first."
                                 % (len(busy), tier["agent"], busy[0][0]["name"]))
    overrides = dict(_STATE["overrides"] or base_overrides())
    overrides[tier["agent"]] = tier["override"]
    await tool.write({"path": "cfg://task/agentModelOverrides", "content": json.dumps(overrides)})  # noqa: F821
    _STATE["overrides"] = overrides
    _STATE["current"] = {tier["agent"]: tier_name}
    return overrides


def session_log(agent_id):
    found = sorted(SESSIONS.glob("*/*/%s.jsonl" % agent_id), key=lambda p: p.stat().st_mtime)
    return found[-1] if found else None


def usage(agent_id):
    """{tokens_in, tokens_out, resolved_model} from the agent's session log, None where absent."""
    out = dict(tokens_in=None, tokens_out=None, resolved_model=None)
    path = session_log(agent_id) if agent_id else None
    if path is None:
        return out
    tokens_in = tokens_out = 0
    seen = False
    for line in path.read_text(errors="replace").splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("type") == "session_init":
            out["resolved_model"] = row.get("resolvedModel")
        message = row.get("message") or {}
        if row.get("type") == "message" and message.get("role") == "assistant" and message.get("usage"):
            u = message["usage"]
            tokens_in += (u.get("input") or 0) + (u.get("cacheRead") or 0) + (u.get("cacheWrite") or 0)
            tokens_out += u.get("output") or 0
            seen = True
    if seen:
        out.update(tokens_in=tokens_in, tokens_out=tokens_out)
    return out


def _spawner(tier):
    def spawn(row, prompt):
        handle = agent(prompt, agent=tier["agent"], label="%s-%s" % (tier["name"], row["id"]))  # noqa: F821
        _STATE["live"].append((tier, handle))
        return handle
    return spawn


def _collector(tier, concurrency):
    def collect(pending):
        # spawn() already started every handle; waiting in slices bounds the collected batch only.
        out = []
        for start in range(0, len(pending), max(1, concurrency)):
            batch = pending[start:start + concurrency]
            replies = wait(batch, raise_errors=False)  # noqa: F821
            for handle, reply in zip(batch, replies):
                extra = usage(getattr(handle, "id", None))
                extra["agent_id"] = getattr(handle, "id", None)
                if isinstance(reply, BaseException):
                    extra["error"] = repr(reply)
                    reply = ""
                if tier.get("model") and extra.get("resolved_model") and extra["resolved_model"] != tier["model"]:
                    extra["model_mismatch"] = True
                out.append((reply, extra))
        return out
    return collect


def _batched_spawn(tier, concurrency):
    """spawn/collect pair that keeps at most CONCURRENCY agents alive: spawn returns a deferred item,
    collect starts and waits CONCURRENCY at a time."""
    def spawn(row, prompt):
        return (row, prompt)

    def collect(pending):
        out = []
        start_one = _spawner(tier)
        gather = _collector(tier, concurrency)
        for start in range(0, len(pending), max(1, concurrency)):
            handles = [start_one(row, prompt) for row, prompt in pending[start:start + concurrency]]
            out += gather(handles)
        return out
    return spawn, collect


def _check_override(tier):
    if tier.get("override") and _STATE.get("current", {}).get(tier["agent"]) != tier["name"]:
        raise replay.ReplayError("Run `await set_tier_override(%r)` before this wave." % tier["name"])
    busy = _unfinished(tier["agent"], tier["name"]) if tier.get("agent") else []
    if busy and tier.get("override"):
        raise replay.ReplayError("%d %s handles of tier %s are unfinished." % (len(busy), tier["agent"], busy[0][0]["name"]))


def run_wave(corpus, tier_name, recipe="similar", ids=None, sets=("known",), concurrency=16, attempt=1):
    """One wave of one tier over the corpus; returns replay.run_wave's summary."""
    tier = replay.tier_row(tier_name)
    if tier_name != "mechanical":
        _check_override(tier)
    spawn, collect = _batched_spawn(tier, concurrency)
    try:
        return replay.run_wave(corpus, tier_name, spawn, recipe=recipe, ids=ids, sets=sets, attempt=attempt,
                               collect=collect)
    finally:
        _prune()


def retry_wave(corpus, tier_name, recipe="similar", ids=None, concurrency=16, attempt=2, resolver_for=None):
    """The next attempt of a tier: prompts with the compiler error text (or the asked-for context),
    then a wave over exactly those goals. Run `replay.py check` on the previous attempt first."""
    chosen = replay.prepare_retry(corpus, tier_name, recipe, ids, attempt, resolver_for=resolver_for)
    if not chosen:
        return dict(tier=tier_name, recipe=recipe, attempt=attempt, started=0, rejected=[], verdicts={})
    return run_wave(corpus, tier_name, recipe=recipe, ids=chosen, sets=("known", "unknown"),
                    concurrency=concurrency, attempt=attempt)
