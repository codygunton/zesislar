#!/usr/bin/env python3
"""Tier replay of the prover tiers (plan A5). It calls no model: dispatch_kernel.py spawns the agents.

    replay.py corpus   --out DIR --bank BANK [--ocamlpath DIR] [--leftovers DIR ...] [--jobs N]
    replay.py falsify  --corpus DIR [--set unknown] [--jobs N]
    replay.py wave     --corpus DIR --tier mechanical [--recipe R]       (the model-free tier)
    replay.py check    --corpus DIR --tier T [--recipe R] [--attempt N] [--jobs N]
    replay.py original --corpus DIR --ids ID ... [--corrupt ID]          (self-test of the check route)
    replay.py status   --corpus DIR
    replay.py routing  --corpus DIR [--out tools/oblig/routing.json] [--min-share 0.5]

corpus writes DIR (outside the source tree) with two sets of pure goals, each a goal dir in the
layout of tools/block/residual_loop.py (goals/<id>/goal.v with PROOF-SLOT, roundtrip.v, check.sh):
- `known` (ids k001..): the lemmas of the residual modules ZesuSsz/Residuals/Block800d*.v (68 on
  the plan's tree), each renamed to `replay_<id>` with its proof withheld. The import header is the
  module's. The shared module DecodeItemBridges.v gives similar-lemma context only.
- `unknown` (ids u001..): the unique statements (by sha256) of the `leftover/Goal*.v` files under
  --leftovers (default _build/agents/rebuild and _build/agents/bench of the main checkout), with
  `Require` lines for the modules their qualified names live in (falsify.leftover_requires).
Each goal is reparsed (residual_loop.reparse): the readable goal after `intros.` is what the task
shows. The task of a recipe is the rules of residual_loop.py's TASK, the readable goal, the path of
the exact goal.v, the imports, the recipe's context and the answer form of package.py (JSON
verdict). Recipes: `slice` (the exported premise slice only), `similar` (plus the 3 nearest closed
lemmas of similar.py, never the lemma itself, a lemma with its statement or one with its
conclusion), `hints` (plus the hint slice, when a hint pack exists; none for these goals). A task
above the tier's max_prompt_bytes is not sent (`fits` false). No task names a repository path or
the original lemma; ORIGINS.json maps ids to their sources for the self-test only.
CORPUS.json: one row per goal: id, set, store id, name, class, conclusion head, statement sha256
and bytes, reparse, readable bytes, and per recipe the task path, bytes, sha256 and context items.
Classes: tools/bench/triage_classes.json on `pure <conclusion>` (the size limit of PURE ignored),
with PURE split by the conclusion head into PURE-linear, PURE-bitvector, PURE-byte-window and
PURE-meaning.

An attempt (tier T, recipe R, number N) lives in DIR/attempts/R/T/: the store log OBLIGATIONS.jsonl
of tools/oblig/store.py (one per recipe and tier, so each tier is measured on the same goals
independently; the repeated (prompt_sha256, tier) rule applies) and a<N>/ with prompts/<id>.md,
answers/<id>.json and .v (package.write_answer), WAVE.json (agent id, resolved model, tokens,
bytes), checks/<id>/ (proof.v, check.sh) and feedback/<id>.txt. check compiles each `proved` answer
with the stand-alone route of residual_loop.py (check.sh of residual_package.py: one resource-guard
scope, 1 GiB booking) and appends `closed` or `failed` (compile_error); a `false` verdict is
checked with falsify.py's kernel refutation on the binder values the answer names (state `false`
when the kernel accepts it, else failed bad_counterexample; on a known-true goal it is failed
wrong_false). routing writes the per-class first tier (rule in the file), attempts, context recipe
and the per-tier shares, and the 50% rule of the plan (do the three Haiku tiers together close at
least half of the known set?).
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
sys.path.insert(0, str(ROOT / "tools/bench"))
import residual_loop as rl  # noqa: E402
import package  # noqa: E402
import similar  # noqa: E402
import store  # noqa: E402
import triage  # noqa: E402
import bench_report  # noqa: E402

FUNCTION = "replay"
CASE = "0000"
TIERS_FILE = HERE / "tiers.json"
ROUTING_FILE = HERE / "routing.json"
RECIPES = ("slice", "similar", "hints")
HAIKU = ("haiku-low", "haiku-medium", "haiku-high")
MIN_SHARE = 0.5
MIN_GOALS = 3
CHECK_PEAK_GIB = 1.0
ROUNDTRIP_PEAK_GIB = 1.5
FALSE_CLASSES = ("wrong_false", "bad_counterexample")


class ReplayError(ValueError):
    pass


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def main_checkout():
    proc = subprocess.run(["git", "rev-parse", "--git-common-dir"], cwd=ROOT, capture_output=True, text=True)
    return (ROOT / proc.stdout.strip()).resolve().parent if proc.returncode == 0 else ROOT


def load_tiers(path=TIERS_FILE):
    return json.loads(Path(path).read_text())["tiers"]


def tier_row(name, tiers=None):
    for row in tiers or load_tiers():
        if row["name"] == name:
            return row
    raise ReplayError("No tier %s in tiers.json." % name)


def jobs_for(peak_gib, requested=None):
    """Workers from 70 percent of available memory and the measured peak per task (AGENTS.md)."""
    if requested:
        return requested
    available = 0
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            available = int(line.split()[1]) / (1 << 20)
    return max(1, min(os.cpu_count() or 1, int(0.7 * available / peak_gib)))


# ---- classes ----

RELATIONS = {"eq", "@eq", "=", "<>", "<", "<=", ">", ">=", "≤", "≥", "≠", "Z.lt", "Z.le", "Z.gt", "Z.ge", "lt", "le",
             "gt", "ge", "Nat.lt", "Nat.le", "N.lt", "N.le", "/\\", "\\/", "∧", "∨", "<->", "not", "~", "True", "False",
             "or", "and", "iff", "ex"}
BYTE_WINDOW = re.compile(r"\b(take|drop|firstn|skipn|app|sublist|lookup|nth|nth_error|length|repeat|seq)\b|\+\+")
BITVECTOR = re.compile(r"\b(bv_[a-z_]+|bv|BV|Z_to_bv|bv_unsigned|bv_signed|bv_concat|bv_extract)\b")


def pure_kind(conclusion):
    names, body = similar.split_binders(conclusion)
    head = similar.head_of(body, set(names))
    short = head.lstrip("@").split(".")[-1]
    qualified = head.lstrip("@")
    if head not in RELATIONS and short not in RELATIONS and qualified not in RELATIONS and not \
            qualified.startswith(("Coq.", "stdpp.")) and re.match(r"[A-Za-z_]", short or ""):
        return "meaning"
    if BYTE_WINDOW.search(body):
        return "byte-window"
    if BITVECTOR.search(body):
        return "bitvector"
    return "linear"


_CLASSES = None


def goal_class(statement):
    """The leftover class of a pure statement (triage_classes.json), PURE split by conclusion head."""
    global _CLASSES
    if _CLASSES is None:
        _CLASSES = triage.load_classes()
    conclusion = " ".join(bench_report.conclusion_of(statement).split())
    found = triage.classify("pure " + conclusion, 0, _CLASSES)
    if found in ("PURE", triage.UNCLASSIFIED):
        return "PURE-" + pure_kind(conclusion)
    return found


# ---- prompts ----

RULES = rl.TASK[rl.TASK.index("Rules:\n"):rl.TASK.index("\n\nLemma name:")]
PROMPT = """# Pure goal {gid}

Prove the Rocq lemma below. Work from this task alone: the only file you may read is the exact
source named below. Do not search other files for the lemma or its proof.

{rules}

Lemma name: `{name}`

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


def base_prompt(corpus, row, header):
    return PROMPT.format(gid=row["id"], rules=RULES, name=row["name"], readable=row["readable"],
                         goal=Path(corpus) / "goals" / row["id"] / "goal.v", header="\n".join(header))


def answer_form(gid):
    return "\n" + package.ANSWER_FORM.format(answer="answers/%s.v" % gid)


def norm(text):
    return " ".join(text.split())


def similar_for(index, statement, budget):
    """The nearest closed lemmas: never one with this statement or this conclusion (a textual duplicate)."""
    own = norm(bench_report.conclusion_of(statement))
    entries = [e for e in index["entries"] if e["statement_sha256"] != sha(statement.strip())
               and norm(bench_report.conclusion_of(e["statement"])) != own]
    return similar.nearest(dict(index, entries=entries), statement, similar.K, max(0, budget))


def recipe_prompts(corpus, row, header, index, max_bytes):
    """{recipe: (text, context items, similar names)}; a recipe without its context item is absent."""
    base = base_prompt(corpus, row, header)
    tail = answer_form(row["id"])
    out = {"slice": (base + tail, [], [])}
    budget = max_bytes - len((base + tail).encode()) - 2
    found = similar_for(index, row["statement"], budget)
    while found and len((base + "\n" + similar.section(found) + tail).encode()) > max_bytes:
        found = found[:-1]
    if found:
        out["similar"] = (base + "\n" + similar.section(found) + tail, ["similar"], [e["name"] for _, e in found])
    hints = package.hint_slice(row.get("hints"), ["+0x" + row.get("block", CASE)], budget)
    if hints:
        out["hints"] = (base + "\n" + hints + tail, ["hints"], [])
    return out


# ---- corpus ----

def known_lemmas(residuals=rl.RESIDUALS):
    """[(module path, header lines, lemma name, statement, proof)] of the Block800d*.v modules."""
    out = []
    for path in sorted(Path(residuals).glob("Block800d*.v")):
        _, header, rows = rl.rrm.parse_module(path.read_text())
        for row in rows:
            match = similar.LEMMA_TEXT.search(row["body"] + "\n")
            out.append((path, header, row["name"], match["stmt"].strip(), match["proof"].strip()))
    return out


def leftover_files(roots):
    files = []
    for root in roots:
        files += sorted(Path(root).rglob("leftover/Goal*.v"))
    return files


def unknown_statements(roots):
    """[(statement, [source paths])] unique by statement sha256, in path order."""
    import falsify
    seen, out = {}, []
    for path in leftover_files(roots):
        try:
            _, statement, _ = falsify.read_goal(path)
        except falsify.FalsifyError:
            continue
        key = sha(statement)
        if key in seen:
            seen[key][1].append(str(path))
            continue
        seen[key] = (statement, [str(path)])
        out.append(seen[key])
    return out


def leftover_header(statement, args, coqlib):
    import falsify
    requires = falsify.leftover_requires(statement, falsify.load_roots(args, coqlib))
    return [rl.CORE_IMPORT, "From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.",
            "Require Import stdpp.bitvector.definitions."] + requires + [rl.SCOPE_LINE]


def coqlib_of(args):
    proc = subprocess.run([args[0], "-where"], capture_output=True, text=True)
    return proc.stdout.strip() if proc.returncode == 0 else ""


def prepare_goal(corpus, row, header, args, ocamlpath):
    """Write the goal dir and reparse the statement; a finished round trip of the same files is reused."""
    d = Path(corpus) / "goals" / row["id"]
    d.mkdir(parents=True, exist_ok=True)
    goal = rl.goal_text(header, row["name"], row["statement"])
    roundtrip = rl.roundtrip_text(header, row["statement"])
    log = d / "roundtrip.log"
    reuse = ((d / "goal.v").exists() and (d / "goal.v").read_text() == goal and (d / "roundtrip.v").read_text() == roundtrip
             and log.exists() and "@@CPU" in log.read_text(errors="replace"))
    (d / "goal.v").write_text(goal)
    (d / "roundtrip.v").write_text(roundtrip)
    (d / "check.sh").write_text(rl.check_script("replay-" + row["id"], args, ocamlpath))
    (d / "check.sh").chmod(0o755)
    if reuse:
        text = log.read_text(errors="replace")
        again = rl.last_record(text, "@@X roundtrip ")
        found = dict(reparse="fails" if again is None else "exact" if again == row["statement"] else "differs",
                     readable=rl.readable(text) if again is not None else "")
    else:
        found = rl.reparse(d, "rt-replay-" + row["id"], row["statement"], args, ocamlpath)
    row.update(reparse=found["reparse"], readable=found.get("readable", ""))
    return row


def cmd_corpus(a):
    corpus = Path(a.out).resolve()
    if corpus.exists() and any(corpus.iterdir()) and not a.resume:
        raise ReplayError("The corpus dir is not empty: %s (--resume reuses its finished round trips)" % corpus)
    corpus.mkdir(parents=True, exist_ok=True)
    args, lib = rl.bank_args(a.bank)
    ocamlpath = a.ocamlpath or lib
    coqlib = coqlib_of(args)
    rows, headers, origins = [], {}, {}
    for n, (path, header, name, statement, proof) in enumerate(known_lemmas(), 1):
        gid = "k%03d" % n
        rows.append(dict(id=gid, set="known", statement=statement))
        headers[gid] = header
        origins[gid] = dict(module=str(path.relative_to(ROOT)), lemma=name, proof=proof)
    roots = a.leftovers or [main_checkout() / "_build/agents/rebuild", main_checkout() / "_build/agents/bench"]
    for n, (statement, sources) in enumerate(unknown_statements(roots), 1):
        gid = "u%03d" % n
        rows.append(dict(id=gid, set="unknown", statement=statement))
        headers[gid] = leftover_header(statement, args, coqlib)
        origins[gid] = dict(sources=sources)
    for n, row in enumerate(rows, 1):
        row.update(name="replay_" + row["id"], store_id=store.goal_id(FUNCTION, "%04x" % n, row["statement"]),
                   statement_sha256=sha(row["statement"]), statement_bytes=len(row["statement"].encode()),
                   **{"class": goal_class(row["statement"])},
                   conclusion_head=similar.keys(row["statement"])[0])
    with ThreadPoolExecutor(max_workers=jobs_for(ROUNDTRIP_PEAK_GIB, a.jobs)) as pool:
        list(pool.map(lambda row: prepare_goal(corpus, row, headers[row["id"]], args, ocamlpath), rows))
    index = similar.build_index()
    max_bytes = tier_row("haiku-low")["max_prompt_bytes"]
    for row in rows:
        row["readable_bytes"] = len(row["readable"].encode())
        row["prompts"] = {}
        if not row["readable"]:
            continue
        for recipe, (text, items, names) in recipe_prompts(corpus, row, headers[row["id"]], index, max_bytes).items():
            path = corpus / "tasks" / recipe / ("%s.md" % row["id"])
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            row["prompts"][recipe] = dict(path=str(path), bytes=len(text.encode()), sha256=sha(text),
                                          context_items=items, similar=names,
                                          fits=len(text.encode()) <= max_bytes)
    manifest = dict(block=CASE, bank=str(Path(a.bank).resolve()), caller=None, rounds=1, skipped=[], exports=[],
                    reruns=[], goals=[dict(id=r["id"], name=r["name"], statement=r["statement"], reparse=r["reparse"],
                                           readable=r["readable"], binders=[], counts={}) for r in rows])
    rl.write_json(corpus / "MANIFEST.json", manifest)
    rl.write_json(corpus / "ORIGINS.json", origins)
    head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    data = dict(schema="oblig-replay-corpus/1", head=head, bank=str(Path(a.bank).resolve()), ocamlpath=ocamlpath,
                max_prompt_bytes=max_bytes, recipes=list(RECIPES),
                rows=[{k: v for k, v in r.items() if k not in ("statement", "readable")} for r in rows])
    rl.write_json(corpus / "CORPUS.json", data)
    print_corpus(data)


def print_corpus(data):
    for name in ("known", "unknown"):
        rows = [r for r in data["rows"] if r["set"] == name]
        line = "CORPUS %s goals=%d exact=%d" % (name, len(rows), sum(r["reparse"] == "exact" for r in rows))
        for recipe in RECIPES:
            line += " %s=%d/%d" % (recipe, sum(r["prompts"].get(recipe, {}).get("fits", False) for r in rows),
                                   sum(recipe in r["prompts"] for r in rows))
        classes = {}
        for r in rows:
            classes[r["class"]] = classes.get(r["class"], 0) + 1
        print(line + " classes=" + ",".join("%s:%d" % kv for kv in sorted(classes.items())))


def load_corpus(corpus):
    data = rl.read_json(Path(corpus) / "CORPUS.json")
    if data is None:
        raise ReplayError("No CORPUS.json in %s." % corpus)
    manifest = rl.read_json(Path(corpus) / "MANIFEST.json")
    by_id = {g["id"]: g for g in manifest["goals"]}
    for row in data["rows"]:
        row["statement"] = by_id[row["id"]]["statement"]
    return data


def eligible(data, recipe, ids=None, sets=("known",)):
    """Rows whose task of RECIPE fits the prompt bound (and the falsity check did not refute)."""
    out = []
    for row in data["rows"]:
        if ids is not None and row["id"] not in ids:
            continue
        if ids is None and row["set"] not in sets:
            continue
        prompt = row["prompts"].get(recipe) if recipe != "none" else dict(fits=True)
        if not prompt or not prompt.get("fits") or row.get("falsify", {}).get("verdict") == "false":
            continue
        out.append(row)
    return out


# ---- falsify on the unknown set ----

def cmd_falsify(a):
    import falsify
    corpus = Path(a.corpus)
    data = load_corpus(corpus)
    route = falsify.Route(data["bank"], data["ocamlpath"])
    rows = [r for r in data["rows"] if r["set"] in a.set]

    def one(row):
        report = falsify.check(corpus / "goals" / row["id"] / "goal.v", route,
                               corpus / "goals" / row["id"] / "falsify")
        row["falsify"] = dict(verdict=report["verdict"], reason=report.get("reason"))
        return row

    with ThreadPoolExecutor(max_workers=jobs_for(2.0, a.jobs)) as pool:
        list(pool.map(one, rows))
    save_corpus(corpus, data)
    counts = {}
    for row in rows:
        counts[row["falsify"]["verdict"]] = counts.get(row["falsify"]["verdict"], 0) + 1
    print("FALSIFY " + " ".join("%s=%d" % kv for kv in sorted(counts.items())))


def save_corpus(corpus, data):
    rl.write_json(Path(corpus) / "CORPUS.json",
                  dict(data, rows=[{k: v for k, v in r.items() if k != "statement"} for r in data["rows"]]))


# ---- attempts ----

def attempt_dir(corpus, recipe, tier, attempt):
    return Path(corpus) / "attempts" / recipe / tier / ("a%d" % attempt)


def store_dir(corpus, recipe, tier):
    return Path(corpus) / "attempts" / recipe / tier


def prepare_attempt(corpus, recipe, tier, attempt):
    d = attempt_dir(corpus, recipe, tier, attempt)
    for sub in ("prompts", "answers", "feedback", "checks"):
        (d / sub).mkdir(parents=True, exist_ok=True)
    link = d / "MANIFEST.json"
    if not link.exists():
        link.symlink_to(Path(os.path.relpath(Path(corpus) / "MANIFEST.json", d)))
    return d


MECHANICAL_PROOF = rl.pkg.CONTROL_TACTIC[len("Proof.\n"):]


def prompt_of(corpus, row, recipe, tier, attempt):
    """The prompt text of an attempt: the recipe's task (attempt 1) or the retry text (attempt 2+)."""
    if tier == "mechanical":
        return MECHANICAL_PROOF
    if attempt > 1:
        path = attempt_dir(corpus, recipe, tier, attempt) / "prompts" / ("%s.md" % row["id"])
        return path.read_text()
    return Path(row["prompts"][recipe]["path"]).read_text()


def start_event(row, recipe, tier, attempt, prompt):
    return store.event(id=row["store_id"], function=FUNCTION, kind="goal", state="running", tier=tier,
                       attempt=attempt, prompt_sha256=sha(prompt), prompt_bytes=len(prompt.encode()),
                       context_items=(row["prompts"].get(recipe, {}).get("context_items")
                                      if attempt == 1 else ["feedback"]), head=None,
                       **{"class": row["class"]})


def register_start(corpus, row, recipe, tier, attempt, prompt):
    """Append the attempt's `running` event; store.Rejected when the (prompt, tier) pair was sent before.
    The store lets a still-running attempt continue under its pair; a wave never re-sends it."""
    run = store_dir(corpus, recipe, tier)
    events = [e for e in store.read_events(run) if e["id"] == row["store_id"]]
    if not events:
        store.append(run, store.event(id=row["store_id"], function=FUNCTION, kind="goal", state="derived",
                                      **{"class": row["class"]}))
    if any(e.get("attempt") is not None and e.get("prompt_sha256") == sha(prompt) and e.get("tier") == tier
           for e in events):
        raise store.Rejected("prompt %s already sent to tier %s for %s" % (sha(prompt)[:16], tier, row["store_id"]))
    store.append(run, start_event(row, recipe, tier, attempt, prompt))


def parse_reply(reply):
    """(data dict or None, raw text) of an agent's final reply."""
    if isinstance(reply, dict):
        return reply, json.dumps(reply, sort_keys=True)
    raw = reply if isinstance(reply, str) else str(reply)
    for candidate in [raw] + re.findall(r"```(?:json)?\s*(\{.*?\})\s*```", raw, re.S) + \
            ([raw[raw.index("{"):raw.rindex("}") + 1]] if "{" in raw and "}" in raw else []):
        try:
            data = json.loads(candidate)
        except (json.JSONDecodeError, ValueError):
            continue
        if isinstance(data, dict):
            return data, raw
    return None, raw


def record_answer(corpus, row, recipe, tier, attempt, reply, extra=None):
    """Write the answer files with package.write_answer; append the failure event of a non-proof verdict.
    Returns the verdict (or `malformed`)."""
    d = attempt_dir(corpus, recipe, tier, attempt)
    extra = extra or {}
    data, raw = parse_reply(reply)
    verdict = None
    if data is not None:
        try:
            verdict, _ = package.write_answer(d, row["id"], data, raw, tier, extra.get("tokens_in"),
                                              extra.get("tokens_out"))
        except package.PackageError as error:
            extra["malformed"] = str(error)
    if verdict is None:
        verdict = "malformed"
        (d / "answers" / ("%s.raw" % row["id"])).write_text(raw)
    prompt = prompt_of(corpus, row, recipe, tier, attempt)
    base = dict(id=row["store_id"], function=FUNCTION, kind="goal", tier=tier, attempt=attempt,
                prompt_sha256=sha(prompt), prompt_bytes=len(prompt.encode()), answer_bytes=len(raw.encode()),
                tokens_in=extra.get("tokens_in"), tokens_out=extra.get("tokens_out"))
    if verdict in ("give_up", "need_context", "malformed"):
        store.append(store_dir(corpus, recipe, tier), store.event(state="failed", **{"class": verdict}, **base))
    wave = d / "WAVE.json"
    rows = rl.read_json(wave, {})
    rows[row["id"]] = dict(extra, verdict=verdict, prompt_bytes=base["prompt_bytes"], answer_bytes=base["answer_bytes"],
                           prompt_sha256=base["prompt_sha256"])
    rl.write_json(wave, rows)
    return verdict


def run_wave(corpus, tier, spawn, recipe="similar", ids=None, sets=("known",), attempt=1, collect=None):
    """One wave: for every eligible goal register the attempt, spawn it, record the answer.
    SPAWN(row, prompt) returns a pending object; COLLECT(list of pending) returns [(reply, extra)] in
    order. With tier `mechanical` no model runs (the answer is CONTROL_TACTIC). Returns a summary."""
    corpus = Path(corpus)
    data = load_corpus(corpus)
    recipe = "none" if tier == "mechanical" else recipe
    prepare_attempt(corpus, recipe, tier, attempt)
    rows = eligible(data, recipe if recipe != "none" else "none", ids, sets)
    if attempt > 1:
        rows = [r for r in rows if (attempt_dir(corpus, recipe, tier, attempt) / "prompts" / ("%s.md" % r["id"])).exists()]
    started, rejected = [], []
    for row in rows:
        prompt = prompt_of(corpus, row, recipe, tier, attempt)
        try:
            register_start(corpus, row, recipe, tier, attempt, prompt)
        except store.Rejected as error:
            rejected.append((row["id"], str(error)))
            continue
        if attempt == 1 and tier != "mechanical":
            (attempt_dir(corpus, recipe, tier, attempt) / "prompts" / ("%s.md" % row["id"])).write_text(prompt)
        started.append((row, prompt))
    if tier == "mechanical":
        results = [(json.dumps(dict(verdict="proved", proof=MECHANICAL_PROOF)), {}) for _ in started]
    else:
        pending = [spawn(row, prompt) for row, prompt in started]
        results = collect(pending)
    verdicts = {}
    for (row, _), (reply, extra) in zip(started, results):
        verdict = record_answer(corpus, row, recipe, tier, attempt, reply, dict(extra))
        verdicts[verdict] = verdicts.get(verdict, 0) + 1
    return dict(tier=tier, recipe=recipe, attempt=attempt, started=len(started), rejected=rejected,
                verdicts=verdicts, dir=str(attempt_dir(corpus, recipe, tier, attempt)))


def prepare_retry(corpus, tier, recipe="similar", ids=None, attempt=2):
    """Write the prompts of attempt ATTEMPT: the previous prompt plus the compiler error text (a FAIL of
    `check`) or the named context items found in the similar-lemma index (need_context). A goal whose
    previous attempt closed, gave up, or named context the index lacks gets no retry. Returns the ids."""
    corpus = Path(corpus)
    data = load_corpus(corpus)
    limit = tier_row(tier)["max_attempts"]
    if attempt > limit:
        raise ReplayError("Tier %s allows %d attempts." % (tier, limit))
    before = attempt_dir(corpus, recipe, tier, attempt - 1)
    d = prepare_attempt(corpus, recipe, tier, attempt)
    checks = rl.read_json(before / "CHECK.json", {})
    index = None
    out = []
    for row in data["rows"]:
        if ids is not None and row["id"] not in ids:
            continue
        meta = rl.read_json(before / "answers" / ("%s.json" % row["id"]))
        old = before / "prompts" / ("%s.md" % row["id"])
        if meta is None or not old.exists():
            continue
        previous = old.read_text()
        if meta["verdict"] == "proved" and checks.get(row["id"], {}).get("result") == "FAIL":
            proof = (before / "answers" / ("%s.v" % row["id"])).read_text()
            errors = (before / "feedback" / ("%s.txt" % row["id"])).read_text()
            text = previous + RETRY_ERROR.format(proof=proof.strip(), errors=errors.strip())
        elif meta["verdict"] == "need_context":
            index = index or similar.build_index()
            found = [e for e in index["entries"] if any(n.split(".")[-1] == e["name"] for n in meta["needs"])]
            if not found:
                continue
            text = previous + "\n## Context you asked for\n\n" + "\n".join(similar.render(e) for e in found)
        else:
            continue
        if len(text.encode()) > tier_row(tier)["max_prompt_bytes"]:
            text = previous + RETRY_ERROR.format(proof=proof.strip(), errors=errors.strip()[:1500]) \
                if meta["verdict"] == "proved" else None
            if text is None or len(text.encode()) > tier_row(tier)["max_prompt_bytes"]:
                continue
        (d / "prompts" / ("%s.md" % row["id"])).write_text(text)
        out.append(row["id"])
    return out


RETRY_ERROR = """
## Your previous attempt failed

Proof sent:

```
{proof}
```

Rocq's errors:

```
{errors}
```

Answer again with a corrected proof in the same JSON form.
"""


# ---- checks ----

def check_one(corpus, data, row, recipe, tier, attempt):
    """(result, class) of one answer, after appending its final store event."""
    corpus = Path(corpus)
    d = attempt_dir(corpus, recipe, tier, attempt)
    meta = rl.read_json(d / "answers" / ("%s.json" % row["id"]))
    prompt = prompt_of(corpus, row, recipe, tier, attempt)
    base = dict(id=row["store_id"], function=FUNCTION, kind="goal", tier=tier, attempt=attempt,
                prompt_sha256=sha(prompt), prompt_bytes=len(prompt.encode()), answer_bytes=meta.get("answer_bytes"),
                tokens_in=meta.get("tokens_in"), tokens_out=meta.get("tokens_out"))
    if meta["verdict"] == "proved":
        answer = (d / "answers" / ("%s.v" % row["id"])).read_text()
        result = check_proof(corpus, row, d, answer, "%s-%s-%d-%s" % (recipe, tier, attempt, row["id"]))
        if result == "PASS":
            supplied = row["prompts"].get(recipe, {}).get("similar", []) if attempt == 1 else []
            used = [name for name in supplied if name in answer]
            path = d / "checks" / row["id"] / "proof.v"
            event = store.event(state="closed", context_items=supplied or None, context_used=used if supplied else None,
                                artifact=dict(path=str(path), sha256=store.sha256_file(path)), **base)
        else:
            event = store.event(state="failed", **{"class": "compile_error"}, **base)
    elif meta["verdict"] == "false":
        if row["set"] == "known":
            result, event = "WRONG", store.event(state="failed", **{"class": "wrong_false"}, **base)
        else:
            hit = check_counterexample(corpus, row, d, meta.get("counterexample") or "", data)
            result = "FALSE" if hit else "BAD"
            event = (store.event(state="false", **{"class": row["class"]}, **base) if hit else
                     store.event(state="failed", **{"class": "bad_counterexample"}, **base))
    else:
        return None
    store.append(store_dir(corpus, recipe, tier), event)
    return result


def check_proof(corpus, row, d, answer, tag):
    """PASS or FAIL of ANSWER with residual_loop.py's stand-alone route (check.sh, one guard scope)."""
    goal_dir = Path(corpus) / "goals" / row["id"]
    c = d / "checks" / row["id"]
    c.mkdir(parents=True, exist_ok=True)
    feedback = d / "feedback" / ("%s.txt" % row["id"])
    problem = rl.answer_problems(answer)
    if problem:
        feedback.write_text("FAIL: %s\n" % problem)
        return "FAIL"
    shutil.copyfile(goal_dir / "goal.v", c / "goal.v")
    (c / "proof.v").write_text(rl.goal_head((goal_dir / "goal.v").read_text()) + answer.strip() + "\n")
    manifest = rl.read_json(Path(corpus) / "MANIFEST.json")
    args, lib = rl.bank_args(manifest["bank"])
    ocamlpath = (rl.read_json(Path(corpus) / "CORPUS.json") or {}).get("ocamlpath") or lib
    (c / "check.sh").write_text(rl.check_script(tag, args, ocamlpath))
    (c / "check.sh").chmod(0o755)
    verdict, _ = rl.run_check(c)
    log = (c / "check.log").read_text(errors="replace") if (c / "check.log").exists() else ""
    feedback.write_text("PASS\n" if verdict == "PASS" else "FAIL\n" + rl.errors_of(log) + "\n")
    return verdict


VALUE = re.compile(r"([A-Za-z_][\w']*)\s*(?::=|=|:)\s*(true|false|-?0x[0-9a-fA-F]+|-?\d+)")


def counterexample_values(text, binders):
    """{binder: value} named in a free-text counterexample (`x = 5, b = true, w = 0xff`); others default."""
    import falsify
    named = {}
    for name, value in VALUE.findall(text):
        named[name] = value
    out = {}
    for b in binders:
        if b["kind"] == "prop":
            continue
        raw = named.get(b["name"])
        if raw is None or b["kind"] == "bytes":
            out[b["name"]] = falsify.default_value(b)
        elif b["kind"] == "bool":
            out[b["name"]] = raw == "true"
        else:
            value = int(raw, 0)
            if b["kind"] == "bv":
                value %= 2 ** b["width"]
            out[b["name"]] = value
    return out


def check_counterexample(corpus, row, d, text, data):
    """True when the kernel accepts `~ statement` on the answer's binder values (falsify.py's refutation)."""
    import falsify
    route = falsify.Route(data["bank"], data["ocamlpath"])
    goal = Path(corpus) / "goals" / row["id"] / "goal.v"
    out = d / "checks" / row["id"]
    out.mkdir(parents=True, exist_ok=True)
    goal_preamble, statement, _ = falsify.read_goal(goal)
    pre = falsify.preamble(goal_preamble, statement, route.args, route.coqlib)
    (out / "probe.v").write_text(falsify.probe_text(pre, statement))
    result, text_log = route.compile(out / "probe.v", "replay-probe-" + row["id"])
    binders, ended = falsify.parse_binders(falsify.records(text_log))
    if result["returncode"] != 0 or not ended or any(b["kind"] not in falsify.CHECKED_KINDS for b in binders):
        return False
    try:
        values = counterexample_values(text, binders)
    except ValueError:
        return False
    (out / "refute.v").write_text(falsify.refute_text(pre, statement, binders, values))
    result, _ = route.compile(out / "refute.v", "replay-refute-" + row["id"])
    return result["returncode"] == 0


def cmd_check(a):
    corpus = Path(a.corpus)
    data = load_corpus(corpus)
    recipe = "none" if a.tier == "mechanical" else a.recipe
    d = attempt_dir(corpus, recipe, a.tier, a.attempt)
    checks = rl.read_json(d / "CHECK.json", {})
    rows = [r for r in data["rows"] if (d / "answers" / ("%s.json" % r["id"])).exists() and r["id"] not in checks]

    def one(row):
        return row["id"], check_one(corpus, data, row, recipe, a.tier, a.attempt)

    with ThreadPoolExecutor(max_workers=jobs_for(CHECK_PEAK_GIB, a.jobs)) as pool:
        for gid, result in pool.map(one, rows):
            if result is not None:
                checks[gid] = dict(result=result)
    rl.write_json(d / "CHECK.json", checks)
    counts = {}
    for gid, value in checks.items():
        counts[value["result"]] = counts.get(value["result"], 0) + 1
    print("CHECK %s %s a%d %s" % (recipe, a.tier, a.attempt, " ".join("%s=%d" % kv for kv in sorted(counts.items()))))


def cmd_wave(a):
    if a.tier != "mechanical":
        raise ReplayError("Model tiers run from the coordinator's kernel (dispatch_kernel.py).")
    print(json.dumps(run_wave(a.corpus, "mechanical", None, sets=tuple(a.set)), sort_keys=True))


def cmd_original(a):
    """Check the withheld original proofs of IDS (expected PASS) and a corrupted one (expected FAIL)."""
    corpus = Path(a.corpus)
    data = load_corpus(corpus)
    origins = rl.read_json(corpus / "ORIGINS.json")
    by_id = {r["id"]: r for r in data["rows"]}
    d = prepare_attempt(corpus, "original", "original", 1)
    cases = [(gid, origins[gid]["proof"], "PASS") for gid in a.ids]
    if a.corrupt:
        proof = origins[a.corrupt]["proof"]
        lines = proof.split("\n")
        broken = "\n".join(lines[:-2] + ["exact I.", lines[-1]])
        cases.append((a.corrupt, broken, "FAIL"))
    ok = True
    for n, (gid, proof, expected) in enumerate(cases):
        got = check_proof(corpus, by_id[gid], d, proof, "original-%d-%s" % (n, gid))
        ok &= got == expected
        print("ORIGINAL %s expected=%s got=%s" % (gid, expected, got))
    sys.exit(0 if ok else 1)


# ---- results and routing ----

def attempt_results(corpus, data, tiers):
    """{(recipe, tier): {id: {attempt: (result, tokens, bytes)}}} from the store logs."""
    out = {}
    names = [t["name"] for t in tiers]
    base = Path(corpus) / "attempts"
    for recipe_dir in sorted(p for p in base.iterdir() if p.is_dir()) if base.is_dir() else []:
        for tier_dir in sorted(p for p in recipe_dir.iterdir() if p.is_dir()):
            if tier_dir.name not in names:
                continue
            state = {}
            for event in store.read_events(tier_dir):
                if event.get("attempt") is None:
                    continue
                slot = state.setdefault(event["id"], {}).setdefault(event["attempt"], dict(result="running"))
                slot["prompt_bytes"] = event.get("prompt_bytes")
                if event["state"] != "running":
                    slot["result"] = "closed" if event["state"] == "closed" else (
                        "false" if event["state"] == "false" else event["class"])
                    slot["answer_bytes"] = event.get("answer_bytes")
                    tokens = [event.get("tokens_in"), event.get("tokens_out")]
                    slot["tokens"] = None if tokens == [None, None] else sum(t or 0 for t in tokens)
            out[(recipe_dir.name, tier_dir.name)] = state
    return out


def shares(rows, state, max_attempts):
    n = len(rows)
    first = sum(1 for r in rows if state.get(r["store_id"], {}).get(1, {}).get("result") == "closed")
    within = sum(1 for r in rows if any(state.get(r["store_id"], {}).get(k, {}).get("result") == "closed"
                                        for k in range(1, max_attempts + 1)))
    spent = [s for r in rows for k, s in state.get(r["store_id"], {}).items() if k <= max_attempts]
    tokens = [s.get("tokens") for s in spent]
    sent = [s for s in spent if s.get("result") != "running"]
    return dict(goals=n, attempted=sum(1 for r in rows if r["store_id"] in state), first=first, within=within,
                first_share=round(first / n, 3) if n else None, within_share=round(within / n, 3) if n else None,
                tokens=None if not tokens or any(t is None for t in tokens) else sum(tokens),
                bytes=sum((s.get("prompt_bytes") or 0) + (s.get("answer_bytes") or 0) for s in sent))


RULE = ("first_tier: the cheapest model tier (tiers.json order) that closes at least min_share of the class's "
        "known-true replay goals within its attempts, on the recipe that closes most at that tier (ties: the "
        "smaller prompt); none reaches it: the tier with the highest share (ties: cheaper). A class with fewer "
        "than %d goals keeps the default haiku-low. Why min_share 0.5: at that share a cheap tier closes at "
        "least as many goals as it hands on, so its wasted attempts are bounded by its own cost on the goals it "
        "closes, and each wasted attempt costs less than one attempt at the next tier." % MIN_GOALS)


def routing(corpus, tiers, min_share=MIN_SHARE):
    corpus = Path(corpus)
    data = load_corpus(corpus)
    results = attempt_results(corpus, data, tiers)
    known = [r for r in data["rows"] if r["set"] == "known"]
    model_tiers = [t for t in tiers if t["agent"]]
    recipes = sorted({recipe for recipe, _ in results if recipe not in ("none", "original")})
    per_tier = {}
    for t in tiers:
        for recipe in (["none"] if not t["agent"] else recipes):
            if (recipe, t["name"]) in results:
                row = shares(known, results[(recipe, t["name"])], t["max_attempts"])
                closed = row["within"]
                row["tokens_per_closed"] = round(row["tokens"] / closed) if closed and row["tokens"] is not None else None
                row["bytes_per_closed"] = round(row["bytes"] / closed) if closed else None
                per_tier["%s/%s" % (t["name"], recipe)] = row
    classes = {}
    for cls in sorted({r["class"] for r in known}) + ["PURE"]:
        rows = [r for r in known if r["class"] == cls or (cls == "PURE" and r["class"].startswith("PURE-"))]
        if not rows:
            continue
        entry = dict(goals=len(rows), attempts={t["name"]: t["max_attempts"] for t in tiers}, shares={})
        best = None
        for t in model_tiers:
            options = []
            for recipe in recipes:
                if (recipe, t["name"]) in results:
                    row = shares(rows, results[(recipe, t["name"])], t["max_attempts"])
                    entry["shares"]["%s/%s" % (t["name"], recipe)] = row
                    if row["attempted"]:
                        options.append((row["within"], -row["bytes"], recipe, row))
            if options:
                within, _, recipe, row = max(options)
                if best is None or row["within_share"] > best[2]["within_share"]:
                    best = (t["name"], recipe, row)
                if row["within_share"] >= min_share and "first_tier" not in entry:
                    entry.update(first_tier=t["name"], context=recipe)
        if "first_tier" not in entry:
            entry.update(first_tier=best[0] if best else "haiku-low", context=best[1] if best else "similar")
        if len(rows) < MIN_GOALS:
            entry.update(first_tier="haiku-low", small_class=True)
        mechanical = results.get(("none", "mechanical"))
        if mechanical is not None:
            entry["shares"]["mechanical"] = shares(rows, mechanical, 1)
        classes[cls] = entry
    union = set()
    for (recipe, tier), state in results.items():
        if tier in HAIKU:
            limit = tier_row(tier, tiers)["max_attempts"]
            union |= {r["id"] for r in known if any(state.get(r["store_id"], {}).get(k, {}).get("result") == "closed"
                                                    for k in range(1, limit + 1))}
    ran = [tier for tier in HAIKU if any(t == tier for (_, t) in results)]
    haiku = dict(tiers_run=ran, closed=len(union), of=len(known),
                 share=round(len(union) / len(known), 3) if known else None)
    haiku["sonnet_needed"] = (haiku["share"] is not None and haiku["share"] < 0.5) if len(ran) == len(HAIKU) else None
    unknown = [r for r in data["rows"] if r["set"] == "unknown"]
    verdicts = {}
    for (recipe, tier), state in results.items():
        for r in unknown:
            for k, slot in state.get(r["store_id"], {}).items():
                key = "%s/%s" % (tier, recipe)
                verdicts.setdefault(key, {})
                verdicts[key][slot["result"]] = verdicts[key].get(slot["result"], 0) + 1
    return dict(schema="oblig-routing/1", rule=RULE, min_share=min_share, min_goals=MIN_GOALS, head=data["head"],
                corpus=str(corpus), classes=classes, tiers=per_tier, haiku_union=haiku, unknown_set=verdicts)


def cmd_routing(a):
    data = routing(a.corpus, load_tiers(), a.min_share)
    if a.out:
        Path(a.out).write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    for cls, entry in sorted(data["classes"].items()):
        print("CLASS %s goals=%d first_tier=%s context=%s" % (cls, entry["goals"], entry["first_tier"], entry["context"]))
    for key, row in sorted(data["tiers"].items()):
        print("TIER %s first=%s within=%s tokens/closed=%s bytes/closed=%s" % (
            key, row["first_share"], row["within_share"], row["tokens_per_closed"], row["bytes_per_closed"]))
    h = data["haiku_union"]
    print("HAIKU closed=%d of=%d share=%s sonnet_needed=%s" % (h["closed"], h["of"], h["share"], h["sonnet_needed"]))


def cmd_status(a):
    data = load_corpus(a.corpus)
    print_corpus(data)
    for (recipe, tier), state in sorted(attempt_results(a.corpus, data, load_tiers() + [dict(
            name="original", agent=None, max_attempts=1)]).items()):
        counts = {}
        for slots in state.values():
            for k, slot in slots.items():
                key = "a%d:%s" % (k, slot["result"])
                counts[key] = counts.get(key, 0) + 1
        print("ATTEMPTS %s %s %s" % (recipe, tier, " ".join("%s=%d" % kv for kv in sorted(counts.items()))))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    c = sub.add_parser("corpus")
    c.add_argument("--out", required=True)
    c.add_argument("--bank", required=True)
    c.add_argument("--ocamlpath")
    c.add_argument("--leftovers", nargs="*")
    c.add_argument("--jobs", type=int)
    c.add_argument("--resume", action="store_true", help="reuse the finished round trips of an earlier run in --out")
    f = sub.add_parser("falsify")
    f.add_argument("--corpus", required=True)
    f.add_argument("--set", nargs="*", default=["unknown"])
    f.add_argument("--jobs", type=int)
    w = sub.add_parser("wave")
    w.add_argument("--corpus", required=True)
    w.add_argument("--tier", required=True)
    w.add_argument("--set", nargs="*", default=["known"])
    k = sub.add_parser("check")
    k.add_argument("--corpus", required=True)
    k.add_argument("--tier", required=True)
    k.add_argument("--recipe", default="similar")
    k.add_argument("--attempt", type=int, default=1)
    k.add_argument("--jobs", type=int)
    o = sub.add_parser("original")
    o.add_argument("--corpus", required=True)
    o.add_argument("--ids", nargs="+", required=True)
    o.add_argument("--corrupt")
    s = sub.add_parser("status")
    s.add_argument("--corpus", required=True)
    r = sub.add_parser("routing")
    r.add_argument("--corpus", required=True)
    r.add_argument("--out", default=str(ROUTING_FILE))
    r.add_argument("--min-share", type=float, default=MIN_SHARE)
    a = ap.parse_args(argv)
    try:
        dict(corpus=cmd_corpus, falsify=cmd_falsify, wave=cmd_wave, check=cmd_check, original=cmd_original,
             status=cmd_status, routing=cmd_routing)[a.command](a)
    except (ReplayError, package.PackageError) as error:
        sys.exit("replay: %s" % error)


if __name__ == "__main__":
    main()
