#!/usr/bin/env python3
"""Goal packaging for the obligation loop (model-free).

    package.py goals     --run RUN --function F [--goal ID ...] [--tier T] [--max-prompt-bytes N]
                         [--index INDEX.json] [--hints DIR] [--falsify --bank BANK [--ocamlpath DIR]
                         [--exec-dir RUN/exec]] [--defs --bank BANK]
    package.py answer    --run RUN --goal ID --answer ANSWER.json [--tier T]
                         [--tokens-in N] [--tokens-out N]
    package.py addresses FILE ...
    package.py diagnose  --log LOG --run RUN --function F --block OFF [--disasm FILE]
                         [--successors FILE ...] [--hints DIR] [--pcs PC ...] [--max-prompt-bytes N]
    package.py diagnosis-answer --task DIR --answer ANSWER.json [--tier T]

RUN is a run dir of tools/block/residual_loop.py (MANIFEST.json, goals/<id>/goal.v);
residual_loop.py stays the engine that exports, checks, minimises and registers.

goals packages each open goal (reparse exact, not PASS, not normalised into parts by
tools/oblig/normalise.py: those parts are open goals of their own) into RUN/package/<id>/:
- the address check: the patterns of tools/oblig/check_relocatable.py (an address of the linked
  image as a whole-token hex or decimal literal) over the text of goal.v and over the decimal value of
  each integer literal of its statement. Before it, each `(N)%Z` or `Zpos` literal that is the
  address of a symbol of tools/oblig/symbols.json (or at most 4 KiB above one), and both bounds of
  a code-disjointness disjunction `x + n <= A \\/ B <= x` that are ELF section bounds, are written
  as their parsing-only notations of ZesuSsz/Generated/Stock/Symbols.v (tools/oblig/symbolize.py);
  the kernel checks `(original) = (rewritten)` by reflexivity with the goal's imports and the bank
  of MANIFEST.json, and only then goal.v is replaced (the original kept as goal-literal.v,
  the Symbols import added) and the task shows the notations. A match that remains gives class
  ADDRESS: the goal goes to the decision queue and gets no prover task. A goal whose section
  bounds were rewritten is a pure range goal (`range_bounds` in PACKAGE.json): its task gets the
  range hint (RANGE_HINT: RAM lies above every code address).
- a goal with a `zesu_hist` premise gets the history hint (HIST_HINT): facts about call results
  may sit inside the sealed history, with the tactic lines that expose them.
- with --falsify, tools/oblig/falsify.py on goal.v; a `false` verdict gets no prover task.
- the prover task TASK-<tier>.md: the TASK text of residual_loop.py (the default-printer goal
  and the path of the exact source), the answer form, then context items while the task
  stays within --max-prompt-bytes: with --defs, the definitions of the goal's project names
  (tools/oblig/defs.py, Rocq About/Print with the goal's imports), the 3 nearest closed lemmas
  (tools/oblig/similar.py) and the hint slice of the block (`tools/oblig/hints.py slice`, when
  --hints names a hint pack).
- PACKAGE.json: obligation id (`<F>/goal/<block>-<16 hex of sha256(statement)>`), class,
  addresses, falsity verdict, task path, prompt bytes and sha256, context items, and `dropped_facts`:
  the facts the export left out of the statement for size (MANIFEST row of residual_loop.py, from the
  `@@X dropped-fact` records of ResidualExport.v); the task names them in one line
  ("premises omitted for size: ...").

answer turns a prover's JSON answer
`{"verdict": "proved"|"false"|"need_context"|"give_up", "proof": ..., "needs": [...],
"counterexample": ...}` into RUN/answers/<id>.json, and for `proved` into RUN/answers/<id>.v
(the proof script), the files `residual_loop.py collect` checks.

diagnose turns each `@@S` record of a compile log (ZesuSsz/Automation2/SpatialExport.v) into a
diagnosis task RUN/diagnose/<block>-<n>/TASK.md with REQUEST.json. Its answer is typed, not a
proof: `annotation`, `pure_goal`, `false` or `rule_gap`; diagnosis-answer checks the form and
writes ANSWER.json (and pure_goal.txt for a pure goal). The check of the content is a rerun of
the block.
"""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
sys.path.insert(0, str(ROOT / "tools/bench"))
import check_relocatable  # noqa: E402
import residual_loop as rl  # noqa: E402
import similar  # noqa: E402
import symbolize  # noqa: E402
import bench_report  # noqa: E402

MAX_PROMPT_BYTES = 12000
ADDRESS_PATTERNS = check_relocatable.PATTERNS
VERDICTS = ("proved", "false", "need_context", "give_up")
DIAGNOSIS_KINDS = ("annotation", "pure_goal", "false", "rule_gap")
HINTS = HERE / "hints.py"

ANSWER_FORM = """## Answer form

Reply with one JSON object and nothing else:

```json
{{"verdict": "proved" | "false" | "need_context" | "give_up",
 "proof": "the text after `Proof.`, ending with one `Qed.` (verdict proved)",
 "needs": ["a lemma, definition or fact you miss (verdict need_context)"],
 "counterexample": "values of the binders that make the premises true and the conclusion false (verdict false)"}}
```

The coordinator writes `proof` to `{answer}` and checks it with Rocq.
"""

RANGE_HINT = """## Range hint

The bounds of `x + n <= A \\/ B <= x` in this goal are the start and end of an ELF section of the
code image (`sec_text_start`, `sec_text_end`, `sec_rodata_start`, `sec_rodata_end` of
`ZesuSsz.Generated.Stock.Symbols`: parsing-only `Z` literals, so `lia` reads them as numbers).
RAM is `[mapRamBase stockZiskMap, machineRamEnd stockZiskMap)` (`ZesuSsz.Contracts.Machine`; both
reduce by `reflexivity` or `cbn`), above every code and read-only data address. A pointer that a
premise places in RAM satisfies the right disjunct `B <= x`: find that premise (a domain range fact,
often guarded by `0 < length`), state the RAM base as a number with
`assert (mapRamBase stockZiskMap = ...) by reflexivity` when it occurs, and finish with `lia`.
"""

HIST_HINT = """## History hint

Facts about call results (for example `call_xN <> 0`) may be inside the `zesu_hist` premise {hyp}.
Unfold it with `zesu_hist_eq` and destruct:

```
unfold {definition} in {hyp}; rewrite zesu_hist_eq in {hyp};
repeat (hnf in {hyp}; match type of {hyp} with ex _ => destruct {hyp} as [? {hyp}] | _ /\\ _ => destruct {hyp} as [_ {hyp}] end).
```

The `repeat` keeps the last conjunct; to keep another, destruct the conjunction by hand.
"""
HIST_PREMISE = re.compile(r"\((H[\w']*) : \(@[\w.]*\bzesu_hist \(@?([\w.']+)")


def hist_hints(statement):
    """The history hint for each `zesu_hist` premise binder of STATEMENT (exporter form)."""
    return [HIST_HINT.format(hyp=hyp, definition=definition.rsplit(".", 1)[-1])
            for hyp, definition in dict.fromkeys(HIST_PREMISE.findall(statement))]


class PackageError(ValueError):
    pass


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def obligation_id(function, block, statement):
    """The goal id of tools/oblig/store.py: the sha256 of the exact exported statement."""
    return "%s/goal/%s-%s" % (function, block, sha(statement)[:16])


# ---- addresses ----

def address_matches(text):
    """Code addresses named in TEXT: pattern hits in the text and in the decimal values of its
    integer literals (positive constructor terms included)."""
    import falsify  # lazy: falsify imports the residual loop's compile route
    found = []
    for pattern in ADDRESS_PATTERNS:
        found += [dict(match=m.group(0), source="text") for m in pattern.finditer(text)]
    for value in sorted(falsify.literals(text)):
        decimal = str(abs(value))
        if any(pattern.fullmatch(decimal) for pattern in ADDRESS_PATTERNS[1:]):
            found.append(dict(match=decimal, source="literal", hex="%#x" % abs(value)))
    unique, seen = [], set()
    for row in found:
        if (row["match"], row["source"]) not in seen:
            seen.add((row["match"], row["source"]))
            unique.append(row)
    return unique


# ---- strict premise slice ----

def statement_parts(statement):
    """(binder text, premises, conclusion) of `forall BINDERS, P1 -> .. -> C` (top-level split; no
    binders: empty binder text). None when the statement has another shape."""
    text = bench_report.unwrap(statement)
    binders = ""
    if text.startswith("forall "):
        pieces = bench_report.top_level(text, ",")
        if len(pieces) < 2:
            return None
        binders, text = pieces[0][len("forall "):].strip(), ",".join(pieces[1:]).strip()
    pieces = [p.strip() for p in bench_report.top_level(text, "->")]
    return binders, pieces[:-1], pieces[-1]


def variables_of(text, names):
    return {n for n in names if re.search(r"(?<![\w'.])%s(?![\w'])" % re.escape(n), text)}


def binder_groups(binders):
    """[(text, names, type)] of `(a b : T) (c : U)`; one group (names, no type) for a bare `a b`."""
    groups, i = [], 0
    while i < len(binders):
        if binders[i] == "(":
            j = similar.matching(binders, i)
            if j is None:
                break
            inner = binders[i + 1:j]
            names, _, typ = inner.partition(":")
            groups.append((binders[i:j + 1], names.split(), typ.strip()))
            i = j + 1
        elif binders[i].isspace():
            i += 1
        else:
            return [(binders, binders.split(":")[0].split(), "")]
    return groups


NAMED_PREMISE = re.compile(r"^H[\w']*$")


def strict_slice(statement):
    """(statement, dropped premises): the premises that share a bound data variable with the conclusion,
    directly or through kept premises, minus a premise that repeats another or is a top-level conjunct
    of another kept premise. Premises are the arrows `P ->` and the named binders `(H.. : P)` that
    nothing else names (the exporter's form). The statement is returned unchanged when nothing drops."""
    parts = statement_parts(statement)
    if parts is None:
        return statement, []
    binders, arrows, conclusion = parts
    groups = binder_groups(binders) if binders else []
    everything = [g[0] for g in groups] + arrows + [conclusion]
    # (kind, text, proposition): kind `binder` with its group index, or `arrow`.
    premises, data = [], set()
    for n, (text, names, typ) in enumerate(groups):
        others = " ".join(t for t in everything if t is not text)
        if typ and names and all(NAMED_PREMISE.match(x) for x in names) and not variables_of(others, names):
            premises.append((("binder", n), text, typ))
        else:
            data |= set(names)
    premises += [(("arrow", n), text, text) for n, text in enumerate(arrows)]
    live = variables_of(conclusion, data)
    kept = set()
    changed = True
    while changed:
        changed = False
        for i, (_, _, prop) in enumerate(premises):
            found = variables_of(prop, data)
            if i not in kept and found & live:
                kept.add(i)
                live |= found
                changed = True
    norm = [" ".join(bench_report.unwrap(p).split()) for _, _, p in premises]
    for i in sorted(kept):
        conjuncts = [{" ".join(bench_report.unwrap(c).split()) for c in
                      bench_report.top_level(bench_report.unwrap(premises[j][2]).replace("∧", "/\\"), "/\\")}
                     for j in kept if j != i]
        if any(norm[j] == norm[i] and j < i for j in kept) or any(norm[i] in cs and len(cs) > 1 for cs in conjuncts):
            kept.discard(i)
    dropped = [text for i, (_, text, _) in enumerate(premises) if i not in kept]
    if not dropped:
        return statement, []
    gone = {key for i, (key, _, _) in enumerate(premises) if i not in kept}
    head = " ".join(text for n, (text, _, _) in enumerate(groups) if ("binder", n) not in gone)
    body = " ->\n  ".join([text for n, text in enumerate(arrows) if ("arrow", n) not in gone] + [conclusion])
    return ("forall %s,\n  %s" % (head, body) if head else body), dropped


def premise_count(statement):
    """Arrow premises plus named premise binders `(H.. : P)` of a statement (strict_slice's premises)."""
    parts = statement_parts(statement)
    if parts is None:
        return 0
    binders, arrows, _ = parts
    named = [g for g in (binder_groups(binders) if binders else [])
             if g[2] and g[1] and all(NAMED_PREMISE.match(x) for x in g[1])]
    return len(arrows) + len(named)


# ---- prover tasks ----

def goal_header(goal_v):
    """The import lines of a goal.v (everything before its Lemma)."""
    head = rl.goal_head(goal_v)
    return head[:head.index("\nLemma ")].strip("\n").split("\n")


def base_task(run, block, goal, goal_v, answer_path):
    counts = goal.get("counts", {})
    text = rl.TASK.format(id=goal["id"], block=block, answer=answer_path,
                          feedback=Path(run) / "feedback" / (goal["id"] + ".txt"), name=goal["name"],
                          premises=counts.get("kept", "?"), props=counts.get("props", "?"),
                          small=counts.get("small", "?"), readable=goal.get("readable") or "(not available)",
                          goal=Path(run) / "goals" / goal["id"] / "goal.v", header="\n".join(goal_header(goal_v)))
    return text + "\n" + ANSWER_FORM.format(answer=answer_path)


def hint_slice(hints, pcs, max_bytes):
    """The hint slice for PCS from tools/oblig/hints.py, or None (no pack, no tool, too large)."""
    if not hints or not pcs or not HINTS.exists() or max_bytes <= 0:
        return None
    command = [sys.executable, str(HINTS), "slice", "--hints", str(hints), "--max-bytes", str(max_bytes)]
    for pc in pcs:
        command += ["--pcs", pc]
    proc = subprocess.run(command, capture_output=True, text=True)
    return proc.stdout if proc.returncode == 0 and proc.stdout.strip() else None


def compose(base, items, max_bytes):
    """BASE plus each (name, text) item that still fits in MAX_BYTES; returns (text, used names)."""
    text, used = base, []
    for name, item in items:
        if item and len((text + "\n" + item).encode()) <= max_bytes:
            text += "\n" + item
            used.append(name)
    return text, used


def symbolize_goal(d, goal_v, route, out, tag):
    """(new goal.v text, [(literal, notation)]) when the statement names a symbol's address and the
    kernel accepts `(original) = (rewritten)` by reflexivity; else (None, reason or [])."""
    symbols, bounds = symbolize.table(), symbolize.sections()
    match = re.search(r"^Lemma (\S+) :\n  (.*)\.\nProof\.\n", goal_v, re.S | re.M)
    if not (symbols or bounds) or not match:
        return None, []
    original = match[2]
    rewritten, found = symbolize.statement(original, symbols, bounds)
    if not found:
        return None, []
    header = symbolize.with_require(goal_header(goal_v))
    check = Path(out) / "symbols" / "same.v"
    check.parent.mkdir(parents=True, exist_ok=True)
    check.write_text("%s\n\nLemma zesu_symbolized_same :\n  (%s) =\n  (%s).\nProof. reflexivity. Qed.\n"
                     % ("\n".join(header), original, rewritten))
    result, log = route.compile(check, tag)
    if result["returncode"] != 0:
        return None, "the kernel refused (original) = (rewritten): " + rl.errors_of(log, limit=6)
    if (d / "goal.v").read_text() == goal_v and not (d / "goal-literal.v").exists():
        (d / "goal-literal.v").write_text(goal_v)
    return rl.goal_text(header, match[1], rewritten), found


def package_goal(run, manifest, goal, function, tier, max_bytes, index, hints, falsify_route=None,
                 exec_dir=None, defs_route=None, symbol_route=None):
    run = Path(run)
    block = manifest["block"]
    d = run / "goals" / goal["id"]
    goal_v = (d / "goal.v").read_text()
    out = run / "package" / goal["id"]
    out.mkdir(parents=True, exist_ok=True)
    record = dict(id=obligation_id(function, block, goal["statement"]), goal=goal["id"], block=block,
                  function=function, tier=tier, conclusion_head=similar.keys(goal["statement"])[0])
    record["dropped_facts"] = goal.get("dropped_facts") or []
    record["addresses"] = address_matches(goal_v)
    if record["addresses"] and symbol_route is not None:
        route = symbol_route() if callable(symbol_route) else symbol_route
        rewritten, found = symbolize_goal(d, goal_v, route, out, "symbols-" + goal["id"])
        if rewritten is not None:
            goal_v = rewritten
            (d / "goal.v").write_text(goal_v)
            record["symbols"] = [dict(literal=literal, notation=name) for literal, name in found]
            record["addresses"] = address_matches(goal_v)
        elif found:
            record["symbols_refused"] = found
    record["class"] = "ADDRESS" if record["addresses"] else None
    if record["class"] == "ADDRESS":
        record["next"] = "decision"
        return write_record(out, record)
    record["range_bounds"] = sorted(set(re.findall(r"\bsec_\w+", goal_v)))
    if falsify_route is not None:
        import falsify
        report = falsify.check(d / "goal.v", falsify_route, out / "falsify", exec_dir=exec_dir, offset=block)
        record["falsify"] = dict(verdict=report["verdict"], reason=report.get("reason"),
                                 hit=report.get("hit"), report=str(out / "falsify" / "FALSIFY.json"))
        if report["verdict"] == "false":
            record["next"] = "owner"
            return write_record(out, record)
    answer_path = run / "answers" / (goal["id"] + ".v")
    base = base_task(run, block, goal, goal_v, answer_path) + dropped_line(record["dropped_facts"])
    if symbolize.REQUIRE in goal_v:
        base = symbolize.display(base, symbolize.table(), symbolize.sections())
    if len(base.encode()) > max_bytes:
        record.update(next="too-large", prompt_bytes=len(base.encode()))
        return write_record(out, record)
    remaining = max_bytes - len(base.encode())
    items = [("range", RANGE_HINT)] if record["range_bounds"] else []
    items += [("hist", text) for text in hist_hints(goal_v)]
    shown = []
    if defs_route is not None:
        import defs
        resolver = defs.Resolver(out / "defs", goal_header(goal_v), defs.route_compile(defs_route),
                                 defs.project_roots(defs_route.args), tag="defs-" + goal["id"])
        names = defs.ranked_names(goal["statement"])
        hinted = sum(len(item.encode()) + 1 for _, item in items)
        section, shown = defs.section(defs.items(resolver.resolve(names), names), remaining - hinted - 200)
        items.append(("defs", section))
    taken = sum(len(item.encode()) + 1 for _, item in items if item)
    found = similar.nearest(index, goal["statement"], similar.K, max(0, remaining - taken - 200)) if index else []
    items += [("similar", similar.section(found))] if found else []
    pcs = ["+0x" + block]
    items.append(("hints", hint_slice(hints, pcs, remaining)))
    text, used = compose(base, items, max_bytes)
    task = out / ("TASK-%s.md" % tier)
    task.write_text(text)
    record.update(next="prover", task=str(task), prompt_bytes=len(text.encode()), prompt_sha256=sha(text),
                  context_items=[name for name, item in items if item],
                  context_supplied=used, similar=[e["name"] for _, e in found] if "similar" in used else [],
                  defs=shown if "defs" in used else [])
    return write_record(out, record)


def dropped_line(facts):
    """The task line naming the premises the export left out for size (ResidualExport.v `dropped-fact`
    records): the statement may be unprovable without them, and a `need_context` answer can name them."""
    if not facts:
        return ""
    return "\npremises omitted for size: %s\n" % ", ".join(
        "%s (%s nodes, head %s)" % (f["name"], f["nodes"] if f.get("nodes") is not None else "?", f["head"])
        for f in facts)


def write_record(out, record):
    rl.write_json(Path(out) / "PACKAGE.json", record)
    return record


def open_goals(run, manifest, only=()):
    for goal in manifest["goals"]:
        if only and goal["id"] not in only:
            continue
        if goal.get("parts"):
            continue  # normalised into parts (tools/oblig/normalise.py): its parts are packaged instead
        status = rl.read_json(Path(run) / "goals" / goal["id"] / "STATUS.json", {})
        if goal.get("reparse") == "exact" and status.get("result") != "PASS":
            yield goal


def cmd_goals(a):
    run = Path(a.run)
    manifest = rl.read_json(run / "MANIFEST.json")
    if manifest is None:
        raise PackageError("No MANIFEST.json in %s." % run)
    index = json.loads(Path(a.index).read_text()) if a.index else similar.build_index(runs=similar.sibling_runs(run))
    route = bank_route = None
    if a.falsify or a.defs:
        import falsify
        if not a.bank:
            raise PackageError("--falsify and --defs need --bank.")
        bank_route = falsify.Route(a.bank, a.ocamlpath)
        route = bank_route if a.falsify else None
    cache = {}

    def symbol_route():
        """The bank's compile route for the kernel check of symbolized literals (made on first use)."""
        if "route" not in cache:
            import falsify
            cache["route"] = bank_route or falsify.Route(a.bank or manifest["bank"], a.ocamlpath)
        return cache["route"]
    for goal in open_goals(run, manifest, set(a.goal or ())):
        record = package_goal(run, manifest, goal, a.function, a.tier, a.max_prompt_bytes, index, a.hints,
                              route, a.exec_dir, bank_route if a.defs else None, symbol_route)
        print("PACKAGE %s %s next=%s class=%s bytes=%s context=%s" % (
            record["goal"], record["id"], record["next"], record["class"] or "-",
            record.get("prompt_bytes", "-"), ",".join(record.get("context_supplied", [])) or "-"))


# ---- prover answers ----

def parse_answer(data):
    if not isinstance(data, dict) or data.get("verdict") not in VERDICTS:
        raise PackageError("The answer needs a verdict among %s." % ", ".join(VERDICTS))
    verdict = data["verdict"]
    if verdict == "proved" and not (isinstance(data.get("proof"), str) and data["proof"].strip()):
        raise PackageError("A proved answer needs a proof.")
    if "needs" in data and not (isinstance(data["needs"], list) and all(isinstance(x, str) for x in data["needs"])):
        raise PackageError("needs must be a list of strings.")
    if verdict == "need_context" and not data.get("needs"):
        raise PackageError("A need_context answer names what it needs.")
    if verdict == "false" and not (isinstance(data.get("counterexample"), str) and data["counterexample"].strip()):
        raise PackageError("A false answer needs a counterexample.")
    return verdict


def write_answer(run, goal_id, data, raw, tier=None, tokens_in=None, tokens_out=None):
    run = Path(run)
    manifest = rl.read_json(run / "MANIFEST.json")
    if manifest is None or goal_id not in {g["id"] for g in manifest["goals"]}:
        raise PackageError("No goal %s in %s." % (goal_id, run))
    verdict = parse_answer(data)
    answers = run / "answers"
    answers.mkdir(exist_ok=True)
    tokens = None if tokens_in is None and tokens_out is None else (tokens_in or 0) + (tokens_out or 0)
    meta = dict(verdict=verdict, tier=tier, tokens=tokens, tokens_in=tokens_in, tokens_out=tokens_out,
                needs=data.get("needs", []), counterexample=data.get("counterexample"),
                answer_bytes=len(raw.encode()), answer_sha256=sha(raw))
    problem = None
    if verdict == "proved":
        proof = data["proof"].strip() + "\n"
        problem = rl.answer_problems(proof)
        meta["proof_sha256"] = sha(proof)
        (answers / (goal_id + ".v")).write_text(proof)
    rl.write_json(answers / (goal_id + ".json"), meta)
    return verdict, problem


def cmd_answer(a):
    raw = Path(a.answer).read_text()
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as error:
        raise PackageError("The answer is not JSON: %s" % error)
    verdict, problem = write_answer(a.run, a.goal, data, raw, a.tier, a.tokens_in, a.tokens_out)
    print("ANSWER %s %s%s" % (a.goal, verdict, " (collect will refuse it: %s)" % problem if problem else ""))


# ---- addresses command ----

def cmd_addresses(a):
    failed = False
    for path in a.files:
        for row in address_matches(Path(path).read_text()):
            failed = True
            print("ADDRESS %s %s %s%s" % (path, row["source"], row["match"],
                                          " (%s)" % row["hex"] if "hex" in row else ""))
    sys.exit(1 if failed else 0)


# ---- spatial diagnosis ----

def spatial_records(log_text):
    """The `@@S` records of a log: dicts with kind, head, seek, seek_vars, res, defs, facts, counts.
    A `@@S skip <kind> error` line becomes a record with `skip` set."""
    records, current = [], None
    for line in log_text.split("\n"):
        line = rl.STAMP.sub(r"\2", line).rstrip()
        if not line.startswith("@@S "):
            continue
        body = line[4:]
        tag, _, rest = body.partition(" ")
        if tag == "skip":
            records.append(dict(skip=rest))
            current = None
        elif tag == "begin":
            current = dict(kind=rest, head=None, seek=None, seek_vars=[], res=[], defs=[], facts=[], counts=None)
            records.append(current)
        elif current is None:
            continue
        elif tag == "head":
            current["head"] = rest
        elif tag == "seek":
            sort, _, text = rest.partition(" ")
            current["seek"] = dict(sort=sort, text=text)
        elif tag == "seek-vars":
            current["seek_vars"] = rest.split()
        elif tag == "res":
            current["res"].append(rest)
        elif tag == "def":
            current["defs"].append(rest)
        elif tag == "fact":
            current["facts"].append(rest)
        elif tag == "counts":
            current["counts"] = dict(kv.split("=", 1) for kv in rest.split() if "=" in kv)
        elif tag == "end":
            current = None
    return [r for r in records if "skip" in r or r.get("head")]


DIAGNOSIS = """# Spatial leftover {id} ({function}, block +0x{block})

`zesu_block2` left an Iris goal open at the end of this block. Find why the lookup is stuck and
answer with one typed JSON object. Your answer is not a proof: the coordinator turns it into the
next obligation and reruns the block.

## Stuck judgment

- head: `{head}`
- seeks ({sort}): `{seek}`
- local variables of the sought term: {seek_vars}

## Owned resources (p: persistent, s: spatial; oldest first)

{res}

## Related definitions and pure facts

{facts}

{extra}## Answer form

Reply with exactly one JSON object; `kind` is one of `annotation`, `pure_goal`, `false`, `rule_gap`:

```json
{{"kind": "annotation", "annotation": {{"at": {{"pc": "+0x...", "boundary": "entry|loop_cut|join|call_site|call_return|function_return|access"}},
  "binders": [...], "resources": [...], "facts": [{{"coq": "...", "role": "..."}}],
  "placement": {{"array": "...", "index": "...", "scale": 8, "offset": 0}}}},
 "reason": "..."}}
{{"kind": "pure_goal", "statement": "forall ..., ... (an exact Rocq proposition that unblocks the lookup)", "reason": "..."}}
{{"kind": "false", "statement": "the entry statement that is wrong", "counterexample": "...", "reason": "..."}}
{{"kind": "rule_gap", "entailment": "a stand-alone Iris entailment the rule library misses", "reason": "..."}}
```

Name code by symbol and offset (`+0x...`), never by absolute address.
"""


def diagnosis_task(record, ident, function, block, extra):
    seek = record.get("seek") or dict(sort="none", text="")
    res = "\n".join("- `%s`" % line for line in record["res"]) or "- (none)"
    facts = "\n".join(["- def `%s`" % line for line in record["defs"]]
                      + ["- fact `%s`" % line for line in record["facts"]]) or "- (none)"
    return DIAGNOSIS.format(id=ident, function=function, block=block, head=record["head"], sort=seek["sort"],
                            seek=seek["text"] or "-", seek_vars=", ".join(record["seek_vars"]) or "-",
                            res=res, facts=facts, extra=extra)


def cmd_diagnose(a):
    run = Path(a.run)
    records = spatial_records(Path(a.log).read_text(errors="replace"))
    if not records:
        raise PackageError("No @@S record in %s." % a.log)
    sections = []
    if a.disasm:
        sections.append("## Disassembly\n\n```\n%s\n```\n" % Path(a.disasm).read_text().strip())
    for path in a.successors or ():
        sections.append("## Successor entry statement `%s`\n\n```coq\n%s\n```\n" % (Path(path).name,
                                                                                  Path(path).read_text().strip()))
    for n, record in enumerate(records, 1):
        ident = "%s/diagnosis/%s-%d" % (a.function, a.block, n)
        out = run / "diagnose" / ("%s-%d" % (a.block, n))
        out.mkdir(parents=True, exist_ok=True)
        if "skip" in record:
            rl.write_json(out / "REQUEST.json", dict(id=ident, record=record, next="skip"))
            print("DIAGNOSE %s skip %s" % (ident, record["skip"]))
            continue
        base = diagnosis_task(record, ident, a.function, a.block, "")
        remaining = a.max_prompt_bytes - len(base.encode())
        items = [("section:%d" % i, text) for i, text in enumerate(sections)]
        items.append(("hints", hint_slice(a.hints, a.pcs or ["+0x" + a.block], remaining)))
        extra, used = "", []
        for name, text in items:
            if text and len((base + extra + text + "\n").encode()) <= a.max_prompt_bytes:
                extra += text + "\n"
                used.append(name)
        text = diagnosis_task(record, ident, a.function, a.block, extra)
        (out / "TASK.md").write_text(text)
        rl.write_json(out / "REQUEST.json", dict(id=ident, function=a.function, block=a.block, record=record,
                                                 kinds=list(DIAGNOSIS_KINDS), task=str(out / "TASK.md"),
                                                 prompt_bytes=len(text.encode()), prompt_sha256=sha(text),
                                                 context_supplied=used, next="opus-medium"))
        print("DIAGNOSE %s task bytes=%d" % (ident, len(text.encode())))


def parse_diagnosis(data):
    if not isinstance(data, dict) or data.get("kind") not in DIAGNOSIS_KINDS:
        raise PackageError("The diagnosis needs a kind among %s." % ", ".join(DIAGNOSIS_KINDS))
    kind = data["kind"]
    need = dict(annotation=("annotation",), pure_goal=("statement",), false=("statement", "counterexample"),
                rule_gap=("entailment",))[kind]
    for key in need:
        if not data.get(key):
            raise PackageError("A %s diagnosis needs %s." % (kind, key))
    if kind == "annotation" and not isinstance(data["annotation"], dict):
        raise PackageError("annotation must be an object (a row of zesu.annotations.v1).")
    text = json.dumps(data, sort_keys=True)
    for pattern in ADDRESS_PATTERNS:
        if pattern.search(text):
            raise PackageError("The diagnosis names an absolute code address: %s." % pattern.search(text).group(0))
    return kind


def cmd_diagnosis_answer(a):
    task = Path(a.task)
    raw = Path(a.answer).read_text()
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as error:
        raise PackageError("The answer is not JSON: %s" % error)
    kind = parse_diagnosis(data)
    rl.write_json(task / "ANSWER.json", dict(answer=data, kind=kind, tier=a.tier, answer_bytes=len(raw.encode()),
                                             answer_sha256=sha(raw)))
    if kind == "pure_goal":
        (task / "pure_goal.txt").write_text(data["statement"].strip() + "\n")
    print("DIAGNOSIS %s %s" % (task.name, kind))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    g = sub.add_parser("goals")
    g.add_argument("--run", required=True)
    g.add_argument("--function", required=True)
    g.add_argument("--goal", action="append")
    g.add_argument("--tier", default="haiku-low")
    g.add_argument("--max-prompt-bytes", type=int, default=MAX_PROMPT_BYTES)
    g.add_argument("--index", help="similar.py index; default: built from the residual modules and the residual "
                                   "runs of every region beside RUN (similar.sibling_runs)")
    g.add_argument("--hints", help="hints/ dir of tools/oblig/hints.py build")
    g.add_argument("--falsify", action="store_true")
    g.add_argument("--defs", action="store_true", help="add the definitions context (defs.py); needs --bank")
    g.add_argument("--bank")
    g.add_argument("--ocamlpath")
    g.add_argument("--exec-dir")
    an = sub.add_parser("answer")
    an.add_argument("--run", required=True)
    an.add_argument("--goal", required=True)
    an.add_argument("--answer", required=True)
    an.add_argument("--tier")
    an.add_argument("--tokens-in", type=int)
    an.add_argument("--tokens-out", type=int)
    ad = sub.add_parser("addresses")
    ad.add_argument("files", nargs="+")
    dg = sub.add_parser("diagnose")
    dg.add_argument("--log", required=True)
    dg.add_argument("--run", required=True)
    dg.add_argument("--function", required=True)
    dg.add_argument("--block", required=True, help="4-hex offset of the block from the function symbol")
    dg.add_argument("--disasm")
    dg.add_argument("--successors", nargs="*")
    dg.add_argument("--hints")
    dg.add_argument("--pcs", nargs="*")
    dg.add_argument("--max-prompt-bytes", type=int, default=MAX_PROMPT_BYTES)
    da = sub.add_parser("diagnosis-answer")
    da.add_argument("--task", required=True)
    da.add_argument("--answer", required=True)
    da.add_argument("--tier")
    a = ap.parse_args(argv)
    try:
        {"goals": cmd_goals, "answer": cmd_answer, "addresses": cmd_addresses, "diagnose": cmd_diagnose,
         "diagnosis-answer": cmd_diagnosis_answer}[a.command](a)
    except PackageError as error:
        sys.exit("package: %s" % error)


if __name__ == "__main__":
    main()
