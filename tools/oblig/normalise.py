#!/usr/bin/env python3
"""Goal normaliser of pure residual goals (model-free), run before falsify, mechanical and packaging.

    normalise.py run     --run RUN [--goal ID ...] [--all] [--bank BANK] [--exec-dir DIR] [--binders FILE]
                         [--out DIR] [--apply] [--store ROOT] [--mechanical] [--jobs N]
    normalise.py compose --run RUN [--goal ID ...]

RUN is a run dir of tools/block/residual_loop.py (MANIFEST.json, goals/<id>/goal.v). A goal of a block
states `forall (args : <Region>BlockArgs) (H0 : <domain> args) ..., C`: a record binder and sealed or
folded premises, which falsify.py cannot instantiate and provers cannot read. `run` rewrites each open
goal (with --all also the closed ones, as a control) in Rocq, never by text:

1. UNFOLD (tools/oblig/normalise_tactic.v, inlined into a probe compile with the goal's imports and
   bank): intros, then each premise headed by `and`/`ex` is destructed (a witness becomes a variable),
   `True` and Automation2 markers are cleared, a sealed ZesuSsz constant `c` is rewritten with `c_eq`
   (the `Global Opaque` + unfold-lemma pattern), any other ZesuSsz constant is unfolded; library
   constants never are. The conclusion is unfolded the same way and split at `and`: one PART per
   conjunct.
2. GENERALISE (level 2): each ZesuSsz definition applied to a record variable is unfolded and each record
   projection (innermost first, nested records too) becomes a variable of the field's type named by its
   projection path (`keysBase_toOwnedList_arrayListLength`); the record binder disappears.
3. SLICE: the exporter of ZesuSsz/Automation2/ResidualExport.v prints each part over the facts its
   conclusion reaches; repeated facts are dropped.
4. LINK: `Lemma zn_link : N1 -> .. -> Nk -> G` with the Ltac1 script the tactic printed (intros,
   unfold/rewrite/destruct/clear of the premises, split, then `exact (zn_part_i <terms>)`), compiled
   with Qed. A level is used only when its link compiles.
5. GUARD: per part, first the snapshot screen (6), then falsify.py. A `false` of falsify.py on a part
   does not indict the goal: the goal falls back to level 1 (unfold and slice only, the record binder
   kept), then to level 0 (the goal itself). A part false on a real machine state stays at its level.
6. SNAPSHOT SCREEN: with --exec-dir (default: exec/ of RUN or of its first three ancestors) holding
   tools/oblig/exec/run.py snapshots at the goal's block offset, each data variable of a part takes its
   value through the region's binder map tools/oblig/exec/binders/<function>.json (entry values from
   STATE-0000 of the same input, block values from STATE-<block>; inputs of the map's run mode only);
   Rocq decides each premise and the conclusion (bool_decide, vm_compute). Verdicts:
   `false-on-real-state(<input>)` (kernel-checked refutation of the part), `true-on-<N>-states`,
   `premises-never-hold`, `not-evaluable` (with the reason). The screened statement is the part without
   the facts on witnesses of destructed existentials (the history ghosts of `zesu_hist`, whose values no
   machine state fixes; the tactic prints it as `screen`): a refutation says the part is false at that
   state for every history the generator's history statement allows.
7. MECHANICAL (--mechanical): the CONTROL_TACTIC of tools/residuals/residual_package.py on each part of
   the level used (with --control on the goal itself too, and falsify.py on it: the before/after
   measures), and, for a closed goal normalised into one part, its accepted proof on that part.

Output per goal: OUT/<id>/NORMALISE.json (default OUT = RUN/normalise): level used and why, parts (id,
statement, sha256, binders), link verdict, per-level falsify and screen verdicts, bytes before/after,
mechanical results. With --apply, a goal normalised at level 1 or 2 gets its parts as MANIFEST rows
`<block>-<n>` (goal dirs written as residual_loop.py writes them, `part_of` = the goal) and the goal the
row field `parts` and `normalised` (level, link script, link file); with --store ROOT, store.py sync
files the parts (the goal becomes `blocked-on` its first open part) and each part gets its falsity
event (tier `falsify`: state `false` on a kernel-refuted real state, else the screen verdict as class).

`compose` closes a goal whose parts all PASS: answers/<goal>.v becomes one proof script, each part's
accepted proof copied byte for byte into `assert (zn_part_i : Ni). { .. }` (the proof of the full part
statement, full-proof.v when residual_loop.py minimised it), then the link script; `residual_loop.py
collect` checks it against goal.v like any answer and `register` renders that lemma (parts are never
registered: rows with `part_of` are skipped).
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
import falsify  # noqa: E402
import residual_loop as rl  # noqa: E402

TACTIC = HERE / "normalise_tactic.v"
BINDERS = HERE / "exec" / "binders"
LEVELS = (2, 1)
EXPORT = "Require Import ZesuSsz.Automation2.ResidualExport."
LTAC2 = "From Ltac2 Require Import Ltac2."
CLASSIC = 'Set Default Proof Mode "Classic".'
SCHEMA = "oblig-normalise/1"
ENTRY = "0000"
CLAIM = 1 << 30  # booked memory per compile: the measured peak of a probe is 0.84 GiB (keysToOwnedSlice 0058)


class NormaliseError(ValueError):
    pass


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


# ---- the probe ----

def header_of(goal_v):
    """The import lines of a residual goal.v (everything before its Lemma)."""
    return goal_v[:goal_v.index("\nLemma ")].strip("\n").split("\n")


def probe_text(header, statement, levels=LEVELS):
    text = "\n".join(header) + "\n%s\n%s\n%s\n%s\n" % (EXPORT, LTAC2, TACTIC.read_text(), CLASSIC)
    for level in levels:
        text += "\nGoal %s.\nltac2:(zn_normalise %d).\nAbort.\n" % (statement, level)
    return text


def parse_probe(log_text):
    """{level: dict(parts=[dict(k, binders, statement)], refused=[...], link)} of the `@@N` records; the
    records of one level end with `done <level> <parts>`."""
    out, current = {}, dict(parts={}, refused=[], link=None)
    for line in log_text.split("\n"):
        line = rl.STAMP.sub(r"\2", line)
        if not line.startswith("@@N "):
            continue
        body = line[4:]
        if body.startswith("part "):
            _, k, kind, rest = (body.split(" ", 3) + [""])[:4]
            part = current["parts"].setdefault(int(k), dict(k=int(k), binders=[], statement=None))
            if kind == "binders":
                part["binders"] = rest.split()
            elif kind == "stmt":
                part["statement"] = rest.strip()
            elif kind == "screen":
                part["screen_statement"] = rest.strip()
            elif kind == "refused":
                current["refused"].append("part %s: %s" % (k, rest))
        elif body.startswith("link "):
            current["link"] = body[5:].strip()
        elif body.startswith("done "):
            level, count = (int(x) for x in body.split()[1:3])
            parts = [current["parts"][k] for k in sorted(current["parts"])]
            ok = (not current["refused"] and current["link"] and len(parts) == count
                  and all(p["statement"] for p in parts))
            out[level] = dict(parts=parts, refused=current["refused"], link=current["link"], complete=bool(ok))
            current = dict(parts={}, refused=[], link=None)
        elif body.startswith("fuel "):
            current["refused"].append(body)
    return out


def link_text(header, statement, parts, link):
    premises = "".join("(%s) ->\n  " % p["statement"] for p in parts)
    names = " ".join("zn_part_%d" % p["k"] for p in parts)
    return ("%s\n\nLemma zn_link :\n  %s(%s).\nProof.\nintros %s.\n%s\nQed.\n"
            % ("\n".join(header), premises, statement, names, link))


def composed_proof(parts, link, proofs):
    """The proof script (after `Proof.`) of the goal from the scripts PROOFS (each ending with Qed.) of
    its parts: each copied byte for byte into an assert, then the link script."""
    out = []
    for part, proof in zip(parts, proofs):
        body = proof.rstrip()
        if not body.endswith("Qed."):
            raise NormaliseError("part %d: its proof does not end with Qed." % part["k"])
        out.append("assert (zn_part_%d :\n  %s).\n{ %s\n}\n" % (part["k"], part["statement"], body[:-len("Qed.")].rstrip()))
    return "".join(out) + link + "\nQed.\n"


# ---- the snapshot screen ----

def load_binder_map(function, path=None):
    path = Path(path) if path else BINDERS / ("%s.json" % function)
    if not path.is_file():
        return None
    data = json.loads(path.read_text())
    if data.get("schema") != "oblig-exec-binders/1":
        raise NormaliseError("%s: schema is not oblig-exec-binders/1" % path)
    return data


def snapshot_states(exec_dir, block, mode):
    """[(input id, visit, entry visit, block visit)] of the inputs of run mode MODE (dir suffix
    `.<mode>`, no other option) that reach BLOCK."""
    out = []
    if not exec_dir or not Path(exec_dir).is_dir():
        return out
    for directory in sorted(p for p in Path(exec_dir).iterdir() if p.is_dir()):
        name = directory.name
        if mode and not name.endswith("." + mode):
            continue
        if mode and "." in name[:-len(mode) - 1]:
            continue
        entry, here = directory / ("STATE-%s.json" % ENTRY), directory / ("STATE-%s.json" % block)
        if not entry.is_file() or not here.is_file():
            continue
        first = json.loads(entry.read_text())["visits"][0]
        for visit in json.loads(here.read_text())["visits"]:
            out.append((name, visit["visit"], first, visit))
    return out


def _regs(visit):
    regs = {}
    for name, raw in visit["regs"].items():
        value = falsify.as_int(raw)
        regs[name] = value
        regs[falsify.ABI.get(name, name)] = value
    return regs


def _memory(visit):
    return {m["name"]: (m["base"], bytes.fromhex(m["hex"])) for m in visit["memory"]}


def _bytes_at(visit, address, count):
    for base, data in _memory(visit).values():
        if base <= address and address + count <= base + len(data):
            return data[address - base:address - base + count]
    return None


def source_value(source, entry, block, groups=()):
    """The int, or dict(hex=...) for bytes, of one binder-map SOURCE; None when the snapshot lacks it."""
    if "const" in source:
        return source["const"]
    visit = entry if source.get("at", "entry") == "entry" else block
    if "reg" in source:
        name = re.sub(r"\\(\d)", lambda m: groups[int(m[1]) - 1], source["reg"])
        return _regs(visit).get(name)
    if "mem" in source:
        found = _memory(visit).get(source["mem"])
        if found is None:
            return None
        data = found[1][source["offset"]:source["offset"] + source["size"]]
        return int.from_bytes(data, "little") if len(data) == source["size"] else None
    if "bytes" in source:
        found = _memory(visit).get(source["bytes"])
        return dict(hex=found[1].hex()) if found else None
    if "deref" in source:
        pointer = source_value(dict(source["deref"], at=source.get("at", "entry")), entry, block)
        count = source_value(dict(source["length"], at=source.get("at", "entry")), entry, block)
        if pointer is None or count is None:
            return None
        size = count * int(source.get("scale", 1))
        if size == 0:
            return dict(hex="")
        data = _bytes_at(visit, pointer, size)
        return dict(hex=data.hex()) if data is not None else None
    raise NormaliseError("unknown binder-map source %r" % source)


def map_binder(name, rows):
    for row in rows:
        match = re.search(row["pattern"], name)
        if match:
            return row["source"], match.groups()
    return None, ()


def screen_rows(binders, states, binder_map):
    """(rows for falsify.search_text, unmapped binder names): one row per snapshot state."""
    data = [b for b in binders if b["kind"] != "prop"]
    unmapped = sorted({b["name"] for b in data if map_binder(b["name"], binder_map["binders"])[0] is None})
    if unmapped:
        return [], unmapped
    rows, missing = [], set()
    for input_id, visit, entry, block in states:
        values = {}
        for b in data:
            source, groups = map_binder(b["name"], binder_map["binders"])
            value = source_value(source, entry, block, [g or "" for g in groups])
            if value is None:
                missing.add(b["name"])
                break
            if b["kind"] == "bytes":
                if not isinstance(value, dict):
                    missing.add(b["name"])
                    break
            elif isinstance(value, dict):
                missing.add(b["name"])
                break
            elif b["kind"] == "bv":
                value %= 2 ** b["width"]
            elif b["kind"] == "bool":
                value = bool(value)
            values[b["name"]] = value
        else:
            rows.append(dict(values=values, origin="%s#%d" % (input_id, visit)))
    return rows, sorted(missing)


def screen(goal, route, out, states, binder_map):
    """The snapshot verdict of the lemma in GOAL (a goal.v): dict(verdict, ...); writes OUT/SCREEN.json."""
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    report = dict(goal=str(goal), states=len(states))
    if binder_map is None:
        report.update(verdict="not-evaluable", reason="no binder map")
        return finish_screen(out, report)
    if not states:
        report.update(verdict="not-evaluable", reason="no snapshot of mode %s reaches the block" % binder_map.get("mode"))
        return finish_screen(out, report)
    goal_preamble, statement, _ = falsify.read_goal(goal)
    pre = falsify.preamble(goal_preamble, statement, route.args, route.coqlib)
    tag = "screen-" + sha(statement)[:12]
    (out / "probe.v").write_text(falsify.probe_text(pre, statement))
    result, text = route.compile(out / "probe.v", tag + "-probe")
    binders, ended = falsify.parse_binders(falsify.records(text))
    if result["returncode"] != 0 or not ended:
        report.update(verdict="not-evaluable", reason="probe failed: " + falsify.first_error(text))
        return finish_screen(out, report)
    other = [b["name"] for b in binders if b["kind"] not in falsify.CHECKED_KINDS]
    if other:
        report.update(verdict="not-evaluable", reason="binder type outside falsify.py's range: " + ", ".join(other))
        return finish_screen(out, report)
    rows, missing = screen_rows(binders, states, binder_map)
    if not rows:
        report.update(verdict="not-evaluable", reason="binders without a snapshot value: " + ", ".join(missing))
        return finish_screen(out, report)
    (out / "search.v").write_text(falsify.search_text(pre, statement, binders, rows))
    result, text = route.compile(out / "search.v", tag + "-search")
    outcomes = falsify.search_outcomes(falsify.records(text))
    if result["returncode"] != 0 or len(outcomes) != len(rows):
        report.update(verdict="not-evaluable", reason="search compile failed: " + falsify.first_error(text))
        return finish_screen(out, report)
    report["rows"] = [dict(origin=row["origin"], **outcomes[k]) for k, row in enumerate(rows)]
    hits = [k for k, o in sorted(outcomes.items()) if o["hit"]]
    if hits:
        row = rows[hits[0]]
        (out / "refute.v").write_text(falsify.refute_text(pre, statement, binders, row["values"]))
        result, text = route.compile(out / "refute.v", tag + "-refute")
        if result["returncode"] == 0:
            report.update(verdict="false-on-real-state(%s)" % row["origin"].split("#")[0], hit=row,
                          refute=str(out / "refute.v"))
            return finish_screen(out, report)
        report["refute_error"] = falsify.compile_error(text)
    decided = [o for o in outcomes.values() if not (o["nodec"] or o["stuck"])]
    tested = sum(1 for o in decided if o["concl"])
    if tested:
        report.update(verdict="true-on-%d-states" % tested)
    elif decided:
        report.update(verdict="premises-never-hold")
    else:
        report.update(verdict="not-evaluable", reason="no state could be decided (a fact has no Decision instance)")
    return finish_screen(out, report)


def finish_screen(out, report):
    rl.write_json(Path(out) / "SCREEN.json", report)
    return report


# ---- compiles of one goal ----

def compile_ok(route, path, tag):
    result, text = route.compile(path, tag)
    return result["returncode"] == 0, text


def mechanical(route, header, name, statement, out, tag):
    """True when the mechanical tier's script proves STATEMENT (one compile)."""
    out.mkdir(parents=True, exist_ok=True)
    path = out / "mechanical.v"
    path.write_text("%s\n\nLemma %s :\n  %s.\n%s" % ("\n".join(header), name, statement, rl.pkg.CONTROL_TACTIC))
    return compile_ok(route, path, tag)[0]


def accepted_proof(goal_dir):
    """The accepted proof script of a closed goal (of its full statement), or None."""
    for name in ("full-proof.v", "proof.v"):
        path = goal_dir / name
        status = rl.read_json(goal_dir / "STATUS.json", {})
        if path.is_file() and status.get("result") == "PASS":
            text = path.read_text()
            return text[text.index("\nProof.\n") + len("\nProof.\n"):]
    return None


def part_name(manifest, statement):
    return rl.rrm.lemma_prefix(manifest["block"], manifest.get("function")) + sha(statement)[:16]


def falsify_part(route, goal, out):
    report = falsify.check(goal, route, out)
    return dict(verdict=report["verdict"], reason=report.get("reason"), hit=(report.get("hit") or {}).get("assignment"))


def normalise_goal(run, manifest, goal, route, out, states, binder_map, run_mechanical=False, control=False):
    """Normalise one goal; returns its NORMALISE.json record (written to OUT/<id>/). CONTROL also runs
    falsify.py and (with RUN_MECHANICAL) the mechanical tier on the goal itself."""
    run = Path(run)
    gdir = run / "goals" / goal["id"]
    goal_v = (gdir / ("full-goal.v" if (gdir / "full-goal.v").is_file() else "goal.v")).read_text()
    header = header_of(goal_v)
    statement = goal.get("statement")
    d = Path(out) / goal["id"]
    d.mkdir(parents=True, exist_ok=True)
    record = dict(schema=SCHEMA, id=goal["id"], function=manifest.get("function"), block=manifest["block"],
                  statement_sha256=sha(statement), original_bytes=len(statement.encode()),
                  status=rl.read_json(gdir / "STATUS.json", {}).get("result"), levels={})
    tag = "norm-%s-%s" % (manifest["block"], sha(statement)[:10])
    (d / "probe.v").write_text(probe_text(header, statement))
    result, text = route.compile(d / "probe.v", tag + "-probe")
    found = parse_probe(text) if result["returncode"] == 0 else {}
    if result["returncode"] != 0:
        record["probe_error"] = falsify.first_error(text)
    if control:
        record["falsify_before"] = falsify_part(route, gdir / "goal.v", d / "falsify-before")["verdict"]
    chosen = None
    for level in LEVELS:
        info = found.get(level)
        row = dict(parts=len(info["parts"]) if info else 0)
        record["levels"][str(level)] = row
        if not info or not info["complete"]:
            row["refused"] = (info or {}).get("refused") or ["no probe output"]
            continue
        parts = info["parts"]
        row["bytes"] = sum(len(p["statement"].encode()) for p in parts)
        ld = d / ("level-%d" % level)
        ld.mkdir(exist_ok=True)
        (ld / "link.v").write_text(link_text(header, statement, parts, info["link"]))
        ok, text = compile_ok(route, ld / "link.v", "%s-link%d" % (tag, level))
        row["link"] = "PASS" if ok else "FAIL"
        if not ok:
            row["link_error"] = rl.errors_of(text, limit=8)
            continue
        verdicts = []
        for p in parts:
            pd = ld / ("part-%d" % p["k"])
            pd.mkdir(exist_ok=True)
            p["name"] = part_name(manifest, p["statement"])
            (pd / "goal.v").write_text(rl.goal_text(header, p["name"], p["statement"]))
            screened = pd / "goal.v"
            if p.get("screen_statement") and p["screen_statement"] != p["statement"]:
                screened = pd / "screen-goal.v"
                screened.write_text(rl.goal_text(header, p["name"] + "_screen", p["screen_statement"]))
            p["screen"] = screen(screened, route, pd / "screen", states, binder_map)["verdict"]
            p["falsify"] = falsify_part(route, pd / "goal.v", pd / "falsify")
            verdicts.append((p["screen"], p["falsify"]["verdict"]))
        row["screen"] = [s for s, _ in verdicts]
        row["falsify"] = [f for _, f in verdicts]
        real = any(s.startswith("false-on-real-state") for s, _ in verdicts)
        if not real and any(f == "false" for _, f in verdicts):
            row["fallback"] = "falsify.py refuted a part"
            continue
        chosen = dict(level=level, parts=parts, link=info["link"], dir=str(ld))
        break
    if chosen is None:
        record.update(level=0, parts=[], screen=None, falsify_after=record.get("falsify_before"))
        if states is not None:
            record["screen"] = screen(gdir / "goal.v", route, d / "screen-original", states, binder_map)["verdict"]
    else:
        parts = chosen["parts"]
        record.update(level=chosen["level"], link=chosen["link"], link_file=str(Path(chosen["dir"]) / "link.v"),
                      normalised_bytes=sum(len(p["statement"].encode()) for p in parts),
                      parts=[dict(k=p["k"], name=p["name"], statement=p["statement"], sha256=sha(p["statement"]),
                                  binders=p["binders"], screen=p["screen"], falsify=p["falsify"],
                                  goal=str(Path(chosen["dir"]) / ("part-%d" % p["k"]) / "goal.v")) for p in parts],
                      screen=worst_screen([p["screen"] for p in parts]),
                      falsify_after=worst_falsify([p["falsify"]["verdict"] for p in parts]))
    if run_mechanical:
        if control:
            record["mechanical_before"] = mechanical(route, header, goal["name"], statement, d / "mech-before",
                                                     tag + "-mech0")
        if chosen:
            record["mechanical_after"] = all(
                mechanical(route, header, p["name"], p["statement"], Path(chosen["dir"]) / ("part-%d" % p["k"]),
                           "%s-mech%d" % (tag, p["k"])) for p in chosen["parts"])
            proof = accepted_proof(gdir)
            if proof is not None and len(chosen["parts"]) == 1:
                p = chosen["parts"][0]
                path = Path(chosen["dir"]) / ("part-%d" % p["k"]) / "accepted.v"
                path.write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s" % ("\n".join(header), p["name"], p["statement"], proof))
                record["accepted_proof_on_normalised"] = compile_ok(route, path, tag + "-acc")[0]
    rl.write_json(d / "NORMALISE.json", record)
    return record


def worst_screen(verdicts):
    for prefix in ("false-on-real-state", "not-evaluable", "premises-never-hold"):
        hit = [v for v in verdicts if v.startswith(prefix)]
        if hit:
            return hit[0]
    return min(verdicts, key=lambda v: int(re.search(r"\d+", v)[0])) if verdicts else None


def worst_falsify(verdicts):
    for verdict in ("false", "unchecked"):
        if verdict in verdicts:
            return verdict
    return "passed" if verdicts else None


# ---- apply: parts as MANIFEST rows ----

def apply(run, manifest, goal, record, reparse=None):
    """Add the parts of RECORD as goals of RUN (part_of = goal) and mark the goal; returns the part ids.
    REPARSE(dir, tag, statement, args, ocamlpath) is residual_loop.py's round-trip check (the tests
    replace it)."""
    run = Path(run)
    reparse = reparse or rl.reparse
    if record["level"] == 0 or goal.get("parts"):
        return goal.get("parts") or []
    args, ocamlpath = rl.bank_args(manifest["bank"])
    header = header_of((run / "goals" / goal["id"] / "goal.v").read_text())
    ids = rl.next_ids(manifest["goals"], manifest["block"], len(record["parts"]))
    rows = []
    for gid, part in zip(ids, record["parts"]):
        row = dict(id=gid, name=part["name"], statement=part["statement"], source="normalised", copies=1,
                   binders=part["binders"], counts={}, conclusion_definitions=[], round=goal.get("round"),
                   part_of=goal["id"], part=part["k"])
        d = rl.write_goal(run, row, header, args, ocamlpath)
        row.update(reparse(d, "rt-" + gid, row["statement"], args, ocamlpath))
        if row["reparse"] == "exact":
            rl.write_task(run, manifest["block"], row, header)
        rl.write_json(d / "STATUS.json", dict(attempts=[], result="OPEN" if row["reparse"] == "exact" else "REFUSED"))
        for name in ("screen", "falsify"):
            source = Path(part["goal"]).parent / name
            if source.is_dir():
                shutil.copytree(source, d / name, dirs_exist_ok=True)
        rows.append(row)
    manifest["goals"].extend(rows)
    goal["parts"] = [row["id"] for row in rows]
    goal["normalised"] = dict(level=record["level"], link=record["link"], link_file=record["link_file"])
    rl.write_json(run / "MANIFEST.json", manifest)
    return goal["parts"]


def file_events(store_root, function, run, manifest, record, part_ids):
    """store.py sync, then each part's falsity event (tier `falsify`)."""
    import store
    store.sync(function, store_root)
    state = store.fold(store.read_events(store_root))
    rows = []
    by_id = {g["id"]: g for g in manifest["goals"]}
    for gid, part in zip(part_ids, record["parts"]):
        identifier = store.goal_id(function, manifest["block"], by_id[gid]["statement"])
        item = state.get(identifier)
        if item is None or any(row.get("tier") == "falsify" for row in item["events"]):
            continue
        screen_json = Path(run) / "goals" / gid / "screen" / "SCREEN.json"
        artifact = store.artifact_of(screen_json) if screen_json.is_file() else None
        if part["screen"].startswith("false-on-real-state"):
            st, cls = "false", item["goal_class"]
        else:
            st, cls = "derived", item["goal_class"] or part["screen"]
        rows.append(store.event(id=identifier, function=function, kind="goal", parent=item["parent"], state=st,
                                **{"class": cls}, tier="falsify", artifact=artifact, head=store.git_head()))
    if rows:
        store.append(store_root, rows)
    return len(rows)


# ---- compose ----

def compose(run, goal_ids=()):
    """Write answers/<goal>.v for each goal with parts whose parts all PASS; returns the goal ids."""
    run = Path(run)
    manifest = rl.read_json(run / "MANIFEST.json")
    by_id = {g["id"]: g for g in manifest["goals"]}
    done = []
    for goal in manifest["goals"]:
        if not goal.get("parts") or (goal_ids and goal["id"] not in goal_ids):
            continue
        status = rl.read_json(run / "goals" / goal["id"] / "STATUS.json", {})
        if status.get("result") == "PASS":
            continue
        proofs, parts = [], []
        for gid in goal["parts"]:
            part = by_id[gid]
            proof = accepted_proof(run / "goals" / gid)
            if proof is None:
                break
            proofs.append(proof)
            parts.append(dict(k=part["part"], statement=part["statement"]))
        else:
            answer = run / "answers" / (goal["id"] + ".v")
            answer.parent.mkdir(parents=True, exist_ok=True)
            answer.write_text(composed_proof(parts, goal["normalised"]["link"], proofs))
            done.append(goal["id"])
    return done


# ---- CLI ----

def default_exec(run):
    """The exec/ of the run dir or of its first ancestors (the function run dir holds it)."""
    run = Path(run).resolve()
    for candidate in [run / "exec"] + [parent / "exec" for parent in list(run.parents)[:3]]:
        if candidate.is_dir():
            return candidate
    return None


def cmd_run(a):
    run = Path(a.run)
    manifest = rl.read_json(run / "MANIFEST.json")
    if manifest is None:
        raise NormaliseError("No MANIFEST.json in %s." % run)
    route = falsify.Route(a.bank or manifest["bank"], a.ocamlpath, claim=CLAIM)
    function = manifest.get("function")
    binder_map = load_binder_map(function, a.binders)
    exec_dir = Path(a.exec_dir) if a.exec_dir else default_exec(run)
    states = snapshot_states(exec_dir, manifest["block"], (binder_map or {}).get("mode"))
    out = Path(a.out) if a.out else run / "normalise"
    goals = []
    for goal in manifest["goals"]:
        if goal.get("part_of") or goal.get("reparse") != "exact":
            continue
        if a.goal and goal["id"] not in a.goal:
            continue
        status = rl.read_json(run / "goals" / goal["id"] / "STATUS.json", {})
        if status.get("result") == "PASS" and not a.all:
            continue
        goals.append(goal)

    def one(goal):
        return goal, normalise_goal(run, manifest, goal, route, out, states, binder_map, a.mechanical, a.control)
    with ThreadPoolExecutor(max_workers=max(1, a.jobs)) as pool:
        results = list(pool.map(one, goals))
    for goal, record in results:
        parts = []
        if a.apply and record["status"] != "PASS":
            parts = apply(run, manifest, goal, record)
            if a.store and parts:
                file_events(Path(a.store), function, run, manifest, record, parts)
        print("NORMALISE %s level=%d parts=%d bytes=%d->%s screen=%s falsify=%s->%s%s" % (
            goal["id"], record["level"], len(record["parts"]), record["original_bytes"],
            record.get("normalised_bytes", "-"), record.get("screen"), record.get("falsify_before", "-"),
            record.get("falsify_after"), " applied=" + ",".join(parts) if parts else ""))


def cmd_compose(a):
    for gid in compose(a.run, set(a.goal or ())):
        print("COMPOSED %s" % gid)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    r = sub.add_parser("run")
    r.add_argument("--run", required=True)
    r.add_argument("--goal", action="append")
    r.add_argument("--all", action="store_true", help="closed goals too (a control; never applied)")
    r.add_argument("--bank", help="default: the MANIFEST's bank")
    r.add_argument("--ocamlpath")
    r.add_argument("--exec-dir", help="run.py snapshots (default: exec/ of RUN or of its first three ancestors)")
    r.add_argument("--binders", help="binder map (default tools/oblig/exec/binders/<function>.json)")
    r.add_argument("--out", help="default RUN/normalise")
    r.add_argument("--apply", action="store_true", help="add the parts as goals of RUN")
    r.add_argument("--store", help="function run dir of the store (with --apply: sync and falsity events)")
    r.add_argument("--mechanical", action="store_true")
    r.add_argument("--control", action="store_true", help="falsify.py and --mechanical on the goal itself too")
    r.add_argument("--jobs", type=int, default=4)
    c = sub.add_parser("compose")
    c.add_argument("--run", required=True)
    c.add_argument("--goal", action="append")
    a = ap.parse_args(argv)
    try:
        {"run": cmd_run, "compose": cmd_compose}[a.command](a)
    except NormaliseError as error:
        sys.exit("normalise: %s" % error)


if __name__ == "__main__":
    main()
