#!/usr/bin/env python3
"""Print one message per refused goal from a diagnostic block compile.

The compile must import `ZesuSsz.Automation2.DiagnosticsOn` (after
`ZesuSsz.Automation2.All`) and should set a large printing width. The hooks in
`ZesuSsz/Automation2/Diagnostics.v` then print `@@D` lines: a `step` event for
each iteration of the stepping loop (with the next `pc` at an instruction
boundary and every side condition that a step raises), a `stage` event with
the context facts at each closing stage, and at the end one `refuse final`
record per open goal with its relevant facts and the full goal.

    refusal_report.py LOG [--objdump FILE] [--expect REGEX] [--control LOG] [--json]

For each refusal the message names the step and pc where the goal was raised,
the instruction at that pc, the goal head, the last closing stage that ran on
the goal, and the stage where each relevant fact first appears. The verdict
`fact-after-finisher` marks a relevant fact that first appears after the last
finisher stage that ran on the goal. `--expect` names the statement of a fact
that should close the goal; `--control` then reports where a fact of that
statement first appears in another run (for example the unchanged block).
A line may carry a leading time stamp (`<seconds> `); stage times are then
reported too.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OBJDUMP = ROOT / "build/stock-zisk/disassembly.objdump"
STAMP = re.compile(r"^(\d+\.\d+) (.*)$")
CONTINUATION_STOP = ("@@", "Chars ", "Warning", "File ", "Error", "Tactic call", "Finished ", "[", "Closed under",
                     "Axioms:")
FINISHER_PREFIX = "finish"


def records(lines):
    """Join wrapped output lines into one record per `@@` line."""
    current = None
    for raw in lines:
        raw = raw.rstrip("\n")
        match = STAMP.match(raw)
        stamp, text = (float(match.group(1)), match.group(2)) if match else (None, raw)
        if text.startswith("@@"):
            if current is not None:
                yield current
            current = [stamp, text]
        elif current is not None and text.strip() and not text.startswith(CONTINUATION_STOP):
            current[1] += " " + text.strip()
        else:
            if current is not None:
                yield current
            current = None
    if current is not None:
        yield current


def number(text):
    text = re.sub(r"%[A-Za-z]+$", "", text.strip().strip("()")).strip()
    try:
        return int(text, 0)
    except ValueError:
        return None


def parse(lines):
    """Return steps, side condition events, stages and refusals from a log."""
    state = dict(step=0, pc=None)
    sideconds, stages, refusals, named = [], [], [], {}
    target = None  # the record that `head`, `fact` and printer lines belong to
    for stamp, text in records(lines):
        if text == "@@D step":
            state["step"] += 1
            target = dict(kind="step")
        elif text.startswith("@@D pc "):
            state["pc"] = number(text[len("@@D pc "):]) or state["pc"]
        elif text.startswith("@@D sidecond "):
            skeleton = text[len("@@D sidecond "):]
            if target is not None and target.get("kind") == "refuse":
                target["sidecond"] = skeleton
            else:
                sideconds.append(dict(skeleton=skeleton, step=state["step"], pc=state["pc"]))
        elif text.startswith("@@D names"):
            for name in text[len("@@D names"):].split():
                named.setdefault(name, dict(step=state["step"], pc=state["pc"]))
        elif text.startswith("@@D head "):
            if target is not None:
                target["head"] = text[len("@@D head "):]
        elif text.startswith("@@D stage "):
            target = dict(kind="stage", name=text[len("@@D stage "):].strip().strip('"'), step=state["step"],
                          pc=state["pc"], time=stamp, facts={}, big=set(), index=len(stages))
            stages.append(target)
        elif text == "@@D step-end":
            target = dict(kind="step-end")
        elif text.startswith("@@D refuse "):
            target = dict(kind="refuse", what=text[len("@@D refuse "):].strip().strip('"'), step=state["step"],
                          pc=state["pc"], time=stamp, facts={}, big=set(), relevant=[], hyps={},
                          index=len(stages))
            refusals.append(target)
        elif text.startswith("@@D relevant"):
            if target is not None and target.get("kind") == "refuse":
                target["relevant"] = text[len("@@D relevant"):].split()
        elif text.startswith("@@D fact "):
            name, _, statement = text[len("@@D fact "):].partition(" : ")
            if target is not None and "facts" in target:
                target["facts"][name.strip()] = statement.strip()
        elif text.startswith("@@D bigfact "):
            if target is not None and "big" in target:
                target["big"].add(text[len("@@D bigfact "):].strip())
        elif text.startswith("@@HYP "):
            name, _, statement = text[len("@@HYP "):].partition(" : ")
            if target is not None and target.get("kind") == "refuse":
                target["hyps"][name.strip()] = statement.strip()
        elif text.startswith("@@CONCL "):
            if target is not None and target.get("kind") == "refuse":
                target["conclusion"] = text[len("@@CONCL "):]
    return dict(steps=state["step"], sideconds=sideconds, stages=stages, refusals=refusals, named=named)


def instructions(path):
    table = {}
    if path is None or not Path(path).exists():
        return table
    line = re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]+\s+(.*)$")
    for text in Path(path).read_text(errors="replace").splitlines():
        match = line.match(text)
        if match:
            table[int(match.group(1), 16)] = " ".join(match.group(2).split())
    return table


def raised_at(refusal, sideconds):
    """The step that raised the refused side condition, else the last step."""
    skeleton = refusal.get("sidecond")
    if skeleton:
        for event in reversed(sideconds):
            if event["skeleton"] == skeleton and event["step"] <= refusal["step"]:
                return event["step"], event["pc"], True
    return refusal["step"], refusal["pc"], False


def first_seen(name, statement, stages):
    for stage in stages:
        if statement is not None and stage["facts"].get(name) == statement:
            return stage
        if statement is None and (name in stage["facts"] or name in stage["big"]):
            return stage
    return None


def first_matching(pattern, stages):
    for stage in stages:
        for name, statement in stage["facts"].items():
            if pattern.search(statement):
                return stage, name, statement
    return None


def analyze(parsed, table, expect=None, control=None):
    stages = parsed["stages"]
    messages = []
    for number_, refusal in enumerate(parsed["refusals"], 1):
        step, pc, raised = raised_at(refusal, parsed["sideconds"])
        head = refusal.get("head", "?")
        own = [stage for stage in stages[:refusal["index"]] if stage.get("head") == head]
        last = own[-1] if own else (stages[refusal["index"] - 1] if refusal["index"] else None)
        finishers = [stage for stage in own if stage["name"].startswith(FINISHER_PREFIX)]
        facts = []
        for name in refusal["relevant"]:
            statement = refusal["facts"].get(name, refusal["hyps"].get(name))
            stage = first_seen(name, refusal["facts"].get(name), stages[:refusal["index"]])
            first = parsed["named"].get(name)
            facts.append(dict(name=name, statement=statement,
                              stage=stage["name"] if stage else None,
                              stage_index=stage["index"] if stage else None,
                              step=first["step"] if first else (stage["step"] if stage else None),
                              pc=first["pc"] if first else None))
        if not finishers:
            verdict = "no-finisher-on-this-goal"
        elif any(f["stage_index"] is not None and f["stage_index"] > finishers[-1]["index"] for f in facts):
            verdict = "fact-after-finisher"
        else:
            verdict = "facts-before-finisher"
        message = dict(number=number_, kind=refusal["what"], step=step, pc=pc, raised_at_step=raised,
                       instruction=table.get(pc) if pc is not None else None, head=head,
                       last_stage=last["name"] if last else None,
                       last_stage_step=last["step"] if last else None,
                       finisher_stages=len(finishers), facts=facts, verdict=verdict,
                       conclusion=refusal.get("conclusion"))
        if expect is not None:
            present = [name for name, statement in {**refusal["hyps"], **refusal["facts"]}.items()
                       if expect.search(statement)]
            message["expect"] = dict(pattern=expect.pattern, present=present)
            if control is not None:
                found = first_matching(expect, control["stages"])
                first = control["named"].get(found[1]) if found else None
                step, pc = (first["step"], first["pc"]) if first else (
                    (found[0]["step"], found[0]["pc"]) if found else (None, None))
                message["expect"]["control"] = None if found is None else dict(
                    stage=found[0]["name"], stage_index=found[0]["index"], step=step, pc=pc,
                    instruction=table.get(pc), name=found[1], statement=found[2])
        messages.append(message)
    return messages


def render(message):
    pc = "?" if message["pc"] is None else hex(message["pc"])
    where = "raised" if message["raised_at_step"] else "last"
    lines = ["REFUSAL %s #%d step=%s (%s) pc=%s insn=\"%s\" head=\"%s\" last_stage=%s@step%s" % (
        message["kind"], message["number"], message["step"], where, pc, message["instruction"] or "?",
        message["head"], message["last_stage"], message["last_stage_step"])]
    shown = ["%s@step %s/%s" % (f["name"], f["step"], "stage %s#%s" % (f["stage"], f["stage_index"])
                               if f["stage"] else "no stage") for f in message["facts"]]
    lines.append("  facts: %s" % (" ".join(shown) if shown else "(none share a term with the goal)"))
    lines.append("  verdict=%s (finisher stages on this goal: %d)" % (message["verdict"],
                                                                    message["finisher_stages"]))
    if "expect" in message:
        expect = message["expect"]
        state = "present: " + " ".join(expect["present"]) if expect["present"] else "absent in this run"
        lines.append("  expect /%s/: %s" % (expect["pattern"], state))
        if "control" in expect:
            found = expect["control"]
            if found is None:
                lines.append("  control: no fact matches")
            else:
                lines.append("  control: first at step %s pc %s insn=\"%s\" (first closing stage %s#%s) as %s : %s" % (
                    found["step"],
                    "?" if found["pc"] is None else hex(found["pc"]), found["instruction"] or "?",
                    found["stage"], found["stage_index"], found["name"], found["statement"]))
    return "\n".join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("log", type=Path)
    parser.add_argument("--objdump", type=Path, default=DEFAULT_OBJDUMP)
    parser.add_argument("--expect", help="regular expression for the statement of the closing fact")
    parser.add_argument("--control", type=Path, help="log of a run where the expected fact exists")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    parsed = parse(args.log.read_text(errors="replace").splitlines())
    control = parse(args.control.read_text(errors="replace").splitlines()) if args.control else None
    expect = re.compile(args.expect) if args.expect else None
    messages = analyze(parsed, instructions(args.objdump), expect, control)
    if args.json:
        print(json.dumps(messages, indent=1))
    else:
        for message in messages:
            print(render(message))
    return 0


if __name__ == "__main__":
    sys.exit(main())
