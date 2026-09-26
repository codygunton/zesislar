#!/usr/bin/env python3
"""WP4: infer a segment's exit boundary by running the block to it.

The boundary predicate of a segment is whatever the block automation still
holds when it arrives at the exit address. So the inference removes the
hypothesis that supplies the boundary, runs the automation, and reads the
context at the stop.

Three things can happen, and the tool reports which:

- `reached`: the automation arrives at the exit and the printed context is
  the inferred boundary.
- `stalled`: the automation stops earlier on a residual. That residual is a
  ticket for WP6, not a hand line, and the tool records its class and its
  normalized signature so the tickets can be ranked.
- `error`: the probe did not compile.

A driver file may supply the sentences that carry the run past a known
stall, one per line, so a boundary can be inferred before the rule that
removes the stall exists.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "residual"))

import probes  # noqa: E402
import timed  # noqa: E402
from classify import classify  # noqa: E402
from goals import conclusion_text, context_size, split_goals, split_goal  # noqa: E402
from call_sites import premises as call_premises  # noqa: E402
from modules import find_proof  # noqa: E402
from signature import signature  # noqa: E402

PROOF_DIR = Path("ZesuSsz/Proofs/WriteSuccess")
SCRATCH = Path("tools/coqc_scratch.sh")
REACHED = "BOUNDARY-REACHED"
RAW_BEGIN = "BOUNDARY-ALL-GOALS-BEGIN"
RAW_END = "BOUNDARY-ALL-GOALS-END"


# Islaris already resolves an instruction fetch from `instr_lookup_resources`
# (InstrSpecs/Lookup.v). What it cannot do is see that resource inside a
# folded project bundle, which is the corpus's largest gap: 122 proofs and
# 888 hand lines. A generated module does not need the bundle at all, so the
# inference states the code premise in the shape the automation can use.
CODE_PREMISES = [
    "  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗",
    "  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗",
]
CODE_BUNDLE = re.compile(r"writeSuccessCompleteNativeCode|instr_map|"
                         r"instr_lookup_resources|spec_instr_resources")


def with_standard_code(lines: list[str]) -> list[str]:
    """Replace whatever code premise the lemma has with the standard pair."""
    out, dropping, inserted = [], False, False
    for line in lines:
        if CODE_BUNDLE.search(line) and "instr_body" not in line:
            dropping = True
            if not inserted:
                out.extend(CODE_PREMISES)
                inserted = True
            if line.rstrip().endswith("-∗"):
                dropping = False
            continue
        if dropping:
            if line.rstrip().endswith("-∗"):
                dropping = False
            continue
        out.append(line)
    if not inserted:
        for index, line in enumerate(out):
            if line.strip().endswith(":"):
                out[index + 1:index + 1] = CODE_PREMISES
                break
    return out


def statement_without(lines: list[str], exit_address: str) -> list[str]:
    """The lemma statement with the premise that supplies the exit dropped.

    A segment names its exit as a premise, `instr_body EXIT (spec …)`. The
    inference is what the automation holds when it asks for that premise,
    so the premise has to go.
    """
    out, dropping = [], False
    for line in lines:
        if exit_address in line and ("instr_body" in line or "instr_pre" in line):
            dropping = True
            continue
        if dropping:
            # The premise continues while the line is indented and has not
            # yet closed with the separating wand of the next premise.
            if line.strip().endswith("-∗"):
                dropping = False
            continue
        out.append(line)
    return out


TRACE_NAME = "zesuInferredTrace"
SHELVE_TERM_GOALS = """all: try (lazymatch goal with
  | |- ?goal =>
      lazymatch type of goal with
      | Prop => fail
      | _ => shelve
      end
  end)."""


def with_inferred_trace(spec: dict) -> tuple[list[str], str, list[str], list[str]]:
    """Turn the segment's trace into a Coq evar the automation fills in.

    A block that calls out has to show its events are included in the
    trace the boundary declares. When the boundary declares a bare
    variable the inclusion carries no information, and when it declares
    a folded project definition no reduction reaches the write at its
    head. Either way the block stops, and the answer is not a rule: it
    is that the boundary should have named the events the block emits.

    So the probe stops declaring them. It states the trace as an
    existential, `eexists` makes it an evar, and every inclusion the
    block raises is then closed by `reflexivity`, which instantiates the
    evar with exactly the events emitted so far. What the evar holds at
    the exit is the trace the boundary should state.

    Returns the binders, the spec with the trace replaced, and the
    prologue and epilogue lines of the statement.
    """
    target = spec.get("infer_trace")
    if not target:
        return [spec["binders"]], spec["spec"], [], []
    binders = spec["binders"]
    for shape in (f"({target} : spec)", f"({target} : spec) "):
        binders = binders.replace(shape, "")
    body = spec["spec"].replace(target, TRACE_NAME)
    return ([binders.strip()], body,
            [f"  ∃ {TRACE_NAME} : spec,", "  ⊢ ("], ["  )."])


def spec_source(spec: dict, rule: str = "",
                alternatives: tuple[str, ...] = ()) -> str:
    """A probe for a segment that has no module yet.

    An open segment is described by its entry address and the predicate
    that holds there, both of which its interface already names. The
    probe states `instr_body ENTRY (predicate)` with the standard code
    premise and nothing else, and runs the automation: where it stops is
    the segment's first debt.
    """
    # One persistent premise per call the range makes, so the block never
    # steps into a callee and asks for an instruction the index does not
    # hold. The targets come from the disassembly, the contracts from the
    # closed B2/B4 list.
    calls, call_modules, unknown = call_premises(int(spec["entry"], 16),
                                                 int(spec["exit"], 16))
    imports = [f"Require Import {name}."
               for name in list(spec["imports"]) + call_modules]
    binders, body, opening, closing = with_inferred_trace(spec)
    statement = ([f"Lemma infer_boundary {binders[0]} :"] + opening
                 + CODE_PREMISES + calls
                 + [f"  instr_body {spec['entry']}",
                    f"    ({body})" + ("" if closing else ".")]
                 + closing)
    preamble: list[str] = []
    block = "zesu_block"
    if rule or alternatives:
        block = "zesu_block_timed"
        module = PROOF_DIR / spec["like"]
        preamble = (timed.requires(module) + rule.split("\n")
                    + timed.timed_tactics(module, labels=False,
                                          extra_alternatives=alternatives
                                          ).split("\n"))
    body = [f'idtac "{probes.BEGIN}".', "try intros.",
            "try eexists." if spec.get("infer_trace") else "idtac.",
            f"try {block}.",
            "all: try liShow.",
            # `unshelve` brings the search's own term evars to the front,
            # and a probe that prints one of those has reported nothing.
            # Shelve anything that is not a proposition, so `Show` prints
            # the goal the automation actually stopped on.
            f'all: idtac "{RAW_BEGIN}".', "Show.", f'all: idtac "{RAW_END}".',
            SHELVE_TERM_GOALS,
            "Show.", "Abort."]
    return "\n".join(
        ["Set Printing Width 200.", "Require Import isla.isla.",
         "From iris.proofmode Require Import environments.",
         "From IslaTraces.write_success_blocks Require Import Index."]
        + imports + preamble + statement + ["Proof."] + body
        + probes.END_MARKER + [""])


def probe_source(module: Path, lemma: str, exit_address: str,
                 driver: list[str], rule: str = "",
                 alternatives: tuple[str, ...] = (),
                 extra_imports: tuple[str, ...] = ()) -> str:
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    statement = with_standard_code(statement_without(
        lines[proof.declaration_line:proof.proof_line], exit_address))
    statement = [line.replace(lemma, "infer_boundary") for line in statement]
    normalized = str(int(exit_address, 16))
    block = "zesu_block"
    preamble: list[str] = []
    if rule or alternatives:
        # The candidate rule and a copy of the search list that calls it,
        # both local to this probe: nothing is installed into the
        # automation until a probe says the rule is affordable.
        block = "zesu_block_timed"
        preamble = (timed.requires(module) + rule.split("\n")
                    + timed.timed_tactics(module, labels=False,
                                          extra_alternatives=alternatives
                                          ).split("\n"))
    body = [f'idtac "{probes.BEGIN}".', "try intros.", f"try {block}."]
    body += driver
    body += [
        # Arriving at the exit shows as the goal asking for the instruction
        # or the precondition at that address.
        f'''all: try (lazymatch goal with
         | |- envs_entails _ (instr_pre {normalized} _) => idtac "{REACHED}"
         | |- envs_entails _ (instr_body {normalized} _) => idtac "{REACHED}"
         | |- context [instr_pre {normalized}] => idtac "{REACHED}"
         end).''',
        "all: try liShow.",
        f'all: idtac "{RAW_BEGIN}".', "Show.", f'all: idtac "{RAW_END}".',
        SHELVE_TERM_GOALS, "Show.", "Abort."]
    source = (["Set Printing Width 200.", "Require Import isla.isla.",
               "From iris.proofmode Require Import environments.",
               "From IslaTraces.write_success_blocks Require Import Index."]
              + lines[:proof.declaration_line]
              + [f"Require Import {name}." for name in extra_imports]
              + preamble + statement
              + ["Proof."]
              + body + probes.END_MARKER
              + [f"End {name}." for name in reversed(proof.open_blocks)] + [""])
    return "\n".join(source)


def run(source: str, name: str, build_dir: Path, seconds: int) -> str:
    directory = build_dir / "det" / "boundary"
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.v"
    path.write_text(source)
    environment = dict(os.environ)
    environment["ZESU_COQC_SECONDS"] = str(seconds)
    done = subprocess.run(
        ["timeout", str(seconds + 60), "nice", "-n", "10", "bash",
         str(SCRATCH), str(path), str(build_dir)],
        capture_output=True, text=True, env=environment)
    return done.stdout + "\n" + done.stderr


def goal_record(text: str) -> tuple[str, dict]:
    """Keep all goals before shelving, then select the Prop residual."""
    all_goals = text
    selected = text
    if RAW_BEGIN in text and RAW_END in text:
        before, rest = text.split(RAW_BEGIN, 1)
        all_goals, after = rest.rsplit(RAW_END, 1)
        all_goals = all_goals.replace(RAW_BEGIN, "").replace(RAW_END, "")
        selected = before + after
    return selected, {
        "raw_goals": text,
        "goals": [{"context": context, "conclusion": conclusion}
                  for context, conclusion in map(split_goal, split_goals(all_goals))],
    }


def infer(module: Path, lemma: str, exit_address: str, build_dir: Path,
          driver: list[str], seconds: int, rule: str = "",
          alternatives: tuple[str, ...] = (),
          extra_imports: tuple[str, ...] = ()) -> dict:
    started = time.monotonic()
    output = run(probe_source(module, lemma, exit_address, driver, rule,
                              alternatives, extra_imports),
                 f"{module.stem}__{lemma}", build_dir, seconds)
    text, details = goal_record(probes.marked(output))
    record = {**details, "module": module.name, "lemma": lemma, "exit": exit_address,
              "seconds": round(time.monotonic() - started, 1),
              "driver_lines": len(driver)}
    if probes.END not in output:
        record["outcome"] = "error"
        record["error_lines"] = [line for line in output.split("\n")
                                 if line.strip().startswith("Error")][:4]
        return record
    context, conclusion = conclusion_text(text)
    frame, points = context_size(context)
    record.update({"frame": frame, "mapsto": points,
                   "context": context, "conclusion": conclusion})
    if REACHED in output:
        record["outcome"] = "reached"
        return record
    record["outcome"] = "stalled"
    record["pred_class"] = classify(text, "residual").pred_class
    record["signature"] = signature(conclusion)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", type=Path, default=None,
                        help="one MODULE:LEMMA:EXIT per line")
    parser.add_argument("--specs", type=Path, default=None,
                        help="a JSON list of open-segment descriptions")
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"))
    parser.add_argument("--drivers", type=Path, default=None,
                        help="directory of <lemma>.tac driver files")
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--rule", type=Path, default=None,
                        help="a candidate rule to compile into the probe")
    parser.add_argument("--alt", action="append", default=[],
                        help="a tactic to append to the probe's search list")
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()
    records = []
    for spec in (json.loads(arguments.specs.read_text())
                 if arguments.specs else []):
        started = time.monotonic()
        output = run(spec_source(spec,
                                 arguments.rule.read_text()
                                 if arguments.rule else "",
                                 tuple(arguments.alt)),
                     spec["name"], arguments.build_dir, arguments.seconds)
        record = {"lemma": spec["name"], "entry": spec["entry"],
                  "exit": spec["exit"],
                  "call_premises": len(call_premises(
                      int(spec["entry"], 16), int(spec["exit"], 16))[0]),
                  "seconds": round(time.monotonic() - started, 1)}
        text, details = goal_record(probes.marked(output))
        record.update(details)
        if probes.END not in output:
            record["outcome"] = "error"
            record["error_lines"] = [line for line in output.split("\n")
                                     if line.strip().startswith("Error")][:4]
        else:
            context, conclusion = conclusion_text(text)
            frame, points = context_size(context)
            record.update({"outcome": "stalled", "frame": frame,
                           "mapsto": points, "context": context,
                           "conclusion": conclusion,
                           "pred_class": classify(text, "residual").pred_class,
                           "signature": signature(conclusion)})
        records.append(record)
        print(f"{record['outcome']:8s} {record['seconds']:7.1f}s "
              f"frame {record.get('frame', 0):3d}  "
              f"{record.get('pred_class', ''):<8} "
              f"{record.get('signature', (record.get('error_lines') or [''])[0])[:44]}"
              f"  {spec['name']}", flush=True)
    for line in ((arguments.set.read_text().split("\n"))
                 if arguments.set else []):
        if line.count(":") < 2:
            continue
        name, lemma, exit_address = line.split(":", 2)
        path = Path(name)
        if not path.exists():
            path = PROOF_DIR / path.name
        driver: list[str] = []
        if arguments.drivers:
            candidate = arguments.drivers / f"{lemma}.tac"
            if candidate.exists():
                driver = [row for row in candidate.read_text().split("\n")
                          if row.strip()]
        record = infer(path, lemma, exit_address.strip(),
                       arguments.build_dir, driver, arguments.seconds,
                       arguments.rule.read_text() if arguments.rule else "",
                       tuple(arguments.alt))
        records.append(record)
        print(f"{record['outcome']:8s} {record['seconds']:7.1f}s "
              f"frame {record.get('frame', 0):3d}  "
              f"{record.get('signature', record.get('error_lines', [''])[0] if record.get('error_lines') else '')[:60]}"
              f"  {lemma}", flush=True)
    arguments.out.parent.mkdir(parents=True, exist_ok=True)
    arguments.out.write_text("".join(json.dumps(r) + "\n" for r in records))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
