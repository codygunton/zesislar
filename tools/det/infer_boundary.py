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
import gen_boundary  # noqa: E402
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
SORT_BEGIN = "BOUNDARY-LOCAL-SORTS-BEGIN"
SORT_END = "BOUNDARY-LOCAL-SORTS-END"
SORT_MARKER = "BOUNDARY-LOCAL-SORT"
REG_BEGIN = "BOUNDARY-REGISTERS-BEGIN"
REG_VALUE = "BOUNDARY-REGISTERS-VALUE"
REG_END = "BOUNDARY-REGISTERS-END"
VALUE_BEGIN = "BOUNDARY-VALUE-BEGIN"
VALUE_TERM = "BOUNDARY-VALUE-TERM"
VALUE_TYPE = "BOUNDARY-VALUE-TYPE"
VALUE_END = "BOUNDARY-VALUE-END"
PARAM_BEGIN = "BOUNDARY-PARAMETERS-BEGIN"
PARAM_END = "BOUNDARY-PARAMETERS-END"
PRINT_PARAMETERS = [f'idtac "{PARAM_BEGIN}".', 'Show.', f'idtac "{PARAM_END}".']
PRINT_TYPED_VALUES = f'''all: try (iMatchHyp ltac:(fun Hvalue body =>
  lazymatch body with
  | (_ ↦ᵣ RVal_Bits (@bv_to_bvn ?width ?bits))%I =>
      let kind := type of bits in
      idtac "{VALUE_BEGIN}" body "{VALUE_TERM}" bits "{VALUE_TYPE}" kind "{VALUE_END}"
  | (_ ↦ₘ ?bits)%I =>
      let kind := type of bits in
      idtac "{VALUE_BEGIN}" body "{VALUE_TERM}" bits "{VALUE_TYPE}" kind "{VALUE_END}"
  | instr_pre (@bv_unsigned ?width ?bits) _ =>
      let kind := type of bits in
      idtac "{VALUE_BEGIN}" body "{VALUE_TERM}" bits "{VALUE_TYPE}" kind "{VALUE_END}"
  end; fail)).'''
PRINT_REGISTERS = f'''all: try (iMatchHyp ltac:(fun Hreg body =>
  lazymatch body with reg_col ?regs =>
    tryif constr_eq regs zesu_ram_sys_regs then fail else
      let values := eval cbv in regs in
      idtac "{REG_BEGIN}" regs "{REG_VALUE}" values "{REG_END}"
  end; fail)).'''
PRINT_LOCAL_SORTS = f'''all: (idtac "{SORT_BEGIN}";
  try (multimatch goal with Hlocal : ?T |- _ =>
    let S := type of T in idtac "{SORT_MARKER}" Hlocal ":" S; fail
  end);
  idtac "{SORT_END}").'''
EXPOSE_RESOURCES = '''all: repeat first
  [ progress (iMatchHyp ltac:(fun Hresource body =>
      lazymatch body with (∃ _, _)%I => iDestruct Hresource as (?) Hresource end))
  | progress (iMatchHyp ltac:(fun Hresource body =>
      lazymatch body with (_ ∗ _)%I => iDestruct Hresource as "[? ?]" end))
  | progress (iMatchHyp ltac:(fun Hresource body =>
      lazymatch body with
      | reg_col _ => fail
      | spec_trace _ => fail
      | mmio_range _ _ => fail
      | instr_pre _ _ => fail
      | instr_body _ _ => fail
      | _ =>
          first
            [ let head := get_head body in
              let instance := constr:(_ : LithiumUnfold head) in
              iEval (progress unfold head; cbv beta zeta) in Hresource
            | let instance := constr:(_ : ZesuSealed body _ _ _) in
              iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance))) in Hresource
            | let instance := constr:(_ : ZesuSealedOpaqueTail body _) in
              iEval (rewrite (zesu_sealed_opaque_unfold
                       (ZesuSealedOpaqueTail := instance))) in Hresource ]
      end)) ].'''


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
                         r"instr_lookup_resources|instr_body_lookup_resources|spec_instr_resources")


def with_standard_code(lines: list[str]) -> list[str]:
    """Replace whatever code premise the lemma has with the standard pair."""
    out, dropping, inserted = [], False, False
    for line in lines:
        if CODE_BUNDLE.search(line) and not re.search(r'\binstr_body\s', line):
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
            dropping = not line.rstrip().endswith("-∗")
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
SELECT_MACHINE_GOALS = """all: try (lazymatch goal with
  | |- envs_entails _ _ => fail
  | _ => shelve
  end)."""


def stop_name(address: str) -> str:
    return f"BLK_STOP_{int(address, 16):x}"


def reached_stop(output: str, address: str | None) -> bool:
    return (bool(re.search(rf'{REACHED}\s+{stop_name(address)}\b', output))
            if address else REACHED in output)


def with_call_premises(lines: list[str], stop: str) -> tuple[list[str], list[str]]:
    """Add each closed callee contract in the complete probe range."""
    bodies = list(re.finditer(r"\binstr_body\s+(0x[0-9a-fA-F]+)\b", "\n".join(lines)))
    if not bodies:
        raise ValueError("the entry instruction address is not a literal")
    entry = int(bodies[-1].group(1), 16)
    calls, modules, _unknown = call_premises(entry, int(stop, 16), strict=True)
    # Interfaces defines this alias as @zesuMemcpyCallSpec Sigma _ _.
    # Import the defining module directly to keep probes independent of
    # the large umbrella module. The contract itself remains unchanged.
    aliases = {'memcpyEntryBoundary': 'zesuMemcpyCallSpec',
               'writeOutputEntryBoundary': 'writeOutputExactCallSpec'}
    calls = list(calls)
    statement = " ".join(lines)
    for alias, definition in aliases.items():
        calls = [call.replace(alias, definition) for call in calls]
        statement = statement.replace(alias, definition)
    missing = [call for call in calls if not re.search(
        r"□\s+instr_pre\s+" + re.escape(call.split()[2]) + r"\s+"
        + re.escape(call.split()[3]) + r"\s*-∗", statement)]
    # Retain the selected lemma's callee as the nearest matching premise.
    # The strict table contract remains available for each called target.
    position = next((index for index, line in enumerate(lines)
                     if 'instr_lookup_resources' in line),
                    max(index for index, line in enumerate(lines) if 'instr_body' in line))
    direct = {'zesuMemcpyCallSpec': 'ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls',
              'writeOutputExactCallSpec':
              'ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWriteOutputCall'}
    if missing and all(call.split()[3] in direct for call in missing):
        modules = list(dict.fromkeys(direct[call.split()[3]] for call in missing))
    return lines[:position] + missing + lines[position:], modules if missing else []


def stop_statement(lines: list[str], address: str) -> list[str]:
    """Bind an abstract successor and retain its guarded instruction premise."""
    lines = statement_without(lines, address)
    name = stop_name(address)
    for index, line in enumerate(lines):
        if line.rstrip().endswith(":"):
            lines[index] = line.rstrip()[:-1] + f" ({name} : iProp Sigma) :"
            position = next((row for row in range(index + 1, len(lines))
                             if "instr_lookup_resources" in lines[row]), index + 1)
            lines[position:position] = [
                f"  instr_pre {hex(int(address, 16))} {name} -∗"]
            return lines
    raise ValueError("the lemma declaration has no binder boundary")


def stop_recording(address: str | None, after_return: bool) -> list[str]:
    """Enter the returned continuation before reading its caller frame."""
    lines = []
    if after_return:
        lines += ["all: try zesu_enter_return_bundle_if_enabled.",
                  "all: try zesu_enter_return_wand_if_enabled."]
    if address:
        lines += [f'''all: try (lazymatch goal with
  | |- envs_entails _ ?target => is_var target; idtac "{REACHED}" target
  end).''']
    return lines


def return_imports(after_return: bool) -> list[str]:
    return (["Require Import ZesuSsz.Automation.ReturnBundle.",
             "Require Import ZesuSsz.Automation.ReturnWand.",
             "Require Import ZesuSsz.Automation.Switches.ReturnBundle.",
             "Require Import ZesuSsz.Automation.Switches.ReturnWand."]
            if after_return else [])


def opaque_probe_prefix(lines: list[str]) -> list[str]:
    """Keep copied native unfold instances from comparing predicate bodies."""
    heads = dict.fromkeys(re.findall(r'LithiumUnfold\s*\(@([\w.]+)\)', '\n'.join(lines)))
    return lines + [f'#[local] Typeclasses Opaque {head}.' for head in heads]


def expose_before_stop(statement: list[str], stop: str, run_tactic: str) -> list[str]:
    """Expose the input, then remove native handoffs inside the probe range."""
    entry = re.findall(r'\binstr_body\s+(0x[\da-fA-F]+)\b', '\n'.join(statement))[-1]
    # A selected native lemma can carry a different closed contract for
    # the same target. Keep both in the statement, but infer its native
    # state with its own callee. Generated blocks still use the table.
    native_output = any('instr_pre 0x10190 zesuWriteOutputCallSpec' in line
                        for line in statement)
    select_native = (['''all: try (iMatchHyp ltac:(fun Hcallee body =>
  lazymatch body with instr_pre 0x10190 writeOutputExactCallSpec => iClear Hcallee end)).''']
                     if native_output else [])
    return ['iStartProof.',
            'repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].',
            'all: repeat (lazymatch goal with |- envs_entails _ (WPasm _) => fail | _ => liAStep end).',
            'all: try liShow.',
            EXPOSE_RESOURCES, *select_native,
            f'''all: repeat (iMatchHyp ltac:(fun Hnext body =>
  lazymatch body with instr_pre ?pc ?resources =>
    let inside := eval vm_compute in (Z.leb {int(entry, 16)} pc && Z.leb pc {int(stop, 16)})%bool in
    constr_eq inside true;
    tryif is_var resources then fail else iClear Hnext
  end)).''',
            # Keep the machine boundary if a later pure solver times out.
            # The shelved obligations remain in the measurement record.
            'all: repeat liAStep.', f'all: try {run_tactic}.']


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
                alternatives: tuple[str, ...] = (), *,
                stop: str | None = None, after_return: bool = False) -> str:
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
                                                 int(stop or spec["exit"], 16), strict=True)
    imports = [f"Require Import {name}."
               for name in list(spec["imports"]) + call_modules]
    binders, body, opening, closing = with_inferred_trace(spec)
    statement = ([f"Lemma infer_boundary {binders[0]} :"] + opening
                 + CODE_PREMISES + calls
                 + [f"  instr_body {spec['entry']}",
                    f"    ({body})" + ("" if closing else ".")]
                 + closing)
    if stop:
        statement = stop_statement(statement, stop)
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
            *stop_recording(stop, after_return),
            "all: try liShow.",
            # `unshelve` brings the search's own term evars to the front,
            # and a probe that prints one of those has reported nothing.
            # Shelve anything that is not a proposition, so `Show` prints
            # the goal the automation actually stopped on.
            f'all: idtac "{RAW_BEGIN}".', "Show.", f'all: idtac "{RAW_END}".',
            SHELVE_TERM_GOALS, SELECT_MACHINE_GOALS, PRINT_REGISTERS,
            PRINT_LOCAL_SORTS,
            "Show.", "Abort."]
    return "\n".join(
        ["Set Printing Width 200.", "Set Printing Depth 10000.", "Set Printing Coercions.", "Require Import isla.isla.",
         "From iris.proofmode Require Import environments.",
         "From IslaTraces.write_success_blocks Require Import Index."]
        + imports + return_imports(after_return) + preamble + statement + ["Proof."] + body
        + probes.END_MARKER + [""])


def probe_source(module: Path, lemma: str, exit_address: str,
                 driver: list[str], rule: str = "",
                 alternatives: tuple[str, ...] = (),
                 extra_imports: tuple[str, ...] = (), *,
                 stop: str | None = None, after_return: bool = False,
                 entry_state: tuple[str, str] | None = None) -> str:
    proof = find_proof(module, lemma)
    lines = module.read_text().split("\n")
    statement = with_standard_code(statement_without(
        lines[proof.declaration_line:proof.proof_line], exit_address))
    statement = [line.replace(lemma, "infer_boundary") for line in statement]
    if entry_state is not None:
        text = '\n'.join(statement)
        entry = list(re.finditer(r'\binstr_body\s+0x[\da-fA-F]+\b', text))[-1]
        statement = (text[:entry.end()] + f' ({entry_state[1]}).').splitlines()
    statement, call_modules = with_call_premises(statement, stop or exit_address)
    if stop:
        statement = stop_statement(statement, stop)
    normalized = str(int(stop or exit_address, 16))
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
    body = [f'idtac "{probes.BEGIN}".', "try intros.", *PRINT_PARAMETERS]
    body += (expose_before_stop(statement, stop, 'zesu_run_timed' if rule or alternatives
                               else 'zesu_run') if stop else [f'try {block}.'])
    body += driver
    body += stop_recording(stop, after_return)
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
        SHELVE_TERM_GOALS, SELECT_MACHINE_GOALS, PRINT_REGISTERS, PRINT_TYPED_VALUES,
        PRINT_LOCAL_SORTS, "Show.", "Abort."]
    source = (["Set Printing Width 200.", "Set Printing Depth 10000.", "Set Printing Coercions.", "Require Import isla.isla.",
               "From iris.proofmode Require Import environments.",
               "Require Import ZesuSsz.Automation.ReturnBundle.",
               "Require Import ZesuSsz.Automation.SealedCoverage.",
               "From IslaTraces.write_success_blocks Require Import Index."]
              + ([entry_state[0]] if entry_state is not None else [])
              + opaque_probe_prefix(lines[:proof.declaration_line])
              + [f"Require Import {name}." for name in extra_imports]
              + [f"Require Import {name}." for name in call_modules]
              + return_imports(after_return)
              + preamble + statement
              + ["Proof."]
              + body + probes.END_MARKER
              + [f"End {name}." for name in reversed(proof.open_blocks)] + [""])
    return "\n".join(source)


def entry_source(module: Path, lemma: str) -> tuple[str, str]:
    """Expose the selected lemma's literal entry resources without execution."""
    proof = find_proof(module, lemma)
    lines = module.read_text().splitlines()
    statement = lines[proof.declaration_line:proof.proof_line]
    literal = list(re.finditer(r'\binstr_body\s+(0x[\da-fA-F]+)\b', '\n'.join(statement)))
    if not literal:
        literal = list(re.finditer(r'\binstr_pre\s+(0x[\da-fA-F]+)\b', '\n'.join(statement)))
    if not literal:
        raise ValueError('the entry instruction address is not a literal')
    last = literal[-1]
    entry = hex(int(last.group(1), 16))
    predicate = '\n'.join(statement)[last.end():].strip().removesuffix('.')
    header = statement[:next(i for i, line in enumerate(statement)
                              if line.rstrip().endswith(':')) + 1]
    header = [line.replace(lemma, 'infer_boundary') for line in header]
    header[-1] = header[-1].rstrip()[:-1] + f' ({stop_name(entry)} : iProp Sigma) :'
    body = [f'idtac "{probes.BEGIN}".', 'try intros.', *PRINT_PARAMETERS, 'iStartProof.',
            'iIntros "ENTRY".', 'try zesu_open_return_bundle "ENTRY".',
            EXPOSE_RESOURCES,
            *stop_recording(entry, False), 'all: try liShow.',
            f'all: idtac "{RAW_BEGIN}".', 'Show.', f'all: idtac "{RAW_END}".',
            PRINT_REGISTERS, PRINT_TYPED_VALUES, PRINT_LOCAL_SORTS, 'Show.', 'Abort.']
    return '\n'.join(['Set Printing Width 200.', 'Set Printing Depth 10000.', 'Set Printing Coercions.', 'Require Import isla.isla.',
                       'From iris.proofmode Require Import environments.',
                       'Require Import ZesuSsz.Automation.ReturnBundle.',
                       'Require Import ZesuSsz.Automation.SealedCoverage.']
                      + opaque_probe_prefix(lines[:proof.declaration_line]) + header
                      + [f'  {predicate} -∗ {stop_name(entry)}.', 'Proof.']
                      + body + probes.END_MARKER
                      + [f'End {name}.' for name in reversed(proof.open_blocks)] + ['']), entry


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
    return done.stdout + "\n" + done.stderr + (
        f'\nprobe exit status={done.returncode}\n' if done.returncode else '')


def goal_record(text: str) -> tuple[str, dict]:
    """Keep all goals before shelving, then select the Prop residual."""
    all_goals = text
    selected = text
    if RAW_BEGIN in text and RAW_END in text:
        before, rest = text.split(RAW_BEGIN, 1)
        all_goals, after = rest.rsplit(RAW_END, 1)
        all_goals = all_goals.replace(RAW_BEGIN, "").replace(RAW_END, "")
        selected = before + after
    selected = re.sub(rf'{PARAM_BEGIN}.*?{PARAM_END}', '', selected, flags=re.S)
    return selected, {
        "raw_goals": text,
        "local_sorts": local_sorts(text),
        "parameter_types": dict(gen_boundary.sections(
            re.search(rf'{PARAM_BEGIN}(.*?){PARAM_END}', text, re.S)[1])[0])
            if PARAM_BEGIN in text and PARAM_END in text else {},
        "register_collections": [
            {"source": ' '.join(source.split()), "value": ' '.join(value.split())}
            for source, value in re.findall(
                rf'{REG_BEGIN}\s+(.*?)\s+{REG_VALUE}\s+(.*?)\s+{REG_END}', text, re.S)],
        "resource_values": [
            {"source": ' '.join(source.split()), "value": ' '.join(value.split()),
             "type": ' '.join(kind.split())}
            for source, value, kind in re.findall(
                rf'{VALUE_BEGIN}\s+(.*?)\s+{VALUE_TERM}\s+(.*?)\s+{VALUE_TYPE}\s+(.*?)\s+{VALUE_END}', text, re.S)],
        "goals": [{"context": context, "conclusion": conclusion}
                  for context, conclusion in map(split_goal, split_goals(all_goals))],
    }


def local_sorts(text: str) -> dict[str, str]:
    """Read the first selected goal's sorts from Rocq's own type query."""
    if SORT_BEGIN not in text or SORT_END not in text:
        return {}
    block = text.split(SORT_BEGIN, 1)[1].split(SORT_END, 1)[0]
    return {name: "Prop" if sort == "Prop" else "Type"
            for name, sort in re.findall(
                rf"{SORT_MARKER}\s+(\S+)\s*:\s*(Prop|Set|Type)\b", block)}


def native_imports(module: Path) -> list[str]:
    """Keep the defining modules visible when a state uses their constants."""
    imports = []
    for prefix, names in re.findall(
            r'(?m)^(?:From\s+([\w.]+)\s+)?Require\s+(?:Import|Export)\s+'
            r'([\w.\s]+?)\.(?=\s*(?:\n|$))', timed.strip_comments(module.read_text())):
        imports.extend((prefix + '.' if prefix else '') + name for name in names.split())
    return list(dict.fromkeys(imports))


def infer(module: Path, lemma: str, exit_address: str, build_dir: Path,
          driver: list[str], seconds: int, rule: str = "",
          alternatives: tuple[str, ...] = (),
          extra_imports: tuple[str, ...] = (), *,
          stop: str | None = None, after_return: bool = False,
          entry_only: bool = False,
          entry_state: tuple[str, str] | None = None) -> dict:
    started = time.monotonic()
    if entry_only:
        source, stop = entry_source(module, lemma)
    else:
        source = probe_source(module, lemma, exit_address, driver, rule,
                              alternatives, extra_imports, stop=stop,
                              after_return=after_return, entry_state=entry_state)
    output = run(source, f"{module.stem}__{lemma}" + ('__entry' if entry_only else ''),
                 build_dir, seconds)
    text, details = goal_record(probes.marked(output))
    record = {**details, "module": module.name, "lemma": lemma, "exit": exit_address,
              "seconds": round(time.monotonic() - started, 1),
              "driver_lines": len(driver)}
    proof = find_proof(module, lemma)
    header = []
    for line in module.read_text().splitlines()[proof.declaration_line:proof.proof_line]:
        header.append(line)
        if line.rstrip().endswith(":"):
            break
    declaration = " ".join(line.strip() for line in header).rstrip(":").strip()
    record["binders"] = re.sub(rf"^Lemma\s+{re.escape(lemma)}\b\s*", "", declaration)
    parts = module.with_suffix("").parts
    if "ZesuSsz" in parts:
        record["imports"] = [".".join(parts[parts.index("ZesuSsz"):]),
                             *native_imports(module), *extra_imports]
    if probes.END not in output:
        record["outcome"] = "error"
        record["error_lines"] = [line for line in output.split("\n")
                                 if line.strip().startswith(("Error", "proof limit exceeded",
                                                             "probe exit status="))][:4]
        return record
    if stop and 'No more goals.' in text and not reached_stop(output, stop):
        record['outcome'] = 'error'
        record['error_lines'] = ['the probe closed without a context at the requested stop']
        return record
    context, conclusion = conclusion_text(text)
    frame, points = context_size(context)
    record.update({"frame": frame, "mapsto": points,
                   "context": context, "conclusion": conclusion})
    if reached_stop(output, stop):
        if stop and conclusion.strip() != stop_name(stop):
            record['outcome'] = 'error'
            record['error_lines'] = ['the selected context does not conclude the requested stop']
            return record
        record["outcome"] = "reached"
        record["state_entry"] = hex(int(stop or exit_address, 16))
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
    parser.add_argument("--stop", default=None,
                        help="stop at ADDR with an abstract BLK_STOP successor")
    parser.add_argument("--after-return", action="store_true",
                        help="enter the return wand and open its bundle before recording")
    parser.add_argument("--entry-context", action="store_true",
                        help="expose the exact selected entry predicate without execution")
    arguments = parser.parse_args()
    records = []
    for spec in (json.loads(arguments.specs.read_text())
                 if arguments.specs else []):
        started = time.monotonic()
        output = run(spec_source(spec,
                                 arguments.rule.read_text()
                                 if arguments.rule else "",
                                 tuple(arguments.alt), stop=arguments.stop,
                                 after_return=arguments.after_return),
                     spec["name"], arguments.build_dir, arguments.seconds)
        record = {"lemma": spec["name"], "entry": spec["entry"],
                  "exit": spec["exit"],
                  "binders": spec["binders"], "imports": spec["imports"],
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
            record.update({"outcome": "reached" if reached_stop(output, arguments.stop) else "stalled", "frame": frame,
                           "mapsto": points, "context": context,
                           "conclusion": conclusion,
                           "pred_class": classify(text, "residual").pred_class,
                           "signature": signature(conclusion)})
            if record["outcome"] == "reached":
                record["state_entry"] = hex(int(arguments.stop or spec["exit"], 16))
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
                       tuple(arguments.alt), stop=arguments.stop,
                       after_return=arguments.after_return,
                       entry_only=arguments.entry_context)
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
