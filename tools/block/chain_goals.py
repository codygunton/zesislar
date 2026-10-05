"""Record each native goal with its own context and captured widths."""
from __future__ import annotations

import re

from chain_widths import PRINT_MEMORY_WIDTHS, WIDTH_MARKER, TRACE_WIDTH_MARKER, ADDRESS_WIDTH_MARKER, captured_widths

BEGIN = "CHAIN-GOAL-BEGIN"
END = "CHAIN-GOAL-END"
LOCAL = "CHAIN-GOAL-LOCAL"
SORT = "CHAIN-GOAL-SORT"
VALUE = "CHAIN-GOAL-VALUE"
PERSISTENT = "CHAIN-GOAL-PERSISTENT"
SPATIAL = "CHAIN-GOAL-SPATIAL"
CONCLUSION = "CHAIN-GOAL-CONCLUSION"
ENV = "CHAIN-GOAL-ENV"

# The environment traversal preserves both Iris contexts without selecting
# or consuming any resource. Each field has its own terminator.
RECORDER = r'''Ltac chain_print_environment marker environment :=
  lazymatch environment with
  | environments.Enil => idtac
  | environments.Esnoc ?rest ?name ?resource =>
      chain_print_environment marker rest;
      idtac marker resource "CHAIN-FIELD-END"
  end.
Ltac chain_print_goal phase :=
  idtac "CHAIN-GOAL-BEGIN" phase;
  try (multimatch goal with
    | Hlocal : ?T |- _ =>
      idtac "CHAIN-GOAL-LOCAL" Hlocal ":" T "CHAIN-FIELD-END";
      let S := type of T in
      idtac "CHAIN-GOAL-SORT" Hlocal ":" S "CHAIN-FIELD-END";
      try (lazymatch goal with
        | Hlocal := ?value : _ |- _ =>
          idtac "CHAIN-GOAL-VALUE" Hlocal ":" value "CHAIN-FIELD-END"
        end);
      fail
    end);
  lazymatch goal with
  | |- envs_entails ?environment ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "iris" "CHAIN-FIELD-END";
      let persistent := eval cbv [environments.env_intuitionistic] in
        (environments.env_intuitionistic environment) in
      let spatial := eval cbv [environments.env_spatial] in
        (environments.env_spatial environment) in
      chain_print_environment "CHAIN-GOAL-PERSISTENT" persistent;
      chain_print_environment "CHAIN-GOAL-SPATIAL" spatial;
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  | |- ?conclusion =>
      idtac "CHAIN-GOAL-ENV" "coq" "CHAIN-FIELD-END";
      idtac "CHAIN-GOAL-CONCLUSION" conclusion "CHAIN-FIELD-END"
  end.
'''


def recording(phase: str) -> str:
    if phase not in {"active", "shelved"}:
        raise ValueError("invalid goal phase")
    widths = PRINT_MEMORY_WIDTHS.removeprefix("all: ").removesuffix(".")
    return (f'Ltac chain_record_{phase} := lazymatch goal with |- ?G => chain_print_goal "{phase}"; {widths}; '
            f'idtac "CHAIN-GOAL-END" end.\nall: chain_record_{phase}.')


def parse_goals(output: str, *, phase: str | None = None,
                allow_local_definitions: bool = False) -> list[dict]:
    """Reject incomplete records instead of recovering an empty context."""
    result = []
    starts = list(re.finditer(r'CHAIN-GOAL-BEGIN\s+"?(active|shelved)"?\b', output))
    if BEGIN in output and not starts:
        raise ValueError("invalid native goal phase")
    for index, start in enumerate(starts):
        limit = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        end = output.find(END, start.end(), limit)
        if end < 0:
            raise ValueError("incomplete native goal record")
        body = output[start.end():end]
        fields = re.findall(r'"?(CHAIN-GOAL-[A-Z]+)"?\s+(.*?)\s*CHAIN-FIELD-END', body, re.S)
        record = {"phase": start.group(1), "coq": [], "persistent": [],
                  "spatial": [], "local_sorts": {}, "local_values": {}}
        conclusion, environment = [], []
        for marker, value in fields:
            value = value.strip()
            if "CHAIN-GOAL-" in value:
                raise ValueError("unterminated native goal field")
            if marker in {LOCAL, SORT, VALUE}:
                name, separator, term = value.partition(":")
                if not separator or not name.strip() or not term.strip():
                    raise ValueError("invalid native local record")
                name, term = name.strip(), term.strip()
                if marker == LOCAL:
                    record["coq"].append([name, term])
                elif marker == SORT:
                    record["local_sorts"][name] = "Prop" if term == "Prop" else "Type"
                else:
                    record["local_values"][name] = term
            elif marker == PERSISTENT:
                record["persistent"].append(value)
            elif marker == SPATIAL:
                record["spatial"].append(value)
            elif marker == CONCLUSION:
                conclusion.append(value)
            elif marker == ENV:
                environment.append(value)
        if len(conclusion) != 1 or environment not in [["iris"], ["coq"]]:
            raise ValueError("missing native goal context or conclusion")
        if any(name not in record["local_sorts"] for name, _ in record["coq"]):
            raise ValueError("missing native local sort")
        if record["local_values"] and not allow_local_definitions:
            raise ValueError("unresolved native local definitions")
        record["coq"].reverse()
        record.update(conclusion=conclusion[0], environment=environment[0],
                      memory_word_widths=captured_widths(body, WIDTH_MARKER),
                      trace_value_widths=captured_widths(body, TRACE_WIDTH_MARKER),
                      address_widths=captured_widths(body, ADDRESS_WIDTH_MARKER),
                      raw_goal=body)
        context = [f"{name} := {record['local_values'][name]} : {term}"
                   if name in record['local_values'] else f"{name} : {term}"
                   for name, term in record["coq"]]
        context.append("============================")
        context.extend(f"_ : {term}" for term in record["persistent"])
        context.append("--------------------------------------□")
        context.extend(f"_ : {term}" for term in record["spatial"])
        record["context"] = "\n".join(context)
        if phase is None or record["phase"] == phase:
            result.append(record)
    return result
