"""Check trace-cited diagnosis structure and terminal-verdict013 provenance."""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[2]
CITATION = re.compile(r"(?P<path>[^\s`|#]+TRACE\.json|TRACE\.json)#(?P<pointer>[^\s`|]*)")
MARKDOWN_LINK = re.compile(r"\[[^\]\n]+\]\((?P<target>[^()\s]+)\)")
CYCLE = re.compile(r"cycle\.([1-9][0-9]*)\.(refusal|reason|normalization|next_refusal)")
CYCLE_ROWS = ("refusal", "reason", "normalization", "next_refusal")
PLACEHOLDER = re.compile(r"(?:TODO|TBD|PENDING|PLACEHOLDER)(?:\b.*)?|<(?:fill|insert|cite|placeholder)[^>]*>", re.IGNORECASE)


@dataclass(frozen=True)
class Citation:
    path: str
    pointer: str


class DiagnosisError(ValueError):
    """A diagnosis or its cited JSON cannot be checked."""


def parse_citations(text: str):
    """Read bare citations and renderer links in their original order."""
    links = list(MARKDOWN_LINK.finditer(text))
    spans = []
    for link in links:
        citation = CITATION.fullmatch(link["target"])
        if citation is not None:
            spans.append((link.start(), link.end(), citation))
    for citation in CITATION.finditer(text):
        # An unfinished link must not become a bare local path.
        unfinished_link = re.search(r"\[[^\]\n]+\]\(", citation["path"])
        if unfinished_link is None and not any(
                link.start() <= citation.start() < link.end() for link in links):
            spans.append((citation.start(), citation.end(), citation))
    spans.sort(key=lambda span: span[0])
    citations, remaining, end = [], [], 0
    for start, stop, citation in spans:
        remaining.append(text[end:start])
        citations.append(Citation(citation["path"], citation["pointer"]))
        end = stop
    remaining.append(text[end:])
    return citations, "".join(remaining).replace("`", "").strip(" ,;")


def resolve_pointer(document, fragment: str):
    """Resolve an RFC 6901 URI fragment, without a TRACE schema."""
    value = document
    for token in pointer_tokens(fragment):
        if isinstance(value, dict):
            if token not in value:
                raise DiagnosisError(f"The JSON Pointer key does not exist: {token!r}.")
            value = value[token]
        elif isinstance(value, list):
            if not re.fullmatch(r"0|[1-9][0-9]*", token):
                raise DiagnosisError(f"The JSON Pointer array index is invalid: {token!r}.")
            try:
                index = int(token)
            except ValueError as error:
                raise DiagnosisError("The JSON Pointer array index is too large.") from error
            if index >= len(value):
                raise DiagnosisError(f"The JSON Pointer array index does not exist: {index}.")
            value = value[index]
        else:
            raise DiagnosisError("The JSON Pointer continues through a scalar value.")
    return value


def pointer_tokens(fragment: str) -> list[str]:
    """Decode pointer tokens through the same RFC rules as resolution."""
    if re.search(r"%(?![0-9a-fA-F]{2})", fragment):
        raise DiagnosisError("The JSON Pointer contains an invalid percent escape.")
    try:
        pointer = unquote(fragment, encoding="utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise DiagnosisError("The JSON Pointer contains invalid UTF-8.") from error
    if not pointer:
        return []
    if not pointer.startswith("/"):
        raise DiagnosisError("The JSON Pointer must be empty or start with '/'.")
    encoded = pointer[1:].split("/")
    if any(re.search(r"~(?![01])", token) for token in encoded):
        raise DiagnosisError("The JSON Pointer contains an invalid '~' escape.")
    return [token.replace("~1", "/").replace("~0", "~") for token in encoded]


def refusal_observation(document, fragment: str) -> dict:
    """Validate an exact refusal and its linked trial in the released trace schema."""
    if (not isinstance(document, dict) or type(document.get("schema_version")) is not int
            or document["schema_version"] != 1 or not isinstance(document.get("points"), list)):
        raise DiagnosisError("The trace does not have the agreed trace envelope.")
    tokens = pointer_tokens(fragment)
    if len(tokens) == 5 and tokens[0] == "points":
        prefix = "/points/" + tokens[1]
        tail = tokens[2:]
    elif len(tokens) == 4 and tokens[0] == "residual":
        prefix = "/residual"
        tail = tokens[1:]
    else:
        raise DiagnosisError("Cite a points/residual refusal message or exposed clause.")
    if tail[0] != "refusal" or tail[2] not in {"message", "clause"}:
        raise DiagnosisError("Cite a refusal message or exposed clause.")
    point = resolve_pointer(document, prefix)
    refusal = resolve_pointer(document, prefix + "/refusal/" + tail[1])
    required = {"trigger", "goal", "goal_nonotation", "hyps", "evars", "hint_log",
                "hand_call", "refusal", "current_goals", "shelf", "given_up", "completeness"}
    if not isinstance(point, dict) or not required.issubset(point):
        raise DiagnosisError("The cited point lacks required trace observations.")
    for name in ("hyps", "current_goals", "shelf", "given_up", "hand_call", "refusal"):
        if not isinstance(point[name], list):
            raise DiagnosisError(f"The cited point has an invalid {name} observation.")
    if any(not isinstance(point[name], str) for name in ("goal", "goal_nonotation")):
        if point["current_goals"] or point["goal"] is not None or point["goal_nonotation"] is not None:
            raise DiagnosisError("The cited point lacks both complete goal renderings.")
    completeness = point["completeness"]
    if (not isinstance(completeness, dict)
            or completeness.get("required_fields_complete") is not True
            or completeness.get("missing_observations") != []):
        raise DiagnosisError("The cited point marks required observations incomplete.")
    for name in ("evars", "hint_log"):
        if not isinstance(point[name], dict) or point[name].get("availability") != "complete":
            raise DiagnosisError(f"The cited point lacks a complete {name} observation.")
    if (not isinstance(refusal, dict) or not isinstance(refusal.get("message"), str)
            or not refusal["message"].strip()):
        raise DiagnosisError("The refusal lacks its exact message.")
    if refusal.get("exposure") not in {"exposed", "not-exposed"}:
        raise DiagnosisError("The refusal lacks its clause exposure status.")
    if refusal["exposure"] == "exposed" and not isinstance(refusal.get("clause"), str):
        raise DiagnosisError("The exposed refusal lacks its exact clause.")
    index = refusal.get("hand_call_index")
    calls = point["hand_call"]
    if type(index) is not int or not isinstance(calls, list) or not 0 <= index < len(calls):
        raise DiagnosisError("The refusal does not resolve to a recorded hand-call trial.")
    trial = calls[index]
    required_trial = {"before", "after_trial", "rollback", "rollback_equal", "command",
                      "clause", "feedback", "outcome"}
    if not isinstance(trial, dict) or not required_trial.issubset(trial):
        raise DiagnosisError("The linked hand-call trial lacks required observations.")
    if not isinstance(trial["command"], str) or not trial["command"].strip():
        raise DiagnosisError("The linked trial lacks the exact rule command.")
    if any(trial[name] is None for name in ("before", "after_trial", "rollback", "feedback")):
        raise DiagnosisError("The linked trial lacks a required snapshot or feedback.")
    if trial["outcome"] != "refused":
        raise DiagnosisError("The linked hand-call trial did not refuse.")
    if trial["clause"] != refusal.get("clause"):
        raise DiagnosisError("The refusal clause differs from its linked trial clause.")
    if trial["rollback_equal"] is not True:
        raise DiagnosisError("The linked trial does not establish exact rollback.")
    return {"point": point, "refusal": refusal, "trial": trial}


def resolve_citation(citation: Citation, root: Path, documents=None):
    """Load the declared local TRACE.json and resolve its pointer."""
    relative = Path(citation.path)
    if relative.name != "TRACE.json" or "://" in citation.path or "\x00" in citation.path:
        raise DiagnosisError("The citation must name a local TRACE.json file.")
    path = (root / relative).resolve()
    documents = {} if documents is None else documents
    if path not in documents:
        try:
            documents[path] = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, ValueError) as error:
            raise DiagnosisError(f"Cannot read the cited TRACE.json: {error}.") from error
    return resolve_pointer(documents[path], citation.pointer)


def split_cells(source: str):
    """Keep escaped Markdown pipes inside a cell."""
    content = source.strip()[1:]
    if content.endswith("|"):
        content = content[:-1]
    cells, cell, index = [], [], 0
    while index < len(content):
        pair = content[index:index + 2]
        if pair == '\\|':
            cell.append("|")
            index += 2
        elif pair == '\\\\':
            cell.append(pair)
            index += 2
        elif content[index] == "|":
            cells.append("".join(cell).strip())
            cell = []
            index += 1
        else:
            cell.append(content[index])
            index += 1
    cells.append("".join(cell).strip())
    return cells


def table_rows(text: str):
    """Read the fixed three-column diagnosis table."""
    rows = []
    for line, source in enumerate(text.splitlines(), 1):
        if not source.strip().startswith("|"):
            continue
        cells = split_cells(source)
        if cells == ["Row", "Evidence", "Trace citations"]:
            continue
        if all(re.fullmatch(r":?-+:?", cell) for cell in cells):
            continue
        if len(cells) != 3:
            raise DiagnosisError(f"Line {line}: the diagnosis table needs exactly three columns.")
        name, evidence, citations = cells
        rows.append((line, name.strip("`"), evidence, citations))
    return rows


STATE_FIELDS = ("goal", "goal_nonotation", "hyps", "evars", "current_goals", "shelf", "given_up")


def require(condition, message):
    if not condition:
        raise DiagnosisError(message)


def quoted_values(text):
    """Require verbatim quoted strings, with no inferred prose."""
    pattern = re.compile(r'`([^`]*)`|"(?:[^"\\]|\\.)*"')
    values, end = [], 0
    for match in pattern.finditer(text):
        require(not text[end:match.start()].strip(" ,;+"), "Use only verbatim quoted trace values.")
        values.append(match[1] if match[1] is not None else json.loads(match[0]))
        end = match.end()
    require(values and not text[end:].strip(" ,;+"), "Use only verbatim quoted trace values.")
    return values


def check_capture(record, session):
    require(isinstance(record, dict), "A cited capture is not an object.")
    require(record.get("session_id") == session, "A cited capture has a different logical session.")
    require(all(name in record for name in STATE_FIELDS), "A cited capture lacks required state observations.")
    complete = record.get("completeness", {})
    require(complete.get("required_fields_complete") is True
            and complete.get("missing_observations") == [], "A cited capture is incomplete.")
    require(isinstance(record["evars"], dict) and record["evars"].get("availability") == "complete", "A cited evar map is unavailable.")
    for name in ("hyps", "current_goals", "shelf", "given_up"):
        require(isinstance(record[name], list), f"The capture lacks its {name} list.")
    require(all(isinstance(record[name], str) for name in ("goal", "goal_nonotation"))
            or (not record["current_goals"] and record["goal"] is None
                and record["goal_nonotation"] is None), "The capture lacks both complete goal renderings.")


def snapshot(document, reference, session):
    require(isinstance(reference, str) and reference.startswith("#/snapshots/"),
            "A command state must cite an internal snapshots pointer.")
    tokens = pointer_tokens(reference[1:])
    require(len(tokens) == 2 and tokens[1], "A snapshot pointer must name one exact snapshot.")
    value = resolve_pointer(document, reference[1:])
    check_capture(value, session)
    return value


def same_state(left, right):
    return all(left[key] == right[key] for key in STATE_FIELDS)


def command_observation(document, tokens, session):
    require((len(tokens) == 7 and tokens[0] == "points" and tokens[2] == "hand_call"
             and tokens[4] == "commands")
            or (len(tokens) == 6 and tokens[0] == "residual" and tokens[1] == "hand_call"
                and tokens[3] == "commands"), "Cite an exact recorded hand-call command field.")
    pointer = "/" + "/".join(tokens[:-1])
    command = resolve_pointer(document, pointer)
    trial_tokens = tokens[:-3]
    trial = resolve_pointer(document, "/" + "/".join(trial_tokens))
    require(isinstance(command, dict) and command.get("outcome") in {"accepted", "refused"},
            "The command lacks an observed outcome.")
    require(isinstance(command.get("command"), str) and command["command"], "The command text is absent.")
    require((command["outcome"] == "accepted" and command.get("refusal") is None)
            or (command["outcome"] == "refused" and isinstance(command.get("refusal"), str)),
            "The command outcome conflicts with its refusal record.")
    before = snapshot(document, command.get("before"), session)
    after = snapshot(document, command.get("after"), session)
    return command, trial, before, after


def semantic_violations(rows, documents, base):
    """Check the released terminal-verdict013 provenance contract."""
    try:
        require(len(documents) == 1, "A completed diagnosis must use one exact TRACE.json bundle.")
        document = next(iter(documents.values()))
        require(isinstance(document, dict) and type(document.get("schema_version")) is int
                and document.get("schema_version") == 1, "The trace schema version is unsupported.")
        session = document["session"]["id"]
        require(isinstance(session, str) and session, "The stable logical session identity is absent.")
        completion = document["completion"]
        require(isinstance(completion, dict) and completion.get("trace_complete") is True
                and completion.get("reasons") == [],
                "The trace does not establish complete required observations.")
        coverage = document["coverage"]
        require(isinstance(coverage, dict) and coverage.get("required_complete") is True
                and coverage.get("missing_event_ids") == [] and coverage.get("unobserved_regions") == [],
                "The trace does not establish complete traversal coverage.")
        points = document["points"]
        require(isinstance(points, list), "The ordered points array is absent.")
        captures = points + ([document["residual"]] if document.get("residual") is not None else [])
        for point in captures:
            check_capture(point, session)
            require(isinstance(point["hint_log"], dict)
                    and point["hint_log"].get("availability") == "complete", "A point lacks complete hint logs.")
        lookup = {name: (evidence, parse_citations(cites)[0])
                  for _, name, evidence, cites in rows}

        def references(name):
            evidence, citations = lookup[name]
            return evidence, [(pointer_tokens(c.pointer), resolve_citation(c, base, documents))
                              for c in citations]

        def verbatim(name, allowed):
            evidence, refs = references(name)
            values = quoted_values(evidence)
            cited = [value for tokens, value in refs if allowed(tokens) and isinstance(value, str)]
            require(all(value in cited for value in values), f"{name}: quoted text differs from its cited observation.")
            require(cited, f"{name}: cite the exact required observation.")
            return refs

        trigger_refs = verbatim("trigger_goal", lambda t: (len(t) == 3 and t[0] == "points"
                                             or len(t) == 2 and t[0] == "residual")
                 and t[-1] in {"goal", "goal_nonotation"})

        def refusal(name):
            evidence, refs = references(name)
            messages = [(tokens, value) for tokens, value in refs if tokens[-1:] == ["message"]]
            require(len(messages) == 1, f"{name}: cite one exact refusal message.")
            tokens, _ = messages[0]
            observation = refusal_observation(document, "/" + "/".join(tokens))
            record = observation["refusal"]
            require(record["exposure"] == "exposed", f"{name}: the refusing clause is not exposed.")
            values = quoted_values(evidence)
            require(record["message"] in values and record["clause"] in values,
                    f"{name}: quote the exact exposed clause and refusal message.")
            require(all(value in {record["message"], record["clause"]} for value in values),
                    f"{name}: the quoted refusal contains an unsupported value.")
            trial = observation["trial"]
            last = len(trial["commands"]) - 1
            command_tokens = tokens[:-3] + ["hand_call", str(record["hand_call_index"]), "commands", str(last), "command"]
            command, _, before, _ = command_observation(document, command_tokens, session)
            require(command["outcome"] == "refused" and command["refusal"] == record["message"],
                    f"{name}: the final command differs from the recorded refusal.")
            require(command["command"] == trial["command"], f"{name}: the refused command is not the recorded rule.")
            return tokens[:-1], trial, before

        cycles = sorted({int(m[1]) for name in lookup if (m := CYCLE.fullmatch(name))})
        previous, normalization_refs, terminal_snapshot = None, [], None
        for number in cycles:
            prefix = f"cycle.{number}."
            key, initial_trial, state = refusal(prefix + "refusal")
            if number == 1:
                for tokens, _ in trigger_refs:
                    length = 2 if tokens[0] == "points" else 1
                    trigger = resolve_pointer(document, "/" + "/".join(tokens[:length]))
                    require(same_state(trigger, state), "The trigger goal differs from the first refusal state.")
            if previous is not None:
                require(key == previous, "A repeated cycle does not start at the preceding next refusal.")
            reason_refs = verbatim(prefix + "reason", lambda t: t[0] in {"points", "residual", "snapshots"}
                                   and any(k in t for k in {"hyps", "evars", "hint_log", "goal", "goal_nonotation", "refusal"}))
            # Reason observations must belong to the current refusal point or its exact before snapshot.
            for tokens, _ in reason_refs:
                if tokens[0] == "snapshots":
                    capture = resolve_pointer(document, "/snapshots/" + tokens[1].replace("~", "~0").replace("/", "~1"))
                else:
                    length = 2 if tokens[0] == "points" else 1
                    capture = resolve_pointer(document, "/" + "/".join(tokens[:length]))
                require(same_state(capture, state), "A reason cites a different proof state.")
            evidence, refs = references(prefix + "normalization")
            values = quoted_values(evidence)
            require(len(refs) == len(values), "Each normalization command needs its own exact citation.")
            for (tokens, value), quoted in zip(refs, values):
                require(tokens[-1] == "command" and quoted == value, "A normalization differs from the observed command.")
                command, _, before, after = command_observation(document, tokens, session)
                require(command["outcome"] == "accepted", "A proposed normalization was refused.")
                require(same_state(state, before), "The normalization chain skips or changes the before state.")
                state = after
                normalization_refs.append(tuple(tokens))
            _, next_refs = references(prefix + "next_refusal")
            if any(tokens[-1:] == ["message"] for tokens, _ in next_refs):
                previous, next_trial, next_state = refusal(prefix + "next_refusal")
            else:
                evidence, _ = references(prefix + "next_refusal")
                require(quoted_values(evidence) == ["accepted"] and len(next_refs) == 1,
                        "Quote and cite the accepted rule command outcome.")
                tokens, value = next_refs[0]
                require(tokens[-1] == "outcome" and value == "accepted", "The next rule command did not succeed.")
                command, next_trial, next_state, terminal_snapshot = command_observation(document, tokens, session)
                require(command["command"] == next_trial["command"]
                        and next_trial["outcome"] == "accepted"
                        and int(tokens[-2]) == len(next_trial["commands"]) - 1,
                        "The accepted command is not the final recorded rule invocation.")
                previous = None
                require(number == cycles[-1], "A cycle continues after its rule succeeded.")
            require(next_trial["command"] == initial_trial["command"], "The next trial calls a different rule.")
            require(same_state(state, next_state), "The next rule trial does not follow the normalization chain.")
        candidate_tokens = [tuple(tokens) for tokens, _ in references("candidate")[1]]
        require(candidate_tokens == normalization_refs, "The candidate citations differ from the ordered normalization sum.")
        terminal, terminal_refs = references("terminal")
        require(any(tokens in (["verdict"], ["verdict", "status"], ["verdict", "evidence"])
                    for tokens, _ in terminal_refs), "The terminal row must cite the top-level verdict.")
        verdict = document["verdict"]
        require(isinstance(verdict, dict), "The terminal verdict is absent.")
        require(verdict.get("status") != "unresolved", "The trace is complete but its terminal verdict is unresolved.")
        if terminal == "unsatisfiable":
            raise DiagnosisError("The verified unsatisfiability-certificate payload is not specified; no refusal can establish it.")
        require(verdict.get("status") == "actual-success" and verdict.get("scope") == "whole-proof",
                "The verdict does not establish whole-proof actual success.")
        require(verdict.get("evidence") == "#/completion/closure_check", "The success verdict lacks its exact Qed evidence pointer.")
        evidence = resolve_pointer(document, "/completion/closure_check")
        require(isinstance(evidence, dict) and evidence.get("command") == "Qed." and evidence.get("accepted") is True
                and evidence.get("unresolved_evars") is False, "The terminal evidence does not record accepted Qed.")
        require(completion.get("proof_closed") is True and document.get("residual") is None
                and document["coverage"].get("traversal") == "proof-closed", "The success verdict conflicts with the traversal.")
        require(previous is None and terminal_snapshot is not None,
                "The final cycle still records a refusal instead of rule success.")
        require(not any(terminal_snapshot[name] for name in ("current_goals", "shelf", "given_up"))
                and not any(entry.get("status") == "undefined" for entry in terminal_snapshot["evars"]["entries"]),
                "The accepted rule only made progress; its after-state still has obligations.")
        return []
    except (DiagnosisError, KeyError, IndexError, TypeError, ValueError, AttributeError) as error:
        return [f"Semantic validation: {error}"]


def violations(path: Path, template=False, structure_only=False) -> list[str]:
    """Require fixed rows, ordered cycles, and resolving citations."""
    errors = []
    try:
        text = path.read_text(encoding="utf-8")
        rows = table_rows(text)
    except (OSError, UnicodeError, DiagnosisError) as error:
        return [f"{path}: {error}"]
    names = [row[1] for row in rows]
    if len(set(names)) != len(names):
        errors.append("The diagnosis contains duplicate row names.")
    cycles = sorted({int(match[1]) for name in names if (match := CYCLE.fullmatch(name))})
    if not cycles or cycles != list(range(1, max(cycles) + 1)):
        errors.append("The diagnosis needs consecutive cycles starting at 1.")
    expected = ["trigger_goal"]
    expected += [f"cycle.{cycle}.{kind}" for cycle in cycles for kind in CYCLE_ROWS]
    expected += ["terminal", "candidate"]
    if names != expected:
        errors.append("The diagnosis rows are missing, unknown, or out of order.")
    documents = {}
    for line, name, evidence, citation_text in rows:
        location = f"Line {line}, row {name}"
        empty = not evidence or PLACEHOLDER.fullmatch(evidence)
        citation_placeholder = not citation_text or PLACEHOLDER.fullmatch(citation_text)
        if template and empty and citation_placeholder:
            continue
        if empty:
            errors.append(f"{location}: replace the evidence placeholder.")
        citations, remaining = parse_citations(citation_text)
        if remaining and not citation_placeholder:
            errors.append(f"{location}: use only TRACE.json citations in the citation cell.")
        if not citations:
            errors.append(f"{location}: a filled row needs a TRACE.json citation.")
        if citation_placeholder:
            errors.append(f"{location}: replace the citation placeholder.")
        for citation in citations:
            try:
                resolve_citation(citation, path.parent, documents)
            except DiagnosisError as error:
                errors.append(f"{location}: {error}")
        if name.endswith(".refusal") or name.endswith(".next_refusal"):
            if not empty and not re.search(r'`[^`]+`|"[^"\n]+"', evidence):
                errors.append(f"{location}: quote the exact refusal or terminal response.")
        if name == "candidate" and not empty:
            expected_sum = "+".join(f"cycle.{cycle}.normalization" for cycle in cycles)
            if re.sub(r"\s|`", "", evidence) != expected_sum:
                errors.append(f"{location}: list the ordered sum of all normalization rows.")
        if name == "terminal" and not empty and evidence not in {"success", "unsatisfiable"}:
            errors.append(f"{location}: the terminal value must be success or unsatisfiable.")
    if not template and not structure_only and not errors:
        errors.extend(semantic_violations(rows, documents, path.parent))
    return [f"{path}: {error}" for error in errors]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, help="Diagnosis Markdown files to check")
    parser.add_argument("--root", type=Path, default=ROOT,
                        help="Workspace used to discover DIAGNOSIS.md files")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--template", action="store_true",
                        help="Allow empty placeholder rows; still check every filled row")
    mode.add_argument("--structure-only", action="store_true",
                      help="Check preparation structure/citations; do not approve completion")
    args = parser.parse_args(argv)
    paths = args.paths or sorted((args.root / "build/stock-zisk/automation-validation")
                                .rglob("DIAGNOSIS.md"))
    errors = [error for path in paths for error in violations(path, template=args.template, structure_only=args.structure_only)]
    for error in errors:
        print(error)
    if errors:
        return 1
    label = "Template" if args.template else "Structure-only" if args.structure_only else "Completed"
    print(f"{label} diagnosis checks passed for {len(paths)} file(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
