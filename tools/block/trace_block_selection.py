"""Classify retained typed entries without running a proof command.

Unknown shapes remain unknown. A later refusal cannot remove a typed trigger.
This module does not read or modify a running capture stream.
"""

import hashlib
import re


class UnknownShape(ValueError):
    pass


def parts(text):
    """Split one printed application. Preserve nested terms as exact strings."""
    text = text.strip()
    while text.startswith("("):
        depth = 0
        closes = None
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closes = index
                    break
        if closes != len(text) - 1:
            break
        text = text[1:-1].strip()
    result, start, depth, braces, quoted = [], None, 0, 0, False
    for index, char in enumerate(text):
        if char == '"':
            quoted = not quoted
        if not quoted:
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            elif char == "{":
                braces += 1
            elif char == "}":
                braces -= 1
        if depth < 0 or braces < 0:
            raise UnknownShape("The printed term has unbalanced delimiters.")
        if char.isspace() and depth == braces == 0 and not quoted:
            if start is not None:
                result.append(text[start:index])
                start = None
        elif start is None:
            start = index
    if depth or braces or quoted:
        raise UnknownShape("The printed term has unclosed delimiters.")
    if start is not None:
        result.append(text[start:])
    if not result:
        raise UnknownShape("The printed term is empty.")
    result[0] = result[0].removeprefix("@")
    return result


def expand(text, definitions):
    seen = set()
    while True:
        items = parts(text)
        while items[0].startswith("("):
            items = parts(items[0]) + items[1:]
        head = items[0]
        if head not in definitions:
            if head in ("let", "match", "fun") or head.startswith("?"):
                raise UnknownShape("The term head needs unsupported reduction.")
            return items
        if head in seen:
            raise UnknownShape("A local definition forms a cycle.")
        seen.add(head)
        body = definitions[head]
        if len(items) != 1:
            body = "(" + body + " " + " ".join(items[1:]) + ")"
        text = body


def integer(text):
    items = parts(text)
    head = items[0]
    if len(items) == 1 and re.fullmatch(r"-?[0-9]+", head):
        return int(head)
    if items == ["xH"]:
        return 1
    if items in (["Z0"], ["N0"]):
        return 0
    if len(items) == 2:
        inner = integer(items[1])
        if head == "xO":
            return 2 * inner
        if head == "xI":
            return 2 * inner + 1
        if head in ("Zpos", "Npos"):
            return inner
        if head == "Zneg":
            return -inner
    raise UnknownShape("The expected integer is not a closed printed integer.")


def app(text, head, arguments, definitions):
    items = expand(text, definitions)
    if items[0] != head:
        return None
    if len(items) < arguments + 1:
        raise UnknownShape("The application has too few explicit arguments.")
    return items[-arguments:] if arguments else []


def bv_literal(text, width, value, definitions):
    items = expand(text, definitions)
    if items[0] != "BV":
        return False
    if len(items) < 3:
        raise UnknownShape("The BV constructor lacks its width or value.")
    return integer(items[1]) == width and integer(items[2]) == value


def masked(text, definitions, *, reduced=False):
    outer = app(text, "bv_or", 2, definitions)
    if outer is None or not bv_literal(outer[1], 64, 0, definitions):
        return False
    inner = app(outer[0], "bv_and", 2, definitions)
    if inner is None or not bv_literal(inner[1], 64, 18446744073709551614, definitions):
        return False
    if reduced:
        # The reduced guard treats the complete inner term as the address.
        # Do not inspect it or discard its later closed-address refusal.
        return True
    added = app(inner[0], "bv_add", 2, definitions)
    return added is not None and bv_literal(added[1], 64, 0, definitions)


def return_shape(goal, client, definitions):
    if client == "ReturnRoute.normalize":
        args = app(goal, "LiTactic", 1, definitions)
        if args is None:
            return False
        args = app(args[0], "normalize_instr_addr", 1, definitions)
        if args is None:
            return False
        args = app(args[0], "bv_unsigned", 1, definitions)
        return args is not None and masked(args[0], definitions, reduced=True)
    wrapper = "SimplAnd" if client == "ReturnRoute.fault" else "SimplImpl"
    args = app(goal, wrapper, 2, definitions)
    if args is None:
        return False
    equation = app(args[0], "eq", 2, definitions)
    if equation is None or not bv_literal(equation[1], 1, 1, definitions):
        return False
    extract = app(equation[0], "bv_extract", 3, definitions)
    if extract is None or integer(extract[0]) != 0 or integer(extract[1]) != 1:
        return False
    shift = app(extract[2], "bv_shiftr", 2, definitions)
    return (shift is not None and bv_literal(shift[1], 64, 1, definitions)
            and masked(shift[0], definitions))


def marker_present(hyps, marker, definitions):
    heads = {marker, "ZesuSsz.Automation.EntryIntro." + marker}
    return any(expand(hyp["type"], definitions)[0] in heads for hyp in hyps)


def classify(entry, rows, descriptor, guard_commands):
    """Return (actual-trigger | non-trigger | unknown, reason)."""
    client = entry["rule"]
    accepted = {row.get("clause") for row in rows if row["kind"] == "hand-accepted"}
    goals = entry["capture"]["no_notation"]["goals"]
    if not goals:
        return "unknown", "The native entry has no current goal."
    current = goals[0]
    hyps = current["hyps"]
    definitions = {name: hyp["body"] for hyp in hyps if hyp.get("body") is not None
                   for name in hyp["names"]}
    try:
        if client == "Hooks.zesu_conjunct_head_if_enabled":
            expected = ('lazymatch goal with |- envs_entails _ _ => idtac | _ => fail 0 '
                        '"entry wrapper is absent" end')
            if descriptor.get("commands", {}).get("entry-goal-shape") != expected:
                return "unknown", "The conjunct goal-shape guard differs from its reviewed bytes."
            if not (marker_present(hyps, "ZesuEntryIntroApplied", definitions)
                    and marker_present(hyps, "ZesuEntryIntroHeads", definitions)):
                return "non-trigger", "The typed introduction/cache marker gate is absent."
            if "entry-goal-shape" not in accepted:
                return "unknown", "The marker gate exists without an accepted goal-shape guard."
            return "actual-trigger", "The typed marker gate and goal-shape guard match."
        if client not in guard_commands:
            return "unknown", "The native client has no reviewed selection policy."
        commands = descriptor["commands"]
        for clause, record in guard_commands[client].items():
            if hashlib.sha256(commands[clause].encode()).hexdigest() != record["sha256"]:
                return "unknown", "A typed guard command differs from its reviewed bytes."
        if client == "ReturnRoute.fault":
            return "actual-trigger", "The exact native fault-hint admission pattern matched."
        if client == "ReturnRoute.normalize" and "requested-trigger" in accepted:
            return "actual-trigger", "The exact typed masked-return guard accepted."
        if "closed-ra" in accepted:
            return "actual-trigger", "The exact typed client guard accepted."
        matches = return_shape(current["conclusion"], client, definitions)
        return (("actual-trigger", "The captured kernel term has the exact return shape.")
                if matches else ("non-trigger", "The captured kernel term has a different shape."))
    except (UnknownShape, KeyError, TypeError) as error:
        return "unknown", str(error)
