"""Render source-bound function-return declarations without proof scripts."""

import re

from check_data_only_lemmas import rocq_commands, rocq_tokens
from entry_bindings import declared_binders
from render_support import expression, identifier


def return_blocks(design):
    """Use the table's return clauses, never the absence of successors alone."""
    result = {}
    seen = set()
    for block in design["blocks"]:
        pc = int(block["entry_pc"], 0)
        if pc in seen:
            raise ValueError("The design repeats a block address.")
        seen.add(pc)
        successors = block["successor_pcs"]
        clause = block.get("return_clause")
        if clause is not None:
            if successors or "return_instruction_pc" not in clause:
                raise ValueError("The design has an inconsistent function-return exit.")
            result[pc] = block
        elif not successors:
            raise ValueError("A terminal block has no declared exit kind.")
    return result


def source_definition(source, name):
    """Retain the complete source command, including its original body bytes."""
    identifier(name, "source return predicate")
    found = []
    for command in rocq_commands(source):
        words = [value for value, _ in command]
        if words[:2] != ["Definition", name]:
            continue
        start = command[0][1]
        last, offset = command[-1]
        tail = offset + len(last)
        period, relative = rocq_tokens(source[tail:])[0]
        if period != ".":
            raise ValueError("The source return definition has no final period.")
        found.append(source[start : tail + relative + 1])
    if len(found) != 1:
        raise ValueError("The source needs exactly one return definition.")
    return found[0]


def return_package(source, source_name, target_name, parameters):
    """Copy the owned package; omit only parameters absent from its body."""
    definition = source_definition(source, source_name)
    match = re.fullmatch(
        r"Definition\s+" + re.escape(source_name)
        + r"(?P<telescope>.*?)\s*:\s*iProp\s+Sigma\s*:=\s*(?P<body>.*?)\.\s*",
        definition,
        re.S,
    )
    if match is None:
        raise ValueError("The source return predicate is not an iProp definition.")
    declared = declared_binders(definition, source_name)
    by_name = {row["name"]: row for row in declared}
    if any(by_name.get(row["name"]) != row for row in parameters):
        raise ValueError("The return parameters differ from their source types.")
    names = {row["name"] for row in parameters}
    if [row for row in declared if row["name"] in names] != parameters:
        raise ValueError("The return parameters differ from their source order.")
    body = match["body"]
    body_tokens = {value for value, _ in rocq_tokens(body)}
    removed = [row for row in declared if row["name"] not in names]
    if any(row["name"] in body_tokens for row in removed):
        raise ValueError("A removed return parameter occurs in the owned package.")
    identifier(target_name, "generated return predicate")
    expression(body, "source return package")
    telescope = "".join(f" ({row['name']} : {row['type']})" for row in parameters)
    rendered = (
        f"Definition {target_name} `{{!islaG Sigma}} `{{!threadG}}{telescope}"
        f" : iProp Sigma :=\n  {body}.\n"
    )
    return rendered, {"body": body, "omitted_unused_parameters": removed}


def add_return_precondition(statement, address, package):
    """Insert one continuation premise and retain all existing statement bytes."""
    expression(address, "return address")
    expression(package, "return package application")
    if re.search(r"\binstr_pre\s+" + re.escape(address) + r"\b", statement):
        raise ValueError("The statement already has a return precondition.")
    depth = 0
    for token, position in rocq_tokens(statement):
        if token in ("(", "{", "["):
            depth += 1
        elif token in (")", "}", "]"):
            depth -= 1
        elif token == ":" and depth == 0:
            premise = f"\n  instr_pre {address} ({package}) -∗"
            return statement[: position + 1] + premise + statement[position + 1 :]
    raise ValueError("The caller statement has no top-level result type.")


RETURN_TAIL = " ∗ True)) ∗ K)%I"


def add_return_facts(source, facts):
    """Add pure exit facts after the last fact of the one return package body.

    The owned resources come first, so they fix the package existentials (for
    example the output bytes) before a fact about them is proved.
    """
    if not facts:
        return source
    for fact in facts:
        expression(fact, "return fact")
        if "⌜" in fact or "⌝" in fact:
            raise ValueError("A return fact must be a bare proposition.")
    if source.count(RETURN_TAIL) != 1:
        raise ValueError("The return package needs exactly one pure fact tail.")
    added = "".join(" ∗ ⌜" + fact + "⌝" for fact in facts)
    return source.replace(RETURN_TAIL, added + RETURN_TAIL)


ENTRY_TAIL = "⌝))%I"


def add_entry_facts(source, facts):
    """Add pure facts after the last fact of the one entry alternative in source."""
    if not facts:
        return source
    for fact in facts:
        expression(fact, "entry fact")
    if source.count(ENTRY_TAIL) != 1:
        raise ValueError("The entry needs exactly one pure fact tail.")
    added = "".join(" ∗ ⌜" + fact + "⌝" for fact in facts)
    return source.replace(ENTRY_TAIL, "⌝" + added + "))%I")
