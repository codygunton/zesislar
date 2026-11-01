"""Render complete, source-resolved witness data for the existing selector.

The pass supplies typed source bindings.  This module checks their mechanical
shape against the actual declaration; it does not infer values from target
equalities.  Rocq must still check the emitted terms and their application.
"""

import hashlib
from pathlib import Path

from check_data_only_lemmas import atom, rocq_commands, rocq_tokens, top_level_positions
from entry_bindings import declared_binders, normalize_type


def _words(command):
    # rocq_tokens emits decimal digits separately. Preserve contiguous literals
    # when reusing the existing binder parser; do not join separated digits.
    result = []
    previous_end = -1
    for token, position in command:
        if result and result[-1].isdigit() and token.isdigit() and position == previous_end:
            result[-1] += token
        else:
            result.append(token)
        previous_end = position + len(token)
    return result


def _unwrap(values):
    while values and values[0] == "(":
        inside, end = atom(values, 0)
        if end != len(values):
            break
        values = inside
    return values


def _register_owners(body):
    result = []
    marker = [token for token, _ in rocq_tokens("↦ᵣ")]
    for index, token in enumerate(body):
        if not token.startswith('"') or body[index + 1:index + 1 + len(marker)] != marker:
            continue
        position = index + 1 + len(marker)
        value, end = atom(body, position)
        value = _unwrap(value)
        if value == ["RVal_Bits"]:
            word, _ = atom(body, end)
        elif value[:1] == ["RVal_Bits"]:
            word = _unwrap(value[1:])
        else:
            continue
        result.append((token[1:-1], word))
    return result


def has_witness_slots(source, name):
    commands = [command for command in rocq_commands(source)
                if [token for token, _ in command[:2]] == ["Definition", name]]
    if len(commands) != 1:
        raise ValueError("The witness target needs one source Definition.")
    values = _words(commands[0])
    position = values.index(":=") + 1
    while position < len(values) and values[position] == "(":
        position += 1
    return values[position:position + 1] == ["∃"]


def declared_witness_slots(source, name):
    """Read one flat leading telescope, retaining every used existential.

    Only syntactically unused slots disappear.  Resource ownership never makes
    a slot disappear.  Nested binders are refused rather than guessed through.
    """
    commands = [command for command in rocq_commands(source)
                if [token for token, _ in command[:2]] == ["Definition", name]]
    if len(commands) != 1:
        raise ValueError("The witness target needs one source Definition.")
    values = _words(commands[0])
    if ":=" not in values:
        raise ValueError("The witness target has no body.")
    position = values.index(":=") + 1
    while position < len(values) and values[position] == "(":
        position += 1
    if values[position:position + 1] != ["∃"]:
        raise ValueError("The witness target needs a leading existential telescope.")
    position += 1
    start = position
    while position < len(values) and values[position] == "(":
        _, position = atom(values, position)
    if values[position:position + 1] != [","]:
        raise ValueError("The witness telescope has an unsupported shape.")
    telescope = " ".join(values[start:position])
    slots = declared_binders("Definition slots " + telescope + " : Type := unit.", "slots")
    if not slots or len({slot["name"] for slot in slots}) != len(slots):
        raise ValueError("The witness telescope is empty or repeats a name.")
    outer = {slot["name"] for slot in declared_binders(source, name)}
    names = {slot["name"] for slot in slots}
    if names.intersection(outer):
        raise ValueError("The witness telescope shadows a declaration parameter.")
    if any(names.intersection(token for token, _ in rocq_tokens(slot["type"])) for slot in slots):
        raise ValueError("The witness telescope needs a dependent product.")
    body = values[position + 1:]
    if set(body).intersection({"∃", "∀", "forall", "fun", "let", "match"}):
        raise ValueError("The witness body has unsupported nested binders.")
    register_slots = {}
    for register, word in _register_owners(body):
        # Only a direct existential variable, with an optional annotation,
        # determines a register slot. Compound expressions are not inverted.
        if word and (len(word) == 1 or word[1:2] == [":"]):
            if word[0] in {slot["name"] for slot in slots}:
                if word[0] in register_slots and register_slots[word[0]] != register:
                    raise ValueError("A witness slot fixes multiple register owners.")
                register_slots[word[0]] = register
    return dict(declared=slots, vacuous=[slot for slot in slots if slot["name"] not in body],
                remaining=[slot for slot in slots if slot["name"] in body],
                register_slots=register_slots)


def check_witness_shape(expected, supplied):
    """Check identity, count, order, and type, including equal-typed slots."""
    if len(expected) != len(supplied):
        raise ValueError("The witness slot count does not match the target declaration.")
    for index, (target, source) in enumerate(zip(expected, supplied)):
        if target["name"] != source["name"]:
            raise ValueError("The witness slot order differs at slot " + str(index) + ".")
        if normalize_type(target["type"]) != normalize_type(source["type"]):
            raise ValueError("The witness slot type differs at slot " + str(index) + ".")


def product(types):
    result = "unit"
    for kind in reversed(types):
        result = "(" + kind + " * " + result + ")%type"
    return result


def value_spine(values):
    result = "tt"
    for value in reversed(values):
        result = "((" + value + "), " + result + ")"
    return result


def _source_declaration(binding, source_texts=None):
    from render_support import identifier, record

    record(binding, {"path", "sha256", "declaration"}, "witness source binding")
    path = Path(binding["path"])
    if not path.is_absolute():
        raise ValueError("The witness source path must be absolute.")
    data = source_texts[str(path)].encode() if source_texts and str(path) in source_texts else path.read_bytes()
    if hashlib.sha256(data).hexdigest() != binding["sha256"]:
        raise ValueError("The resolved witness source changed.")
    name = identifier(binding["declaration"], "witness source declaration")
    commands = [command for command in rocq_commands(data.decode())
                if [token for token, _ in command[:2]] == ["Definition", name]]
    if len(commands) != 1:
        raise ValueError("The witness source needs one bound Definition.")
    values = _words(commands[0])
    if ":=" not in values:
        raise ValueError("The witness source has no body.")
    return values


def _source_definition(binding, source_texts=None):
    values = _source_declaration(binding, source_texts)
    return values[values.index(":=") + 1:]


def _result_type(declaration):
    signature = declaration[:declaration.index(":=")]
    colons = top_level_positions(signature, {":"})
    if len(colons) != 1:
        raise ValueError("The witness source needs an explicit result type.")
    return _unwrap(signature[colons[0] + 1:])


def _check_sources(target_source, target, assertion, values, source_texts=None):
    commands = [command for command in rocq_commands(target_source)
                if [token for token, _ in command[:2]] == ["Definition", target]]
    target_declaration = _words(commands[0])
    sources = [assertion] + values
    declarations = [_source_declaration(binding, source_texts) for binding in sources]
    if len({(row["path"], row["declaration"]) for row in sources}) != len(sources):
        raise ValueError("The witness source roles repeat a declaration.")
    for index, declaration in enumerate(declarations):
        if declaration == target_declaration:
            raise ValueError("The target declaration cannot supply its own witness provenance.")
        kind = _result_type(declaration)
        if index == 0:
            if not kind or kind[0].rsplit(".", 1)[-1] != "iProp":
                raise ValueError("The forward source owner must be an assertion definition.")
        elif any(token.rsplit(".", 1)[-1] in {"iProp", "Prop", "SProp", "Type", "Set"} for token in kind):
            raise ValueError("A witness value source cannot be an assertion or a pure conclusion.")


def _array_owners(source, name):
    commands = [command for command in rocq_commands(source)
                if [token for token, _ in command[:2]] == ["Definition", name]]
    if len(commands) != 1:
        raise ValueError("The array source needs one bound Definition.")
    command = commands[0]
    values = [token for token, _ in command]
    marker = [token for token, _ in rocq_tokens("↦ₘ∗")]
    result = []
    for position in range(values.index(":=") + 1, len(values)):
        if values[position:position + len(marker)] != marker:
            continue
        # Require a grouped address. Never guess an ungrouped application or
        # commute address arithmetic to make two owners appear identical.
        if values[position - 1] != ")":
            continue
        start, depth = position - 1, 1
        while start and depth:
            start -= 1
            depth += (values[start] == ")") - (values[start] == "(")
        if depth:
            raise ValueError("The array owner has an unfinished address.")
        address_text = source[command[start][1]:command[position - 1][1] + len(command[position - 1][0])]
        address = _words(rocq_tokens(address_text))
        while True:
            previous = address
            address = _unwrap(address)
            if address[-2:] == ["%", "Z"]:
                address = address[:-2]
            if address == previous:
                break
        begin = position + len(marker)
        if values[begin] == "{":
            raise ValueError("The array witness needs an explicit supported fraction view.")
        payload, end = atom(values, begin)
        text = source[command[begin][1]:command[end - 1][1] + len(command[end - 1][0])]
        result.append(dict(address=address, payload=_unwrap(_words(rocq_tokens(text))), value=text))
    return result


def resolved_array_value(target_source, target, slot, binding):
    """Read a payload from the exact same full array owner in the source.

    This selects a value only. It does not duplicate, convert, or consume the
    array owner, and it does not use a target pure equality as a source value.
    """
    _source_definition(binding)  # Verify the exact source bytes and declaration.
    targets = [owner for owner in _array_owners(target_source, target) if owner["payload"] == [slot]]
    if len(targets) != 1:
        raise ValueError("The witness slot needs one direct target array owner.")
    owners = [owner for owner in _array_owners(Path(binding["path"]).read_text(), binding["declaration"])
              if owner["address"] == targets[0]["address"]]
    if len(owners) != 1:
        raise ValueError("The source does not resolve one exact same-address array owner.")
    return owners[0]["value"]


def _contains(values, fragment):
    return any(values[index:index + len(fragment)] == fragment
               for index in range(len(values) - len(fragment) + 1))


def resolved_witness_data(source, target, value, *, source_texts=None):
    """Emit data and a register-input descriptor from checked pass bindings.

    Each binding has a source reference. Register bindings capture the current
    owned word through the existing input interface. Expressions are supplied
    by the source pass, never reconstructed from target pure conclusions.
    """
    # Import lazily: render_support exposes this function to its callers.
    from render_support import binders, expression, identifier, record, sequence

    record(value, {"name", "parameters", "source_assertion", "value_sources", "slots"}, "witness data")
    name = identifier(value["name"], "witness data name")
    parameters = binders(value["parameters"], reserved=(name, "source_words"))
    layout = declared_witness_slots(source, target)
    if not layout["remaining"]:
        raise ValueError("The witness target has no remaining slots.")
    value_sources = sequence(value["value_sources"], "witness value sources")
    _check_sources(source, target, value["source_assertion"], value_sources, source_texts)
    slots = sequence(value["slots"], "resolved witness slots")
    for slot in slots:
        record(slot, {"name", "type", "source", "value"}, "resolved witness slot")
    check_witness_shape(layout["remaining"], slots)
    internal = [dict(name=slot["name"], type=slot["type"]) for slot in reversed(slots)]
    check_witness_shape(list(reversed(layout["remaining"])), internal)
    registers, terms = [], []
    for slot in slots:
        origin = slot["source"]
        if not isinstance(origin, dict) or not origin.get("provenance"):
            raise ValueError("The witness slot lacks its resolved source provenance.")
        source_body = _source_definition(origin["provenance"], source_texts)
        if origin.get("kind") in {"register", "array"}:
            if origin["provenance"] != value["source_assertion"]:
                raise ValueError("The witness owner differs from the bound forward source assertion.")
        elif origin.get("kind") == "expression" and origin["provenance"] not in value_sources:
            raise ValueError("The witness expression lacks an approved source value definition.")
        expected_register = layout["register_slots"].get(slot["name"])
        if expected_register is not None and (origin.get("kind") != "register" or
                                             origin.get("register") != expected_register):
            raise ValueError("The witness source register differs from its target owner.")
        if origin.get("kind") == "register":
            record(origin, {"kind", "register", "width", "provenance"}, "register source")
            register = origin["register"]
            if not isinstance(register, str) or not register or '"' in register:
                raise ValueError("The witness register name is invalid.")
            width = origin["width"]
            if type(width) is not int or width <= 0:
                raise ValueError("The witness register width is unresolved.")
            kind = "bv " + str(width) + "%N"
            if normalize_type(slot["type"]) != normalize_type(kind):
                raise ValueError("The witness register width differs from its slot type.")
            if slot["value"] is not None:
                raise ValueError("A register witness must use its resolved owned value.")
            owners = [word for owner, word in _register_owners(source_body) if owner == register]
            if not owners:
                raise ValueError("The resolved source does not own the witness register.")
            if len(owners) != 1:
                raise ValueError("The resolved source has ambiguous register owners.")
            word = owners[0]
            if len(word) > 1 and word[1] == ":":
                if normalize_type(" ".join(word[2:])) != normalize_type(kind):
                    raise ValueError("The resolved source register annotation has a different width.")
            key = (register, width)
            if any(other[0] == register and other != key for other in registers):
                raise ValueError("The witness register has conflicting source widths.")
            if key not in registers:
                registers.append(key)
            term = "source_words"
            for _ in range(registers.index(key)):
                term = "(snd " + term + ")"
            terms.append("(fst " + term + ")")
        elif origin.get("kind") == "array":
            record(origin, {"kind", "provenance"}, "array source")
            if slot["value"] is not None:
                raise ValueError("An array witness must use its resolved source payload.")
            terms.append(expression(resolved_array_value(source, target, slot["name"], origin["provenance"]),
                                    "resolved array payload"))
        elif origin.get("kind") == "expression":
            record(origin, {"kind", "provenance"}, "expression source")
            term = expression(slot["value"], "resolved source expression")
            if not _contains(source_body, _words(rocq_tokens(term))):
                raise ValueError("The witness expression is absent from its bound source body.")
            terms.append(term)
        else:
            raise ValueError("The witness source is absent or unsupported.")
    input_type = product(["bv " + str(width) + "%N" for _, width in registers])
    descriptor = "ZesuWitnessUnit"
    for register, width in reversed(registers):
        descriptor = ("(ZesuWitnessPair "
                      "(ZesuWitnessRegister " +
                      str(width) + "%N \"" + register + "\") " + descriptor + ")")
    witness_type = product([slot["type"] for slot in slots])
    typed = "".join(" (" + bound + " : " + kind + ")" for bound, kind in parameters)
    text = ("Definition " + name + typed + " (source_words : " + input_type + ")\n"
            "  : " + witness_type + " :=\n  " + value_spine(terms) + ".\n")
    return dict(source=text, input_type=input_type, input=descriptor,
                witness_type=witness_type, registers=registers,
                declaration_order=layout["remaining"], internal_order=internal,
                vacuous=layout["vacuous"], provenance=[slot["source"] for slot in slots])
