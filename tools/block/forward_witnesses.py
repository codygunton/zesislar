"""Derive complete witness models from bound forward-output rows.

The producer reads source application arguments and source resource roles.
It never solves target equalities or chooses a value from a target conclusion.
All generated text is a value Definition; no proof script is generated.
"""

import hashlib
import json
from pathlib import Path

from check_data_only_lemmas import atom, rocq_tokens, top_level_positions
from entry_bindings import declared_binders, normalize_type
from witness_data import (_array_owners, _register_owners, _source_declaration,
                          _source_definition, _unwrap, _words, declared_witness_slots,
                          closed_bitvector_width as _width)


def _bound_json(binding):
    from render_support import record

    record(binding, {"path", "sha256"}, "forward output binding")
    data = Path(binding["path"]).read_bytes()
    if hashlib.sha256(data).hexdigest() != binding["sha256"]:
        raise ValueError("The forward output changed.")
    return json.loads(data)


def _pointer(document, pointer):
    if not isinstance(pointer, str) or not pointer.startswith("/"):
        raise ValueError("The forward row needs an explicit JSON pointer.")
    for key in pointer[1:].split("/"):
        key = key.replace("~1", "/").replace("~0", "~")
        document = document[int(key)] if isinstance(document, list) else document[key]
    return document


def _lex(text):
    result = []
    for token, position in rocq_tokens(text):
        if (result and token.isdigit() and result[-1][0].isdigit()
                and result[-1][1] + len(result[-1][0]) == position):
            previous, start = result.pop()
            result.append((previous + token, start))
        else:
            result.append((token, position))
    return result


def _application_arguments(text):
    lexed = _lex(text)
    values = [token for token, _ in lexed]
    if not values or values[0] in {"(", "@", "let", "fun", "match"}:
        raise ValueError("The forward source application needs an explicit named head.")
    arguments, position = [], 1
    while position < len(values):
        start = position
        _, position = atom(values, position)
        arguments.append(text[lexed[start][1]:lexed[position - 1][1] + len(lexed[position - 1][0])])
    return values[0], arguments



def _canonical(values, *, word=False, address=False):
    values = _unwrap(values)
    if word:
        colons = top_level_positions(values, {":"})
        if colons:
            if len(colons) != 1:
                raise ValueError("The source word has an ambiguous annotation.")
            values = _unwrap(values[:colons[0]])
    if address and values[-2:] == ["%", "Z"]:
        return _canonical(values[:-2], address=True)
    result, position = [], 0
    while position < len(values):
        start = position
        inside, position = atom(values, position)
        if values[start] == "(":
            item = _canonical(inside)
            result.append(item[0] if len(item) == 1 else item)
        else:
            result.extend(inside)
    return tuple(result)


def _pure_assignments(body, variable):
    result = []
    for position, token in enumerate(body):
        if token != "⌜":
            continue
        end = body.index("⌝", position + 1)
        clause = _unwrap(body[position + 1:end])
        equals = top_level_positions(clause, {"="})
        if len(equals) == 1 and _unwrap(clause[:equals[0]]) == [variable]:
            result.append(clause[equals[0] + 1:])
    return result


def _check_forward_owner(row, binding):
    """Match full source values and arrays, including explicit lowering links."""
    source = Path(binding["path"]).read_text()
    body = _source_definition(binding)
    if any(resource.get("kind") not in {"register", "register_collection", "byte_array", "owned_parameter"}
           for resource in row["resources"]):
        raise ValueError("The forward row has an unsupported resource owner.")
    collections = [atom(body, position + 1)[0] for position, token in enumerate(body) if token == "reg_col"]
    expected_collections = [resource["value"] for resource in row["resources"]
                            if resource.get("kind") == "register_collection"]
    if (len(collections) != len(expected_collections) or
            [_canonical(value) for value in collections] !=
            [_canonical(_words(rocq_tokens(value))) for value in expected_collections]):
        raise ValueError("The source register collection differs from the bound forward row.")
    registers = _register_owners(body)
    expected = [resource for resource in row["resources"] if resource.get("kind") == "register"]
    if (len({resource["name"] for resource in expected}) != len(expected)
            or sorted(name for name, _ in registers) != sorted(resource["name"] for resource in expected)):
        raise ValueError("The forward row and its source declaration have different register owners.")
    evidence = []
    for resource in expected:
        words = [word for name, word in registers if name == resource["name"]]
        if len(words) != 1 or "value" not in resource:
            raise ValueError("The forward register lacks one typed source value.")
        actual = words[0]
        reported = _register_owners(_words(rocq_tokens('"' + resource["name"] + '" ↦ᵣ ' + resource["value"])))
        if len(reported) != 1:
            raise ValueError("The forward register value is not a supported bits owner.")
        wanted = _canonical(reported[0][1], word=True)
        matched = _canonical(actual, word=True) == wanted
        link = None
        if not matched:
            plain = _unwrap(actual)
            if len(plain) > 1 and plain[1] == ":":
                plain = plain[:1]
            links = _pure_assignments(body, plain[0]) if len(plain) == 1 else []
            matching = [value for value in links if _canonical(value) == wanted]
            if len(matching) == 1:
                matched, link = True, matching[0]
        if not matched:
            raise ValueError("The source register value differs from the bound forward row: " + resource["name"])
        evidence.append(dict(register=resource["name"], reported_value=resource["value"], source_word=actual,
                             source_lowering_equality=link))
    arrays = _array_owners(source, binding["declaration"])
    expected_arrays = [resource for resource in row["resources"] if resource.get("kind") == "byte_array"]
    if len(arrays) != len(expected_arrays):
        raise ValueError("The source array ownership differs from the bound forward row.")
    unmatched = list(arrays)
    array_fractions = []
    for resource in expected_arrays:
        matches = [owner for owner in unmatched
                   if _canonical(owner["address"], address=True) == _canonical(_words(rocq_tokens(resource["address"])), address=True)
                   and _canonical(owner["payload"]) == _canonical(_words(rocq_tokens(resource["value"]))) ]
        if len(matches) != 1:
            raise ValueError("The source array address or payload differs from the bound forward row.")
        array_fractions.append(dict(address=resource['address'], fraction=matches[0]['fraction']))
        unmatched.remove(matches[0])
    return dict(registers=evidence, arrays=expected_arrays, collections=expected_collections,
                array_fractions=array_fractions, exact_machine_resource_projection=True)


def _argument_catalog(row, dependencies):
    """Bind parameter names through source declarations, not target equations."""
    catalog = {}
    seen = set()
    for fact in row.get("execution_facts", []):
        origin = fact.get("source", {})
        text = origin.get("original_term")
        if not text or text in seen or not fact.get("expansion"):
            continue
        if any(key in row and origin.get(key) != row[key] for key in ("pc", "definition")):
            raise ValueError("The source argument certificate belongs to a different forward row.")
        seen.add(text)
        head, arguments = _application_arguments(text)
        expansions = [item for item in fact.get("expansion", [])
                      if item["declaration"] == head.rsplit(".", 1)[-1]]
        if not expansions:
            continue  # Primitive clauses do not supply named argument slots.
        if len(expansions) != 1:
            raise ValueError("The source application has ambiguous declaration provenance.")
        expansion = expansions[0]
        module = expansion["source"]["module"]
        if module not in dependencies:
            raise ValueError("The source application declaration is not bound: " + module)
        binding = dependencies[module]
        if binding["sha256"] != expansion["source"]["sha256"]:
            raise ValueError("The source declaration differs from the forward certificate.")
        reference = dict(path=binding["path"], sha256=binding["sha256"], declaration=expansion["declaration"])
        _source_declaration(reference)
        parameters = declared_binders(Path(binding["path"]).read_text(), expansion["declaration"])
        if len(parameters) != len(arguments):
            raise ValueError("The source application argument count differs from its declaration.")
        for parameter, argument in zip(parameters, arguments):
            catalog.setdefault(parameter["name"], []).append(dict(
                value=argument, type=parameter["type"], source=origin,
                declaration=reference, parameter=parameter["name"]))
    return catalog


def forward_witness_data(value, target_source, target, parameters, output_path):
    """Produce data from a retained pass row without a per-block slot table.

    The report supplies source applications. Resource templates supply only
    direct register roles. The actual values come from the forward owner.
    """
    from render_support import binders, expression, identifier, record, sequence

    record(value, {"name", "report", "pointer", "source_assertion", "declaration_sources", "resource_templates"},
           "forward witness input")
    name = identifier(value["name"], "forward data name")
    report = _bound_json(value["report"])
    row = _pointer(report, value["pointer"])
    if not isinstance(row, dict) or not {"parameters", "resources", "execution_facts"} <= row.keys():
        raise ValueError("The forward output row lacks typed source bindings.")
    source_assertion = value["source_assertion"]
    source_projection = _check_forward_owner(row, source_assertion)
    dependencies = {}
    for binding in sequence(value["declaration_sources"], "forward declarations"):
        record(binding, {"module", "path", "sha256"}, "forward declaration binding")
        module = identifier(binding["module"], "forward declaration module", qualified=True)
        if module in dependencies:
            raise ValueError("The forward declaration module is repeated.")
        dependencies[module] = binding
    catalog = _argument_catalog(row, dependencies)
    roles = {}
    for binding in sequence(value["resource_templates"], "source resource templates"):
        source = _source_declaration(binding)
        source_parameters = {item["name"]: item["type"] for item in
                             declared_binders(Path(binding["path"]).read_text(), binding["declaration"])}
        body = source[source.index(":=") + 1:]
        for register, word in _register_owners(body):
            if len(word) == 1 and word[0] in source_parameters:
                role = (register, _width(source_parameters[word[0]]))
                if word[0] in roles and roles[word[0]] != role:
                    raise ValueError("The source resource templates disagree on a direct register role.")
                roles[word[0]] = role
    layout = declared_witness_slots(target_source, target)
    arrays = {owner["payload"][0] for owner in _array_owners(target_source, target)
              if len(owner["payload"]) == 1}
    from join_witness_plan import planned_witnesses
    join_values, join_registers, join_plan = planned_witnesses(row, layout, roles)
    slots, pending, certificates = [], [], []
    pending_inputs = set()
    for slot in layout["remaining"]:
        bound = slot["name"]
        if bound in layout["register_slots"] or bound in roles:
            register = layout["register_slots"].get(bound, roles.get(bound, (None, None))[0])
            width = _width(slot["type"])
            if bound in roles and roles[bound][1] != width:
                raise ValueError("The direct source register role has a different width.")
            slots.append(dict(**slot, value=None, source=dict(kind="register", register=register,
                         width=width, provenance=source_assertion)))
        elif bound in arrays:
            slots.append(dict(**slot, value=None, source=dict(kind="array", provenance=source_assertion)))
        elif bound in join_values:
            pending.append((slot, join_values[bound]))
            pending_inputs.add(bound)
            certificates.append(dict(slot=bound, join_witness_plan=join_plan))
        else:
            candidates = catalog.get(bound, [])
            unique = {normalize_type(item["value"]) for item in candidates}
            if len(unique) != 1:
                raise ValueError("The forward output does not resolve one source argument for slot " + bound + ".")
            candidate = candidates[0]
            if len({normalize_type(item["type"]) for item in candidates}) != 1:
                raise ValueError("The source argument name has conflicting source types: " + bound)
            expression(candidate["value"], "forward source argument")
            pending.append((slot, candidate["value"]))
            certificates.append(dict(slot=bound, candidates=candidates))
    # Source locals cannot become invented entry parameters. Such a value needs
    # a registered source owner or an explicit future source-expression adapter.
    locals_ = {item["name"] for item in row.get("existentials", []) + row.get("lets", [])}
    if any(locals_.intersection(token for token, _ in rocq_tokens(term)) for _, term in pending):
        raise ValueError("A forward argument still refers to an uncaptured source local.")
    used = {token for _, term in pending for token, _ in rocq_tokens(term)}
    data_parameters = [dict(name=item["name"], type=item["type"]) for item in parameters if item["name"] in used]
    available = {item["name"] for item in data_parameters}
    source_parameters = {item["name"] for item in row["parameters"]}
    if (source_parameters & used) - available:
        raise ValueError("A forward argument needs a parameter absent from the mapping scope.")
    typed = "".join(" (" + bound + " : " + kind + ")" for bound, kind in binders(data_parameters))
    prefix, value_sources = [], []
    from witness_data import product
    input_type = product(['bv ' + str(width) + '%N' for _, width in join_registers])
    for slot, term in pending:
        definition = identifier(name + "_source_" + slot["name"], "forward value name")
        inputs = ' (source_words : ' + input_type + ')' if slot['name'] in pending_inputs else ''
        prefix.append("Definition " + definition + typed + inputs + " : " + expression(slot["type"], "slot type") +
                      " :=\n  " + term + ".\n")
        value_sources.append(dict(path=str(Path(output_path).resolve()), declaration=definition))
    prefix = "\n".join(prefix)
    digest = hashlib.sha256(prefix.encode()).hexdigest()
    for binding in value_sources:
        binding["sha256"] = digest
    for (slot, term), binding in zip(pending, value_sources):
        slots.append(dict(**slot, value=term, source=dict(kind="expression", provenance=binding)))
    index = {slot["name"]: slot for slot in slots}
    data = dict(name=name, parameters=data_parameters, source_assertion=source_assertion,
                value_sources=value_sources, slots=[index[slot["name"]] for slot in layout["remaining"]])
    return dict(data=data, prefix=prefix, source_texts={str(Path(output_path).resolve()): prefix},
                certificates=certificates, report=value["report"], pointer=value["pointer"],
                source_projection=source_projection)
