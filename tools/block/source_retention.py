"""Retain source-certified facts without extending the primitive fact grammar.

The caller supplies the existing machine-fact Catalog. Its source-bound
expansion must reproduce each retained leaf. Decoder leaves use a separate,
owned-array check; they never become primitive path clauses or proof evidence.
"""

from copy import deepcopy
import hashlib
import json
from pathlib import Path

from check_data_only_lemmas import rocq_tokens


def tokens(text):
    return tuple(value for value, _ in rocq_tokens(text))


def groups(values):
    result, index = [], 0
    while index < len(values):
        start = index
        if values[index] == "(":
            depth = 1
            index += 1
            while index < len(values) and depth:
                depth += (values[index] == "(") - (values[index] == ")")
                index += 1
            if depth:
                raise ValueError("A retained source expression has an unfinished group.")
        else:
            index += 1
        result.append(values[start:index])
    return result


def unwrap(values):
    values = tuple(values)
    while values:
        if len(values) > 2 and values[-2] == "%":
            values = values[:-2]
        elif values[0] == "(" and groups(values)[0] == values:
            values = values[1:-1]
        else:
            break
    return values


def typed_nat_literals(term):
    """Scope list-position literals without changing any other source bytes."""
    lexed = []
    for value, start in rocq_tokens(term):
        end = start + len(value)
        if (lexed and value.isdigit() and lexed[-1][0].isdigit()
                and lexed[-1][2] == start):
            previous, begin, _ = lexed.pop()
            lexed.append((previous + value, begin, end))
        else:
            lexed.append((value, start, end))
    edits = {}

    def word(index):
        return lexed[index][0]

    def parts(indices):
        result, offset = [], 0
        while offset < len(indices):
            begin = offset
            if word(indices[offset]) == "(":
                depth = 1
                offset += 1
                while offset < len(indices) and depth:
                    depth += (word(indices[offset]) == "(") - (word(indices[offset]) == ")")
                    offset += 1
                if depth:
                    raise ValueError("A typed source term has an unfinished group.")
            else:
                offset += 1
            result.append(indices[begin:offset])
        return result

    def unwrap_indices(indices):
        while indices and word(indices[0]) == "(" and parts(indices)[0] == indices:
            indices = indices[1:-1]
        return indices

    def literal(indices, position):
        indices = unwrap_indices(indices)
        if len(indices) != 1 or not word(indices[0]).isdigit():
            return
        value, start, end = lexed[indices[0]]
        edits[start] = dict(position=position, source=value,
                            rendered="(" + value + "%nat)", type="nat", end=end)

    def visit(indices):
        nodes = parts(indices)
        for index, node in enumerate(nodes):
            if (word(node[0]) == "(" and not
                    (index + 1 < len(nodes) and word(nodes[index + 1][0]) == "%")):
                visit(node[1:-1])
        for index, node in enumerate(nodes[:-1]):
            if len(node) == 1 and word(node[0]) in {
                    "firstn", "List.firstn", "skipn", "List.skipn"}:
                if not (index + 2 < len(nodes) and word(nodes[index + 2][0]) == "%"):
                    literal(nodes[index + 1], word(node[0]) + " index")
        equal = [index for index, node in enumerate(nodes)
                 if len(node) == 1 and word(node[0]) == "="]
        if len(equal) != 1:
            return
        index = equal[0]
        for side, other in (([item for node in nodes[:index] for item in node], nodes[index + 1:]),
                            ([item for node in nodes[index + 1:] for item in node], nodes[:index])):
            side = parts(unwrap_indices(side))
            if (len(side) == 2 and len(side[0]) == 1
                    and word(side[0][0]) in {"length", "List.length", "Datatypes.length"}
                    and len(other) == 1):
                literal(other[0], "list length equality")

    visit(list(range(len(lexed))))
    rendered = term
    for start, edit in sorted(edits.items(), reverse=True):
        rendered = rendered[:start] + edit["rendered"] + rendered[edit["end"]:]
    return rendered, [{key: value for key, value in edit.items() if key != "end"}
                      for _, edit in sorted(edits.items())]


def _leaf_identity(text):
    """Ignore only an explicit Z scope on integer literal tokens.

    Older source reports omit that annotation. Emit the replayed source leaf,
    not the report presentation. Other scopes and all grouping remain exact.
    """
    values, result, index = tokens(text), [], 0
    while index < len(values):
        if (values[index:index + 2] == ("%", "Z") and result and
                result[-1].isdigit()):
            index += 2
        else:
            result.append(values[index])
            index += 1
    return tuple(result)


def decoder_owner(term, resources):
    """Recognize an existing list decoder, with arbitrary source slice indices."""
    values = unwrap(tokens(term))
    depth, equal = 0, []
    for index, value in enumerate(values):
        depth += (value == "(") - (value == ")")
        if depth == 0 and value in {"->", "=>", "/", "\\", "∨", "∧", "↔"}:
            return None
        if value == "=" and depth == 0:
            equal.append(index)
    if len(equal) != 1:
        return None
    left = groups(unwrap(values[:equal[0]]))
    if len(left) != 2 or left[0] != ("littleEndian",):
        return None
    payload = unwrap(left[1])
    while True:
        parts = groups(payload)
        if parts and parts[0] in (("firstn",), ("List.firstn",),
                                  ("skipn",), ("List.skipn",)):
            if len(parts) != 3:
                return None
            payload = unwrap(parts[2])
        else:
            break
    owners = [resource for resource in resources
              if resource.get("kind") == "byte_array" and
              unwrap(tokens(resource["value"])) == payload]
    if len(owners) != 1:
        raise ValueError("A source decoder requires one exact owned byte array.")
    return deepcopy(owners[0])


def _source_clause(source, row, documents):
    identity = source["input"]
    path = Path(identity["path"])
    key = (str(path), identity["sha256"])
    if key not in documents:
        payload = path.read_bytes()
        if hashlib.sha256(payload).hexdigest() != identity["sha256"]:
            raise ValueError("A retained source document changed.")
        documents[key] = json.loads(payload)
    if (source["pc"], source["definition"]) != (row["pc"], row["definition"]):
        raise ValueError("A retained fact belongs to another source scope.")
    entries = [entry for entry in documents[key]["entries"]
               if entry["body"]["at"] == row["pc"]]
    if len(entries) != 1:
        raise ValueError("A retained fact has no unique source entry.")
    definitions = [item for item in entries[0]["body"]["additional_definitions"]
                   if item["suffix"] == row["definition"]]
    if len(definitions) != 1:
        raise ValueError("A retained fact has no unique source definition.")
    body = definitions[0]["body"]
    if body["existentials"] != row["existentials"] or body.get("lets", []) != row.get("lets", []):
        raise ValueError("A retained source binder scope changed.")
    for resource in row["resources"]:
        if resource.get("kind") == "byte_array" and resource not in body["components"]:
            raise ValueError("A retained source owner or fraction changed.")
    component = body["components"][source["component"]]
    if component["kind"] != "pure":
        raise ValueError("A retained fact does not name a source pure component.")
    clause = component["terms"][source["term_index"]]
    if (clause["term"]["value"] != source["original_term"] or
            clause["provenance"] != source["provenance"]):
        raise ValueError("A retained source clause or provenance changed.")
    return clause["term"]["value"]


def certified_execution_facts(report, row, catalog, *, refusals=None):
    """Replay the existing lowerer; retain its facts and owned decoder leaves."""
    candidates = [("/execution_facts/" + str(index), fact, "execution")
                  for index, fact in enumerate(row.get("execution_facts", []))]
    for index, fact in enumerate(report.get("unsupported", [])):
        source = fact.get("source", {})
        if (source.get("pc"), source.get("definition")) != (row["pc"], row["definition"]):
            continue
        if fact.get("expansion"):
            try:
                owner = decoder_owner(fact["unsupported"]["term"], row["resources"])
            except ValueError as error:
                if refusals is None:
                    raise
                refusals.append(dict(pointer="/unsupported/" + str(index),
                                     source=deepcopy(source), term=fact["unsupported"]["term"],
                                     reason=str(error)))
                continue
            if owner:
                candidates.append(("/unsupported/" + str(index), fact, "decoder"))
    documents, lowered, selected = {}, {}, {}
    previous = getattr(catalog, "owned_lists", ())
    catalog.owned_lists = [item["value"] for item in row["resources"]
                           if item["kind"] == "byte_array"]
    try:
        for pointer, fact, kind in candidates:
            source = fact["source"]
            original = _source_clause(source, row, documents)
            key = (source["component"], source["term_index"])
            if key not in lowered:
                lowered[key] = catalog.lower(original, row["parameters"] + row["existentials"])
            kept, omitted, expansion = lowered[key]
            if expansion != fact.get("expansion", []):
                raise ValueError("A retained source expansion certificate changed.")
            term = fact["term"] if kind == "execution" else fact["unsupported"]["term"]
            leaves = kept if kind == "execution" else [item["term"] for item in omitted]
            matches = [item for item in leaves if _leaf_identity(item) == _leaf_identity(term)]
            if len(matches) != 1:
                raise ValueError("The existing lowerer does not reproduce the source fact.")
            term = matches[0]
            owner = decoder_owner(term, row["resources"]) if kind == "decoder" else None
            if kind == "decoder":
                # This uses the existing value grammar, not the primitive clause grammar.
                catalog._values(list(tokens(term)),
                                {item["name"] for item in row["parameters"] + row["existentials"]})
            identity = tokens(term)
            item = selected.setdefault(identity, dict(term=term, kind=kind,
                                                       owners=[], source_references=[]))
            owners = [owner] if owner else [
                resource for resource in row["resources"]
                if resource.get("kind") == "byte_array" and
                any(identity[index:index + len(tokens(resource["value"]))] ==
                    tokens(resource["value"])
                    for index in range(len(identity)))]
            for resource in owners:
                if resource not in item["owners"]:
                    item["owners"].append(deepcopy(resource))
            item["source_references"].append(dict(pointer=pointer, source=deepcopy(source),
                                                   expansion=deepcopy(expansion)))
    finally:
        catalog.owned_lists = previous
    return list(selected.values())
