#!/usr/bin/env python3
"""Generate a selected function's CFG from words and explicit entry metadata."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/block"))
from function_names import FunctionNames, prefix_argument
from generate_table import control, structure, resolved_calls
from entry_bindings import check_binders, validate_design
from check_data_only_lemmas import rocq_commands, rocq_tokens, top_level_positions


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def checked_design_text(text):
    """Ignore only the producer hash while preserving every other byte."""
    decoder = json.JSONDecoder()

    def member_span(start, wanted):
        position = start + 1
        found = None
        keys = set()
        while True:
            while text[position].isspace():
                position += 1
            if text[position] == "}":
                break
            key, position = decoder.raw_decode(text, position)
            if key in keys:
                raise ValueError("The block design contains a duplicate JSON key.")
            keys.add(key)
            while text[position].isspace():
                position += 1
            if text[position] != ":":
                raise ValueError("The block design contains an invalid JSON member.")
            position += 1
            while text[position].isspace():
                position += 1
            value_start = position
            _, position = decoder.raw_decode(text, position)
            if key == wanted:
                found = (value_start, position)
            while text[position].isspace():
                position += 1
            if text[position] == ",":
                position += 1
        if found is None:
            raise ValueError(f"The block design omits {wanted}.")
        return found

    parsed = json.loads(text)
    value = parsed["hashes"]["generator_sha256"]
    if not isinstance(value, str) or len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError("The generator hash must contain 64 lowercase hexadecimal digits.")
    start = len(text) - len(text.lstrip())
    hashes_start, _ = member_span(start, "hashes")
    first, last = member_span(hashes_start, "generator_sha256")
    return text[:first] + '"<generator_sha256>"' + text[last:]


def address(value):
    return f"0x{value:08x}"


def selected_function(inventory, name):
    matches = [row for row in inventory["functions"] if row["name"] == name]
    if not matches:
        matches = [row for row in inventory["functions"]
                   if row["name"].rsplit(".", 1)[-1] == name]
    if len(matches) != 1:
        raise ValueError("The inventory must contain one selected function.")
    return matches[0]


def register_reads(row):
    mnemonic = row["mnemonic"]
    if mnemonic in {"lui", "auipc", "jal"}:
        return set()
    if mnemonic in {"addi", "andi", "xori", "sltiu", "slli", "lb", "lbu", "lhu", "ld", "jalr", "csrrs"}:
        return {row["rs1"]} - {0}
    if mnemonic in {"sd", "sh", "sb", "add", "sub", "or", "and", "sll", "sltu", "beq", "bne", "blt", "bge", "bltu", "bgeu"}:
        return {row["rs1"], row["rs2"]} - {0}
    raise ValueError(f"Unsupported selected instruction: {mnemonic}.")


def source_hashes(paths, root):
    result = {}
    for name in paths:
        path = Path(name)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("The source path must stay inside the workspace.")
        source = (root / path).resolve()
        if not source.is_relative_to(root.resolve()) or not source.is_file():
            raise ValueError(f"The bound source is unavailable: {name}.")
        result[name] = digest(source)
    return result


def validate_resources(design, root, name_prefix):
    """Keep legacy bindings strict and validate generated rows independently."""
    supported = [row for row in design["blocks"] if "support" in row]
    if not supported:
        validate_design(design, root)
        return
    from render_support import validate_support
    legacy = dict(design, blocks=[row for row in design["blocks"] if "support" not in row])
    validate_design(legacy, root)
    validate_support(design, root, name_prefix=name_prefix)


def verify_rendered_entries(design, root, *, name_prefix="decodeItem"):
    """Bind fresh declarations after rendering, without changing input metadata."""
    from render_support import support_declarations
    names = FunctionNames(name_prefix)
    path = Path("ZesuSsz/Generated") / names.module / "Entries.v"
    bindings = []
    for row in support_declarations(design):
        fields = deepcopy(row)
        declaration = row["entry_definition"].rsplit(".", 1)[-1]
        qualified = f"ZesuSsz.Generated.{names.module}.Entries.{declaration}"
        fields.update(entry_definition=qualified, resource_predicate=qualified,
                      source_hashes={str(path): digest(Path(root) / path)})
        check_binders(fields, root)
        bindings.append(fields)
    return bindings


def refresh_supported_sources(design, root, generated_paths):
    """Refresh primary, auxiliary, and shared inputs before renderer validation."""
    rows = []
    for block in design["blocks"]:
        if "support" not in block:
            continue
        rows.append(block)
        support = block["support"]
        if not isinstance(support, dict):
            raise ValueError("The entry support is not a record.")
        extras = support.get("additional_definitions", [])
        if not isinstance(extras, list):
            raise ValueError("The additional definitions are not a list.")
        for extra in extras:
            if not isinstance(extra, dict) or not isinstance(extra.get("declaration"), dict):
                raise ValueError("The additional definition lacks a declaration record.")
            rows.append(extra["declaration"])
    for row in rows:
        if generated_paths.intersection(row["source_hashes"]):
            raise ValueError("The profile binds a generated output as an input source.")
        row["source_hashes"] = source_hashes(row["source_hashes"], root)
    metadata = design.get("support")
    if isinstance(metadata, dict):
        groups = [metadata]
        if isinstance(metadata.get("bootstrap"), dict):
            groups.append(metadata["bootstrap"])
        for group in groups:
            if "source_hashes" not in group:
                continue
            if generated_paths.intersection(group["source_hashes"]):
                raise ValueError("The profile binds a generated output as an input source.")
            group["source_hashes"] = source_hashes(group["source_hashes"], root)


def compact_record(value, required, optional=(), *, label="compact record"):
    if (not isinstance(value, dict) or not set(required) <= value.keys()
            or value.keys() - set(required) - set(optional)):
        raise ValueError(f"The {label} has missing or unsupported fields.")
    return value


def compact_identifier(value, *, qualified=False):
    pattern = r"[A-Za-z_][A-Za-z0-9_']*"
    if qualified:
        pattern += r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
    if not isinstance(value, str) or not re.fullmatch(pattern, value):
        raise ValueError("The compact input contains an invalid identifier.")
    return value


def compact_global_index(closure, *, notation_owners=None, notation_scopes=None):
    """Index declaration ownership without reading declaration parameters."""
    compact_record(closure, {"sources"}, {"seeds", "namespace_roots", "edges",
                   "unresolved_imports", "source_count", "forbidden",
                   "external_toolchain", "status"}, label="source closure")
    if closure.get("unresolved_imports"):
        raise ValueError("The source closure has unresolved imports.")
    owners = {}
    notation_owners = {} if notation_owners is None else notation_owners
    notation_scopes = {} if notation_scopes is None else notation_scopes
    declarations = {"Definition", "Lemma", "Theorem", "Fact", "Corollary",
                    "Remark", "Proposition", "Record", "Class", "Inductive",
                    "Variant", "Fixpoint", "CoFixpoint", "Instance", "Axiom",
                    "Parameter", "Parameters", "Variable", "Variables"}
    for module, row in closure["sources"].items():
        compact_identifier(module, qualified=True)
        path = Path(row["path"])
        if ".Generated." in module or "Generated" in path.parts:
            raise ValueError("A generated declaration cannot supply constructor inputs.")
        if digest(path) != row["sha256"]:
            raise ValueError("A global source binding changed: " + module)
        glob = row.get("resolution_glob")
        if glob:
            if (digest(glob["path"]) != glob["sha256"]
                    or hashlib.md5(path.read_bytes()).hexdigest() != glob["source_md5"]
                    or Path(glob["path"]).read_text().splitlines()[0] != "DIGEST " + glob["source_md5"]):
                raise ValueError("A glob binding does not match its source.")
        nested_modules = []
        for command in rocq_commands(path.read_text()):
            values = [token for token, _ in command]
            if values[:1] == ["Module"] and len(values) == 2:
                nested_modules.append(values[1])
                continue
            if values[:1] == ["End"] and nested_modules and values[1:] == [nested_modules[-1]]:
                nested_modules.pop()
                continue
            prefix = ".".join([module, *nested_modules])
            if (values[:1] in (["Notation"], ["Abbreviation"]) and len(values) > 2
                    and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", values[1])):
                notation_owners.setdefault(values[1], set()).add(prefix + "." + values[1])
            if values[:1] == ["Infix"] and len(values) > 2:
                quoted = re.fullmatch(r'"([A-Za-z_][A-Za-z0-9_\']*)"', values[1])
                if quoted:
                    name = prefix + "." + quoted[1]
                    notation_owners.setdefault(quoted[1], set()).add(name)
                    if values[-2:-1] == [":"]:
                        notation_scopes[name] = values[-1]
            record_body = (values.index(":=") if ":=" in values
                           and {"Record", "Class"}.intersection(values) else len(values))
            for index, token in enumerate(values[:-1]):
                name = values[index + 1]
                declared = token in declarations
                field = (index > record_body and index + 2 < len(values) and values[index + 2] == ":"
                         and token in {"|", "{", ";"})
                constructor = (token in {"|", ":="}
                               and bool({"Inductive", "Variant"}.intersection(values)))
                if (declared or field or constructor) and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
                    owners.setdefault(name, set()).add(prefix + "." + name)
    return owners



def compact_import_visibility(closure, metadata):
    """Follow actual entry imports and source-bound Require Export commands."""
    sources = closure["sources"]
    edges = {}
    for edge in closure.get("edges", []):
        edges.setdefault((edge["from"], edge["requested"]), set()).add(edge["resolved"])

    def resolve(owner, requested):
        if requested in sources:
            return requested
        candidates = edges.get((owner, requested), set())
        if not candidates:
            # Rocq's From prefix can omit intermediate library directories.
            short = requested.rsplit(".", 1)[-1]
            prefix = requested.rsplit(".", 1)[0] + "." if "." in requested else ""
            candidates = {target for (source, name), targets in edges.items()
                          if source == owner and name.rsplit(".", 1)[-1] == short
                          for target in targets if target.startswith(prefix)}
        if not candidates:
            candidates = {module for module in sources if module.endswith("." + requested)}
        if len(candidates) != 1 or not candidates <= sources.keys():
            raise ValueError("An exported module has no unique source binding: " + requested)
        return next(iter(candidates))

    visible = set()
    for row in metadata.get("entries_imports", []):
        compact_record(row, {"mode", "module"})
        if row["module"] not in sources:
            raise ValueError("An entry import has no bound source: " + row["module"])
        if row["mode"] not in {"import", "export", "require"}:
            raise ValueError("The compact entry import has an unsupported mode.")
        if row["mode"] != "require":
            visible.add(row["module"])
    if "Coq.Init.Prelude" in sources:
        visible.add("Coq.Init.Prelude")
    pending = list(visible)
    while pending:
        owner = pending.pop()
        for command in rocq_commands(Path(sources[owner]["path"]).read_text()):
            values = [token for token, _ in command]
            if values[:1] == ["From"] and len(values) > 4 and values[2:4] == ["Require", "Export"]:
                requested = [values[1] + "." + name for name in values[4:]]
            elif values[:2] == ["Require", "Export"]:
                requested = values[2:]
            else:
                continue
            for name in requested:
                module = resolve(owner, name)
                if module not in visible:
                    visible.add(module)
                    pending.append(module)
    return visible



def compact_notation_choices(choices, closure, context):
    """Check explicit notation choices without reading historical proof artifacts."""
    if choices is None:
        return {}
    compact_record(choices, {"entries_imports", "notations"}, label="notation choices")
    if choices["entries_imports"] != context["shared"]["support_metadata"].get("entries_imports", []):
        raise ValueError("The notation choice import boundary changed.")
    selected = {}
    for name, choice in choices["notations"].items():
        compact_identifier(name)
        compact_record(choice, {"owner", "source_sha256", "visible_candidates"})
        owner = compact_identifier(choice["owner"], qualified=True)
        source = closure["sources"].get(owner)
        if source is None or source["sha256"] != choice["source_sha256"]:
            raise ValueError("The notation choice source binding changed.")
        visible = {item for item in context["notations"].get(name, set())
                   if item.rsplit(".", 1)[0] in context["visible_modules"]}
        if (sorted(visible) != choice["visible_candidates"] or owner + "." + name not in visible):
            raise ValueError("The visible notation candidates changed: " + name)
        selected[name] = owner + "." + name
    return selected


def _compact_global_candidates(identifier, context):
    short = identifier.rsplit(".", 1)[-1]
    constants = context["globals"].get(short, set())
    if identifier in context.get("local_declarations", {}).values():
        return {identifier}
    if "." in identifier:
        return {name for name in constants if name == identifier or name.endswith("." + identifier)}
    visible = context.get("visible_modules")
    if visible is not None:
        constants = {name for name in constants if name.rsplit(".", 1)[0] in visible}
    notations = context.get("notations", {}).get(short, set())
    if visible is not None:
        notations = {name for name in notations if name.rsplit(".", 1)[0] in visible}
    scopes = context.get("notation_scopes", {})
    notations = {name for name in notations if name not in scopes
                 or scopes[name] in context.get("active_scopes", ())}
    # A visible abbreviation preserves bare syntax and takes priority over constants.
    choice = context.get("notation_choices", {}).get(short)
    return {choice} if choice else notations or constants


def compact_registers(function, policy):
    """Retain ownership registers, rather than infer ownership from liveness."""
    if policy == "rv64_integer_abi_owned_full":
        caller = {5, 6, 7, *range(10, 18), *range(28, 32)}
        callee = {8, 9, *range(18, 28)}
        registers = caller | callee | {1, 2}
    elif policy == "resource_free_gprs":
        registers = set(range(32))
    elif policy == "decoded_function_accessed_gprs":
        registers = set()
        calls = resolved_calls(function)
        for row in function["rows"]:
            registers.update(register_reads(row))
            kind, _, _, _ = control(row, calls)
            if kind in {"plain", "load"}:
                registers.update({row["rd"]} - {0})
    else:
        raise ValueError("The compact input selects an unsupported register policy.")
    return [f"x{register}" for register in sorted(registers)]


def compact_free_identifiers(text, *, locals=(), reserved=(), ordered=False):
    """Track the supported lexical binders without changing expression bytes."""
    from render_support import expression
    expression(text, "compact expression")
    raw = rocq_tokens(text)
    tokens = []
    cursor = 0
    while cursor < len(raw):
        token, position = raw[cursor]
        if token == "0" and text[position:position + 2].lower() == "0x":
            numeral = re.match(r"0[xX][0-9a-fA-F]+", text[position:])
            if numeral is None:
                raise ValueError("The compact expression contains an invalid numeral.")
            tokens.append(numeral.group())
            cursor += 1
            while cursor < len(raw) and raw[cursor][1] < position + len(numeral.group()):
                cursor += 1
        else:
            tokens.append(token)
            cursor += 1
    protected = set(reserved)
    occurrences = []
    pairs = {"(": ")", "[": "]", "{": "}"}

    def matching(start, stop):
        stack = [pairs[tokens[start]]]
        for index in range(start + 1, stop):
            token = tokens[index]
            if token in pairs:
                stack.append(pairs[token])
            elif token in pairs.values():
                if not stack or token != stack.pop():
                    raise ValueError("The compact expression has mismatched delimiters.")
                if not stack:
                    return index
        raise ValueError("The compact expression has an unfinished delimiter.")

    def boundary(start, stop, wanted):
        index = start
        while index < stop:
            if tokens[index] in wanted:
                return index
            if tokens[index] in pairs:
                index = matching(index, stop)
            index += 1
        raise ValueError("The compact binder has no supported body delimiter.")

    def bind(names, scope):
        if any(name in scope or name in protected for name in names) or len(set(names)) != len(names):
            raise ValueError("A compact binder shadows a reserved or local name.")
        return scope | set(names)

    def typed(start, stop, scope):
        colon = boundary(start, stop, {":"})
        names = tokens[start:colon]
        if not names or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name) for name in names):
            raise ValueError("The compact binder uses unsupported pattern syntax.")
        found = scan(colon + 1, stop, scope)
        return found, bind(names, scope)

    def scan(start, stop, scope):
        found = set()
        index = start
        while index < stop:
            token = tokens[index]
            if token in {"exists", "forall", "fun"}:
                end = boundary(index + 1, stop, {"=>"} if token == "fun" else {","})
                cursor, nested = index + 1, set(scope)
                while cursor < end:
                    if tokens[cursor] == "(":
                        close = matching(cursor, end)
                        free, nested = typed(cursor + 1, close, nested)
                        cursor = close + 1
                    else:
                        free, nested = typed(cursor, end, nested)
                        cursor = end
                    found.update(free)
                return found | scan(end + 1, stop, nested)
            if token == "let":
                assignment = boundary(index + 1, stop, {":="})
                free, nested = typed(index + 1, assignment, scope)
                end = boundary(assignment + 1, stop, {"in"})
                found.update(free)
                found.update(scan(assignment + 1, end, scope))
                return found | scan(end + 1, stop, nested)
            if token in {"match", "fix", "cofix", "if", "∃", "∀", "λ"}:
                raise ValueError("The compact expression uses unsupported binder syntax.")
            if token in pairs:
                close = matching(index, stop)
                found.update(scan(index + 1, close, scope))
                index = close + 1
                continue
            record_label = (tokens[start:start + 1] == ["|"] and tokens[stop - 1:stop] == ["|"]
                            and index > start and tokens[index - 1] in {"|", ";"}
                            and tokens[index + 1:index + 2] == [":="])
            if (re.fullmatch(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*", token)
                    and token not in scope and token != "_" and not record_label
                    and not (index > start and tokens[index - 1] == "%")):
                found.add(token)
                occurrences.append(token)
            index += 1
        return found

    free = scan(0, len(tokens), set(locals))
    return list(dict.fromkeys(occurrences)) if ordered else free


def compact_reference(node, context, block):
    """Expand only reviewed typed references; never evaluate author code."""
    if not isinstance(node, dict) or "kind" not in node:
        raise ValueError("The compact reference must be a typed record.")
    kind = node["kind"]
    if kind == "local_declaration_ref":
        compact_record(node, {"kind", "role", "suffix"})
        key = (node["role"], node["suffix"])
        if key not in context.get("local_declarations", {}):
            raise ValueError("The local reference selects no attached declaration role.")
        return context["local_declarations"][key]
    if kind == "symbol_ref":
        compact_record(node, {"kind", "name"})
        if node["name"] not in context["symbols"]:
            raise ValueError("The compact reference names an unknown symbol.")
        return node["name"]
    if kind == "gpr_group_ref":
        compact_record(node, {"kind", "policy"})
        if node["policy"] != "function":
            raise ValueError("The compact register group must use the function policy.")
        return list(context["registers"])
    if kind == "block_pc_ref":
        compact_record(node, {"kind", "format"})
        if node["format"] != "hex8":
            raise ValueError("The compact block address requires hex8.")
        return address(block["start"])
    if kind == "global_ref":
        compact_record(node, {"kind", "name", "owner", "role"})
        name = compact_identifier(node["name"])
        owner = compact_identifier(node["owner"], qualified=True)
        if (node["role"] != "handwritten_helper"
                or re.search(r"(?:EntryAt|BodyAt)[0-9a-f]+$", name)):
            raise ValueError("An author body cannot select an entry reference.")
        qualified = owner + "." + name
        if qualified not in context["globals"].get(name, set()):
            raise ValueError("The global reference lacks a bound declaration owner.")
        return qualified
    if kind == "text":
        compact_record(node, {"kind", "value"})
        if not isinstance(node["value"], str):
            raise ValueError("A compact text reference requires a string.")
        return node["value"]
    if kind == "concat":
        compact_record(node, {"kind", "parts"})
        if not isinstance(node["parts"], list) or not node["parts"]:
            raise ValueError("A compact concatenation requires scalar parts.")
        parts = [compact_reference(part, context, block) for part in node["parts"]]
        if any(not isinstance(part, str) for part in parts):
            raise ValueError("A compact concatenation requires scalar parts.")
        return "".join(parts)
    if kind == "binder":
        compact_record(node, {"kind", "binder_kind", "binders", "body"})
        if node["binder_kind"] not in {"exists", "forall", "fun"}:
            raise ValueError("The compact reference uses an unsupported binder.")
        declarations = []
        for binder in node["binders"]:
            compact_record(binder, {"name", "type"})
            declarations.append(f"({compact_identifier(binder['name'])} : {binder['type']})")
        body = compact_reference(node["body"], context, block)
        if not declarations or not isinstance(body, str):
            raise ValueError("The compact binder requires a scalar body.")
        separator = " => " if node["binder_kind"] == "fun" else ", "
        return node["binder_kind"] + " " + " ".join(declarations) + separator + body
    raise ValueError("The compact input contains an unsupported reference kind.")


def compact_helper_statement(helper, closure):
    """Read explicit source syntax; leave omitted parameter types unresolved."""
    compact_identifier(helper, qualified=True)
    owners = [module for module in closure["sources"] if helper.startswith(module + ".")]
    if not owners:
        raise ValueError("A fact helper has no bound source module.")
    owner = max(owners, key=len)
    source = closure["sources"][owner]
    path = Path(source["path"])
    if ".Generated." in owner or "Generated" in path.parts or digest(path) != source["sha256"]:
        raise ValueError("A fact helper source is generated or differs from its binding.")
    text, nested, selected = path.read_text(), [], []
    declarations = {"Lemma", "Theorem", "Fact", "Corollary", "Remark", "Proposition"}
    for command in rocq_commands(text):
        values = [token for token, _ in command]
        if values[:1] == ["Module"] and len(values) == 2:
            nested.append(values[1])
        elif values[:1] == ["End"] and nested and values[1:] == [nested[-1]]:
            nested.pop()
        elif (len(values) > 1 and values[0] in declarations
              and ".".join([owner, *nested, values[1]]) == helper):
            selected.append(command)
    if len(selected) != 1:
        raise ValueError("A fact helper needs one source lemma declaration.")
    tokens = selected[0]
    values = [token for token, _ in tokens]
    colons = top_level_positions(values[2:], {":"})
    if not colons:
        raise ValueError("A fact helper has no result type delimiter.")
    boundary = colons[0] + 2

    def span(start, stop):
        if start >= stop:
            raise ValueError("A fact helper contains an empty type or proposition.")
        return text[tokens[start][1]:tokens[stop - 1][1] + len(tokens[stop - 1][0])].strip()

    parameters, names, index = [], set(), 2
    while index < boundary:
        opening = values[index]
        if opening in {"(", "{"}:
            depth, end = 1, index + 1
            while end < boundary and depth:
                depth += int(values[end] in {"(", "[", "{"})
                depth -= int(values[end] in {")", "]", "}"})
                end += 1
            if depth:
                raise ValueError("A fact helper parameter has an unbalanced type.")
            colon = top_level_positions(values[index + 1:end - 1], {":"})
            if len(colon) != 1:
                raise ValueError("A grouped fact parameter requires an explicit type.")
            split = index + 1 + colon[0]
            group, typ, implicit = values[index + 1:split], span(split + 1, end - 1), opening == "{"
            index = end
        else:
            group, typ, implicit = [opening], None, False
            index += 1
        if not group:
            raise ValueError("A fact helper parameter group has no name.")
        for name in group:
            compact_identifier(name)
            if name in names:
                raise ValueError("A fact helper repeats a parameter name.")
            names.add(name)
            parameters.append({"name": name, "type": typ, "implicit": implicit})
    body = values[boundary + 1:]
    if body[:1] in (["forall"], ["∀"], ["fun"], ["let"]):
        raise ValueError("A fact helper uses an unsupported outer binder.")
    arrows = [boundary + 1 + index for index in top_level_positions(body, {"->"})]
    starts = [boundary + 1, *[index + 1 for index in arrows]]
    stops = [*arrows, len(tokens)]
    clauses = [span(start, stop) for start, stop in zip(starts, stops)]
    return {"source": deepcopy(source), "parameters": parameters,
            "premises": clauses[:-1], "conclusion": clauses[-1]}


def _compact_fact_choices(shared, closure, evidence):
    """Construct fact records from source clauses and explicit author choices."""
    if "fact_choices" not in shared:
        if "registry_defaults" in shared or "fact_name_policy" in shared or evidence is not None:
            raise ValueError("Registry inputs require fact choices.")
        return
    metadata = shared["support_metadata"]
    if "facts" in metadata:
        raise ValueError("Constructed facts cannot coexist with copied fact records.")
    registry = "ZesuSsz.Automation.FactRegistry."
    expected = {"class": "lithium.simpl_classes.SimplAnd", "class_arguments": ["conclusion", "True"],
        "constructor": registry + "zesu_simpl_and_fact",
        "constructor_application": "@" + registry + "zesu_simpl_and_fact conclusion helper_proof",
        "evidence_class": registry + "ZesuFactEvidence", "evidence_projection": registry + "zesu_fact_evidence",
        "evidence_application": "@" + registry + "zesu_fact_evidence premise_type evidence_binder"}
    defaults = shared.get("registry_defaults")
    attributes = {"locality", "priority", "explicit_lemma"}
    if isinstance(defaults, dict) and "constructor_role" in defaults:
        compact_record(defaults, attributes | {"constructor_role"}, label="registry defaults")
        if defaults["constructor_role"] != "simpl_and_true_fact":
            raise ValueError("The registry constructor role is unsupported.")
        defaults = {key: defaults[key] for key in attributes} | deepcopy(expected)
    else:
        compact_record(defaults, attributes | expected.keys(), label="registry defaults")
    if any(defaults[key] != value for key, value in expected.items()):
        raise ValueError("The registry defaults differ from the supported fact constructor.")
    if defaults["locality"] not in {"local", "global", "export"} or type(defaults["explicit_lemma"]) is not bool:
        raise ValueError("The registry locality or explicit lemma flag is invalid.")
    evidence = compact_record(evidence or {}, {"signature_packets", "type_spellings", "spelling_choices"},
                              label="registry evidence")

    def bound_json(binding):
        compact_record(binding, {"path", "sha256"}, label="registry binding")
        if digest(Path(binding["path"])) != binding["sha256"]:
            raise ValueError("A registry evidence file differs from its binding.")
        return json.loads(Path(binding["path"]).read_text())

    signatures = {}
    for binding in evidence["signature_packets"]:
        packet = bound_json(binding)
        for field in ("query", "stdout"):
            item = packet[field]
            if digest(Path(item["path"])) != item["sha256"]:
                raise ValueError("A printed signature differs from its retained evidence.")
        for row in packet["signatures"]:
            helper = row["helper"]
            if helper in signatures:
                raise ValueError("Printed signatures repeat a helper.")
            signatures[helper] = row
    spellings = {}
    for row in bound_json(evidence["type_spellings"])["shared_type_spellings"]:
        key = hashlib.sha256(row["printed_type"].encode()).hexdigest()
        if key != row["printed_type_sha256"] or key in spellings or not row["spelling"].strip():
            raise ValueError("A printed type spelling is repeated or invalid.")
        spellings[key] = row["spelling"]
    alternatives = {}
    for row in bound_json(evidence["spelling_choices"]):
        helper = row["helper"]
        if helper in alternatives or len(row["spelling_choices"]) != 1:
            raise ValueError("Conclusion spelling choices repeat a helper or field.")
        alternative = row["spelling_choices"][0]
        compact_record(alternative, {"field", "source_clause_sha256", "source_sha256", "spelling"})
        if alternative["field"] != "conclusion":
            raise ValueError("Only explicit conclusion spellings are supported.")
        alternatives[helper] = alternative
    choices = shared["fact_choices"]
    if not isinstance(choices, list):
        raise ValueError("Fact choices must be an ordered list.")
    policy = None
    if "fact_name_policy" in shared:
        policy = compact_record(shared["fact_name_policy"],
            {"activation_names", "instance_suffix_default"}, label="fact name policy")
        if policy != {"activation_names": "source_position_hfact",
                      "instance_suffix_default": "RegisteredFact"}:
            raise ValueError("The fact name policy is unsupported.")
    facts, names, used_alternatives = [], set(), set()
    for choice in choices:
        required = {"helper", "activation_premises"}
        optional = {"priority", "locality", "explicit_lemma"}
        if policy is None:
            required.add("instance_name")
        else:
            optional.add("instance_suffix")
        compact_record(choice, required, optional, label="fact choice")
        helper = choice["helper"]
        statement = compact_helper_statement(helper, closure)
        if policy is None:
            name = compact_identifier(choice["instance_name"])
        else:
            suffix = compact_identifier(choice.get("instance_suffix", policy["instance_suffix_default"]))
            name = compact_identifier(helper.rsplit(".", 1)[-1] + suffix)
        if name in names:
            raise ValueError("Fact choices repeat an instance name.")
        names.add(name)
        parameters = deepcopy(statement["parameters"])
        if any(row["type"] is None for row in parameters):
            signature = signatures.get(helper)
            if signature is None or signature["source"]["sha256"] != statement["source"]["sha256"]:
                raise ValueError("An omitted fact type lacks a source-bound printed signature.")
            binders = signature["binders"]
            if [row["name"] for row in binders] != [row["name"] for row in parameters]:
                raise ValueError("Printed signature binders differ from source binders.")
            for parameter, binder in zip(parameters, binders):
                key = hashlib.sha256(binder["type"].encode()).hexdigest()
                if key != binder["type_sha256"]:
                    raise ValueError("A printed binder type differs from its hash.")
                if parameter["type"] is None:
                    if key not in spellings:
                        raise ValueError("An omitted fact type lacks an explicit spelling.")
                    parameter["type"] = spellings[key]
        selected, binder_names, premises = {}, {row["name"] for row in parameters}, []
        for activation in choice["activation_premises"]:
            compact_record(activation, {"source_premise"} if policy else {"name", "source_premise"},
                           {"name"} if policy else (), label="activation premise")
            index = activation["source_premise"]
            if type(index) is not int or not 0 <= index < len(statement["premises"]):
                raise ValueError("An activation premise is repeated, absent, or out of range.")
            default = "Hfact" + str(index + 1)
            bound = compact_identifier(activation.get("name", default))
            if policy and "name" in activation and re.fullmatch(r"Hfact[0-9]+", bound):
                raise ValueError("A selected activation name copies or conflicts with the fact name policy.")
            if (index in selected or bound in binder_names or bound == name):
                raise ValueError("An activation premise is repeated, absent, or out of range.")
            selected[index] = bound
            binder_names.add(bound)
            premises.append({"name": bound, "type": statement["premises"][index], "implicit": False})
        if set(selected) != set(range(len(statement["premises"]))):
            raise ValueError("A fact choice omits an activation premise.")
        conclusion = statement["conclusion"]
        if helper in alternatives:
            alternative = alternatives[helper]
            if (alternative["source_sha256"] != statement["source"]["sha256"]
                    or alternative["source_clause_sha256"] != hashlib.sha256(conclusion.encode()).hexdigest()
                    or not alternative["spelling"].strip()):
                raise ValueError("A conclusion spelling differs from its source binding.")
            conclusion = alternative["spelling"]
            used_alternatives.add(helper)
        fact = {key: choice.get(key, defaults[key]) for key in ("locality", "priority", "explicit_lemma")}
        if (fact["priority"] is not None and (type(fact["priority"]) is not int or fact["priority"] < 0)
                or fact["locality"] not in {"local", "global", "export"}
                or type(fact["explicit_lemma"]) is not bool):
            raise ValueError("A fact choice has invalid registration attributes.")
        arguments = [row["name"] for row in parameters if not row["implicit"] or fact["explicit_lemma"]]
        arguments.extend("@" + registry + "zesu_fact_evidence _ " + selected[index]
                         for index in range(len(statement["premises"])))
        fact.update(name=name, parameters=parameters, premises=premises, conclusion=conclusion,
                    lemma=helper, arguments=arguments)
        facts.append(fact)
    if used_alternatives != alternatives.keys():
        raise ValueError("A conclusion spelling selects an unknown fact helper.")
    metadata["facts"] = facts


def _compact_support_choices(shared, closure, globals_index, root, registry_evidence=None):
    """Construct ordered imports and bootstrap fields from explicit selections."""
    shared = deepcopy(shared)
    metadata = shared["support_metadata"]
    if "version" in metadata:
        raise ValueError("The compact schema supplies the support version; omit the copied version field.")
    metadata["version"] = 1
    _compact_fact_choices(shared, closure, registry_evidence)
    imports = compact_record(shared.get("import_choices", {}), set(),
                             {"entries_imports", "registrations_imports"}, label="import choices")
    for field, choices in imports.items():
        if field in metadata:
            raise ValueError("Constructed imports cannot coexist with copied import records.")
        if not isinstance(choices, list):
            raise ValueError("Import choices must be an ordered list.")
        records, seen = [], set()
        for choice in choices:
            row = {"module": choice, "mode": "import"} if isinstance(choice, str) else deepcopy(choice)
            compact_record(row, {"module"}, {"mode"}, label="import choice")
            module = compact_identifier(row["module"], qualified=True)
            mode = row.setdefault("mode", "import")
            if module not in closure["sources"] or mode not in {"import", "export", "require"}:
                raise ValueError("An import choice lacks a bound module or supported mode.")
            if module in seen:
                raise ValueError("Import choices repeat a module.")
            seen.add(module)
            records.append(row)
        metadata[field] = records
    if "bootstrap_choices" not in shared:
        return shared
    choices = shared["bootstrap_choices"]
    if not isinstance(choices, list):
        raise ValueError("Bootstrap choices must be an ordered list.")
    bootstrap = metadata.setdefault("bootstrap", {})
    if {"imports", "source_hashes", "unfold_sources", "regcol_unfold_sources"}.intersection(bootstrap):
        raise ValueError("Constructed bootstrap fields cannot coexist with copied fields.")
    if "isla.automation" not in closure["sources"]:
        raise ValueError("Bootstrap construction requires the bound isla.automation module.")
    selected = {"unfold": [], "regcol": []}
    hashes, seen = {}, set()
    imports = [{"module": "isla.automation", "mode": "import"}]
    imported = {"isla.automation"}
    for choice in choices:
        compact_record(choice, set(), {"unfold", "regcol"}, label="bootstrap choice")
        if len(choice) != 1:
            raise ValueError("A bootstrap choice requires exactly one predicate role.")
        role, name = next(iter(choice.items()))
        compact_identifier(name, qualified=True)
        if name not in globals_index.get(name.rsplit(".", 1)[-1], set()):
            raise ValueError("A bootstrap predicate has no bound declaration: " + name)
        if (role, name) in seen:
            raise ValueError("Bootstrap choices repeat a predicate role.")
        seen.add((role, name))
        owners = [module for module in closure["sources"] if name.startswith(module + ".")]
        if not owners:
            raise ValueError("A bootstrap predicate has no defining source.")
        owner = max(owners, key=len)
        source = closure["sources"][owner]
        relative = owner.replace(".", "/") + ".v"
        path = Path(root) / relative
        if not path.is_file() or digest(path) != source["sha256"]:
            raise ValueError("A bootstrap source differs from its bound project source.")
        selected[role].append(name)
        hashes[relative] = source["sha256"]
        if owner not in imported:
            imports.append({"module": owner, "mode": "import"})
            imported.add(owner)
    bootstrap.update(imports=imports, source_hashes=hashes, unfold_sources=selected["unfold"],
                     regcol_unfold_sources=selected["regcol"])
    return shared


def _compact_metadata_bodies(author):
    """Expand explicit shared metadata without changing resource expressions."""
    profiles = author["shared"].get("metadata_profiles", {})
    if not isinstance(profiles, dict):
        raise ValueError("Shared metadata profiles must be named records.")
    fields = {"lets", "existentials", "loop", "continuation"}
    for name, profile in profiles.items():
        compact_identifier(name)
        compact_record(profile, set(), fields, label="shared metadata profile")

    def expand(body):
        if not isinstance(body, dict):
            raise ValueError("A compact body must be a record.")
        body = deepcopy(body)
        if "metadata_profile" in body:
            name = body.pop("metadata_profile")
            if not isinstance(name, str) or name not in profiles:
                raise ValueError("A body selects an unknown metadata profile.")
            if profiles[name].keys() & body.keys():
                raise ValueError("Shared metadata cannot coexist with local metadata fields.")
            body.update(deepcopy(profiles[name]))
        for auxiliary in body.get("additional_definitions", []):
            if isinstance(auxiliary, dict) and "body" in auxiliary:
                auxiliary["body"] = expand(auxiliary["body"])
        return body

    return [expand(body) for body in author["bodies"]]


def _compact_typed_author(author):
    """Expand the seven v2 field shapes only inside selected resource bodies."""
    author = deepcopy(author)

    def field(value, shapes, label):
        if not isinstance(value, dict):
            raise ValueError(f"A typed {label} must be a record.")
        for keys, constructed in shapes:
            if set(value) == keys:
                value.update(constructed)
                return
        raise ValueError(f"A typed {label} has unsupported fields.")

    def component(value):
        if not isinstance(value, dict):
            raise ValueError("A typed resource component must be a record.")
        if "predicate" in value:
            field(value["predicate"], [
                ({"owner", "name"}, {"kind": "global_ref", "role": "handwritten_helper"}),
                ({"suffix"}, {"kind": "local_declaration_ref", "role": "entry_variant"})], "predicate")
        if "registers" in value:
            field(value["registers"], [({"policy"}, {"kind": "gpr_group_ref"})], "register group")
        if "terms" in value:
            if not isinstance(value["terms"], list):
                raise ValueError("Typed resource terms must be an ordered list.")
            for pair in value["terms"]:
                compact_record(pair, {"term", "provenance"}, label="typed resource term")
                field(pair["provenance"], [
                    ({"source"}, {"kind": "data"}),
                    ({"from_block", "from_instruction"}, {"kind": "path"})], "provenance")
                field(pair["term"], [
                    ({"value"}, {"kind": "text"}),
                    ({"parts"}, {"kind": "concat"})], "text term")
        if "alternatives" in value:
            if not isinstance(value["alternatives"], list):
                raise ValueError("Typed resource alternatives must be an ordered list.")
            for alternative in value["alternatives"]:
                component(alternative)

    def body(value):
        if not isinstance(value, dict) or not isinstance(value.get("components"), list):
            raise ValueError("A typed body requires an ordered component list.")
        for item in value["components"]:
            component(item)
        auxiliary_bodies = value.get("additional_definitions", [])
        if not isinstance(auxiliary_bodies, list):
            raise ValueError("Typed auxiliaries must be an ordered list.")
        for auxiliary in auxiliary_bodies:
            if not isinstance(auxiliary, dict) or "body" not in auxiliary:
                raise ValueError("A typed auxiliary requires a body.")
            body(auxiliary["body"])

    if not isinstance(author["bodies"], list):
        raise ValueError("The compact bodies must be an ordered list.")
    for selected in author["bodies"]:
        body(selected)
    author["schema"] = "p1b.compact-profile.v1"
    return author


def validate_author_data(author, inventory, name, *, root=ROOT, source_closure, notation_choices=None,
                         registry_evidence=None):
    """Validate compact selections before constructing any entry interfaces."""
    compact_record(author, {"schema", "function", "symbols", "shared", "bodies"}, label="author input")
    if author["schema"] not in ("p1b.compact-profile.v1", "p1b.compact-profile.v2"):
        raise ValueError("The compact profile schema is unsupported.")
    if author["schema"] == "p1b.compact-profile.v2":
        author = _compact_typed_author(author)
    selected = selected_function(inventory, name)
    function = compact_record(author["function"], {"inventory_name", "prefix", "root",
                              "handwritten_owner", "register_policy", "profile_layout"},
                              {"parameter_order", "helper_family_owners"})
    if function["inventory_name"] != selected["name"] or function["prefix"] != prefix_argument(selected["name"]):
        raise ValueError("The compact function identity differs from the selected inventory.")
    compact_identifier(function["handwritten_owner"], qualified=True)
    if function["profile_layout"] not in {"sparse_cfg_placeholders", "expanded_cfg"}:
        raise ValueError("The compact profile layout is unsupported.")
    if function.get("parameter_order", "root_registers_catalog") not in {"root_registers_catalog", "semantic_anchor"}:
        raise ValueError("The compact parameter order is unsupported.")
    if (function["register_policy"] == "resource_free_gprs") != (function.get("parameter_order") == "semantic_anchor"):
        raise ValueError("Free resource registers require semantic anchor ordering.")
    compact_record(function["root"], {"name", "type"})
    registers = compact_registers(selected, function["register_policy"])
    if not isinstance(author["symbols"], list):
        raise ValueError("The compact symbols must be an ordered list.")
    symbols = {}
    for item in [function["root"], *author["symbols"]]:
        compact_record(item, {"name", "type"})
        symbol = compact_identifier(item["name"])
        if symbol in symbols or symbol in registers or re.fullmatch(r"x\d+", symbol):
            raise ValueError("The compact symbol catalog repeats or shadows a register.")
        if not isinstance(item["type"], str) or not item["type"].strip():
            raise ValueError("The compact symbol requires an explicit type.")
        symbols[symbol] = item["type"]
    shared = compact_record(author["shared"], {"design_metadata", "support_metadata",
                            "input_digest_sources", "lets", "continuation", "loop_annotations",
                            "historical_design_metadata"},
                            {"row_source_paths", "source_policies", "helper_summaries", "introduction_defaults", "derived_table_metadata",
                             "annotation_defaults", "selection_order", "import_choices", "bootstrap_choices",
                              "registry_defaults", "fact_choices", "fact_name_policy", "metadata_profiles", "continuation_summaries"})
    if {"blocks", "function", "support"}.intersection(shared["design_metadata"]):
        raise ValueError("Shared metadata cannot contain copied entry interfaces.")
    if "unfold_entries" in shared["support_metadata"]:
        raise ValueError("The constructor must derive Unfold names.")
    if set(shared["historical_design_metadata"]) - {"hashes"}:
        raise ValueError("Historical compact metadata contains executable fields.")
    if not isinstance(author["bodies"], list):
        raise ValueError("The compact bodies must be an ordered list.")
    starts = {block["start"] for block in selected["blocks"]}
    attached = set()
    bodies = _compact_metadata_bodies(author)
    for body in bodies:
        compact_record(body, {"at", "components"}, {"lets", "continuation", "existentials", "loop",
                       "source_policy", "introduction", "additional_definitions", "annotations"},
                       label="body attachment")
        if not isinstance(body["at"], str) or not re.fullmatch(r"0x[0-9a-f]{8}", body["at"]):
            raise ValueError("A body attachment requires an exact CFG address.")
        pc = int(body["at"], 0)
        if pc not in starts or pc in attached:
            raise ValueError("Compact bodies must cover each CFG block exactly once.")
        attached.add(pc)
    if attached != starts:
        raise ValueError("Compact bodies must cover each CFG block exactly once.")
    notation_owners, notation_scopes = {}, {}
    globals_index = compact_global_index(source_closure, notation_owners=notation_owners,
                                         notation_scopes=notation_scopes)
    shared = _compact_support_choices(shared, source_closure, globals_index, root, registry_evidence)
    context = {"function": selected, "selection": function, "symbols": symbols, "bodies": bodies,
               "registers": registers, "globals": globals_index, "notations": notation_owners,
               "notation_scopes": notation_scopes,
               "active_scopes": shared["support_metadata"].get("entries_scopes", []),
                "root": Path(root), "shared": shared, "source_closure": source_closure,
               "visible_modules": compact_import_visibility(source_closure, shared["support_metadata"])}
    context["notation_choices"] = compact_notation_choices(notation_choices, source_closure, context)
    for family, owner in function.get("helper_family_owners", {}).items():
        compact_identifier(family, qualified=True)
        compact_identifier(owner, qualified=True)
        if (family not in source_closure["sources"]
                and family not in globals_index.get(family.rsplit(".", 1)[-1], set())):
            raise ValueError("A helper family lacks a bound source module or declaration.")
    for paths in shared.get("source_policies", {}).values():
        if (not isinstance(paths, list) or not paths or any(not isinstance(path, str) for path in paths)
                or len(set(paths)) != len(paths)):
            raise ValueError("A source policy requires a nonempty ordered list of unique paths.")
        source_hashes(paths, Path(root))
    return context


def _compact_expand(value, context, block):
    references = {"symbol_ref", "gpr_group_ref", "block_pc_ref", "global_ref", "text", "binder", "entry_ref", "concat", "local_declaration_ref"}
    if isinstance(value, dict):
        if value.get("kind") in references:
            return compact_reference(value, context, block)
        if value.get("kind") == "register_resources":
            compact_record(value, {"kind", "registers", "value_constructor"})
            group = value["registers"]
            if not isinstance(group, dict) or group.get("kind") != "gpr_group_ref":
                raise ValueError("Register resources require the function register group.")
            registers = compact_reference(group, context, block)
            constructor = compact_identifier(value["value_constructor"], qualified=True)
            candidates = _compact_global_candidates(constructor, context)
            if len(candidates) != 1:
                raise ValueError("The register value constructor has no unique bound owner.")
            return [{"kind": "register", "name": register,
                     "value": f"{constructor} {register}"} for register in registers]
        return {key: _compact_expand(item, context, block) for key, item in value.items()}
    if isinstance(value, list):
        result = []
        for item in value:
            expanded = _compact_expand(item, context, block)
            if isinstance(item, dict) and item.get("kind") in {"gpr_group_ref", "register_resources"}:
                result.extend(expanded)
            else:
                result.append(expanded)
        return result
    return deepcopy(value)


def _compact_body_symbols(support, context):
    semantic = context["selection"].get("parameter_order") == "semantic_anchor"
    protected = set() if semantic else set(context["symbols"]) | set(context["registers"])
    local_names = set() if semantic else {context["selection"]["root"]["name"], *context["registers"]}
    free = set()

    def expression(text, scope):
        free.update(compact_free_identifiers(text, locals=scope, reserved=protected))

    for binding in support.get("lets", []):
        compact_record(binding, {"name", "type", "value"})
        name = compact_identifier(binding["name"])
        if name in protected or name in local_names:
            raise ValueError("A shared let shadows a compact symbol.")
        expression(binding["type"], local_names)
        expression(binding["value"], local_names)
        local_names.add(name)
    for binding in support["existentials"]:
        compact_record(binding, {"name", "type"})
        name = compact_identifier(binding["name"])
        if name in protected or name in local_names:
            raise ValueError("An existential shadows a compact symbol.")
        expression(binding["type"], local_names)
        local_names.add(name)

    def visit(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key in {"provenance", "lets", "existentials", "additional_definitions"}:
                    continue
                if value.get("kind") == "base" and key in {"arguments", "memory_deltas"}:
                    if key == "arguments":
                        from render_support import base_arguments
                        for argument in base_arguments(value):
                            expression(argument, local_names)
                    continue
                if key in {"predicate", "value", "address", "length", "term", "conclusion", "type"} and isinstance(item, str):
                    expression(item, local_names)
                elif key == "arguments" and isinstance(item, list):
                    for argument in item:
                        expression(argument, local_names)
                else:
                    visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(support)
    selected = free & (set(context["symbols"]) | (set(context["registers"]) if semantic else set()))
    for identifier in free - selected:
        candidates = _compact_global_candidates(identifier, context)
        if len(candidates) != 1:
            raise ValueError("An expression has an unresolved or ambiguous global: " + identifier)
    return selected




def _compact_helper_summaries(context):
    packet = context["shared"].get("helper_summaries")
    if packet is None:
        return {}
    compact_record(packet, {"schema", "summaries"}, label="helper summaries")
    if packet["schema"] != "p1b.resource-helper-summary.v1":
        raise ValueError("The helper summary schema is unsupported.")
    result = {}
    for item in packet["summaries"]:
        compact_record(item, {"schema", "helper", "exposure", "resource_existentials"},
                       {"source", "source_binding_role", "boundary", "validation"},
                       label="resource helper summary")
        if ("source" in item) == ("source_binding_role" in item):
            raise ValueError("A helper summary requires exactly one source record or source binding role.")
        if item["schema"] != packet["schema"] or item["exposure"] != "top_level_spatial_existentials":
            raise ValueError("The helper summary exposure is unsupported.")
        helper = compact_reference(item["helper"], context, {})
        if "source_binding_role" in item:
            if item["source_binding_role"] != "from_bound_definition":
                raise ValueError("The helper summary source binding role is unsupported.")
            if "source_closure" not in context:
                raise ValueError("The helper summary requires an immutable source binding.")
            _, _, binding, original, start, stop = _compact_definition(helper, context)
            stop = original.index(".", stop) + 1
            source = {"path": item["helper"]["owner"].replace(".", "/") + ".v",
                      "sha256": binding["sha256"],
                      "definition_sha256": hashlib.sha256(original[start:stop].encode()).hexdigest(),
                      "line_start": original.count("\n", 0, start) + 1,
                      "line_end": original.count("\n", 0, stop) + 1}
        else:
            source = item["source"]
        source = compact_record(source, {"path", "sha256", "definition_sha256", "line_start", "line_end"})
        path = context["root"] / source["path"]
        if (path.suffix != ".v" or ".".join(Path(source["path"]).with_suffix("").parts)
                != item["helper"]["owner"] or digest(path) != source["sha256"]):
            raise ValueError("The helper summary source binding changed.")
        text = path.read_text()
        commands = [command for command in rocq_commands(text)
                    if [token for token, _ in command[:2]] == ["Definition", item["helper"]["name"]]]
        if len(commands) != 1:
            raise ValueError("The helper summary has no unique Definition command.")
        command = commands[0]
        start = command[0][1]
        stop = text.index(".", command[-1][1] + len(command[-1][0])) + 1
        declaration = text[start:stop]
        if hashlib.sha256(declaration.encode()).hexdigest() != source["definition_sha256"]:
            raise ValueError("The helper summary definition binding changed.")
        if (text.count("\n", 0, start) + 1 != source["line_start"]
                or text.count("\n", 0, stop) + 1 != source["line_end"]):
            raise ValueError("The helper summary source lines changed.")
        body = declaration.split(":=", 1)[1].strip()
        match = re.match(r"\(\s*∃\s*\(([^():]+):\s*([^()]+)\)\s*,", body)
        if match is None or "(*" in body:
            raise ValueError("The helper summary has an unsupported spatial binder shape.")
        names = match[1].split()
        type_ = match[2].strip()
        resources = item["resource_existentials"]
        if ([resource["name"] for resource in resources] != names
                or any(resource["type"] != type_ for resource in resources)):
            raise ValueError("The helper summary changes its existential binders.")
        for resource in resources:
            compact_record(resource, {"name", "type", "register_resource"})
            register = compact_record(resource["register_resource"], {"kind", "name", "value"})
            if register["kind"] != "register" or not re.fullmatch(r"x(?:[0-9]|[12][0-9]|3[01])", register["name"]):
                raise ValueError("The helper summary selects an invalid register resource.")
            occurrence = ('"' + register["name"] + '" ↦ᵣ ' + register["value"])
            if (body.count(occurrence) != 1 or register["value"] != "RVal_Bits " + resource["name"]):
                raise ValueError("The helper summary changes its register resource.")
        if helper in result:
            raise ValueError("A helper summary is repeated.")
        result[helper] = names
    return result


def _compact_table_metadata(rows, context):
    policies = context["shared"].get("derived_table_metadata")
    if policies is None:
        return {}
    compact_record(policies, {"register_existentials", "internal_existentials"})
    if policies != {"register_existentials": "primary_top_level_register_resources_and_helper_summaries",
                    "internal_existentials": "primary_loop_bodies_with_equal_ordered_existentials"}:
        raise ValueError("The table metadata derivation policy is unsupported.")
    summaries = _compact_helper_summaries(context)
    registers, loop_rows = {}, []
    for row in rows:
        support = row["support"]
        used = set()
        hidden = []
        for component in support["components"]:
            if component["kind"] == "register":
                used.update(compact_free_identifiers(component["value"]))
            elif component["kind"] in {"base", "application"}:
                hidden.extend(summaries.get(component["predicate"], []))
        names = [item["name"] for item in support["existentials"] if item["name"] in used] + hidden
        if len(set(names)) != len(names):
            raise ValueError("The table derivation repeats a hidden existential name.")
        if names:
            registers[row["entry_pc"]] = names
        if support["loop"] is not None:
            loop_rows.append((row["entry_pc"], [item["name"] for item in support["existentials"]]))
    result = {"register_existentials": registers}
    if loop_rows:
        if any(names != loop_rows[0][1] for _, names in loop_rows):
            raise ValueError("The table format requires equal ordered loop existential names.")
        result["internal_existentials"] = {"entry_pcs": [pc for pc, _ in loop_rows], "binders": loop_rows[0][1]}
    return result


def _compact_introduction(row, body, context):
    if "introduction" not in body:
        return None
    choice = compact_record(body["introduction"], {"helper", "facts"})
    defaults = compact_record(context["shared"]["introduction_defaults"], {
        "class", "iris_contexts", "parameter_policy", "parameter_renames", "type_spelling_policy",
        "instance_name_rule", "explicit_lemma", "priority", "locality"})
    if (defaults["parameter_policy"] != "constructed_entry_binders"
            or defaults["instance_name_rule"] != "PREFIX + Entry + shortHex4(parentPC) + IntroductionRegistered"):
        raise ValueError("The introduction derivation policy is unsupported.")
    parameters = [{"name": defaults["parameter_renames"].get(item["name"], item["name"]),
                   "type": defaults["type_spelling_policy"].get(item["type"], item["type"]), "implicit": False}
                  for item in row["binders"]]
    if len({item["name"] for item in parameters}) != len(parameters):
        raise ValueError("An introduction parameter rename collides with another parameter.")
    arguments = [item["name"] for item in parameters]
    prefix = context["selection"]["prefix"]
    name = f"{prefix}Entry{int(row['entry_pc'], 0) & 0xffff:04x}IntroductionRegistered"
    module = f"ZesuSsz.Generated.{FunctionNames(prefix).module}.Entries"
    return {"name": name, "iris_contexts": deepcopy(defaults["iris_contexts"]),
            "parameters": parameters, "class": defaults["class"],
            "source": {"predicate": module + "." + row["entry_definition"].rsplit(".", 1)[-1],
                       "arguments": list(arguments)},
            "facts": compact_reference(choice["facts"], context, {}),
            "lemma": compact_reference(choice["helper"], context, {}), "arguments": arguments,
            "explicit_lemma": defaults["explicit_lemma"], "priority": defaults["priority"],
            "locality": defaults["locality"]}


def _compact_anchor(components):
    """Select the approved resource anchor without interpreting helper parameters."""
    from render_support import base_arguments
    for kind in ("base", "application"):
        matches = [node for node in components if node["kind"] == kind]
        if matches:
            if len(matches) != 1:
                raise ValueError("The resource anchor is ambiguous.")
            node = matches[0]
            return node, base_arguments(node) if kind == "base" else node["arguments"]
    matches = [node for node in components if node["kind"] == "disjunction"]
    if (len(matches) != 1 or not matches[0]["alternatives"]
            or matches[0]["alternatives"][0]["kind"] != "application"):
        raise ValueError("The resource body has no supported unambiguous anchor.")
    node = matches[0]["alternatives"][0]
    return node, node["arguments"]


def _compact_entry_binders(author, support, used, context):
    if context["selection"].get("parameter_order") != "semantic_anchor":
        return [deepcopy(context["selection"]["root"]),
                *({"name": reg, "type": "bv 64"} for reg in context["registers"]),
                *(deepcopy(symbol) for symbol in author["symbols"] if symbol["name"] in used)]
    _, arguments = _compact_anchor(support["components"])
    locals_ = {item["name"] for item in support.get("lets", []) + support["existentials"]}
    ordered = []
    for argument in arguments:
        for symbol in compact_free_identifiers(argument, locals=locals_, ordered=True):
            if symbol in used and symbol not in ordered:
                ordered.append(symbol)
    ordered.extend(reg for reg in context["registers"] if reg in used and reg not in ordered)
    ordered.extend(symbol for symbol in context["symbols"] if symbol in used and symbol not in ordered)
    return [{"name": symbol, "type": context["symbols"].get(symbol, "bv 64")} for symbol in ordered]


def construct_entry_fields(author, block, inventory, name, *, root=ROOT, source_closure, context=None,
                           notation_choices=None):
    """Construct binders and references from a CFG block and its resource body."""
    context = context or validate_author_data(author, inventory, name, root=root, source_closure=source_closure,
                                              notation_choices=notation_choices)
    bodies = {int(body["at"], 0): body for body in context["bodies"]}
    body = bodies[block["start"]]
    context = dict(context)
    context["local_declarations"] = {}
    auxiliary = body.get("additional_definitions", [])
    for item in auxiliary:
        compact_record(item, {"position", "role", "suffix", "handwritten_owner", "body"},
                       label="auxiliary role")
        if item["position"] not in {"before", "after"} or item["role"] not in {"entry_variant", "body"}:
            raise ValueError("An auxiliary role or placement is unsupported.")
        suffix = item["suffix"]
        if not isinstance(suffix, str) or (suffix and compact_identifier(suffix) != suffix):
            raise ValueError("An auxiliary suffix is invalid.")
        if item["role"] == "body" and suffix:
            raise ValueError("A body role cannot select an entry-variant suffix.")
        compact_identifier(item["handwritten_owner"], qualified=True)
        compact_record(item["body"], {"components", "source_policy"}, {"lets", "existentials", "loop", "continuation"},
                       label="auxiliary body")
        key = (item["role"], suffix)
        if key in context["local_declarations"]:
            raise ValueError("The parent body repeats an auxiliary declaration role.")
        stem = "BodyAt" if item["role"] == "body" else "EntryAt"
        prefix = context["selection"]["prefix"]
        context["local_declarations"][key] = (f"ZesuSsz.Generated.{FunctionNames(prefix).module}.Entries."
                                              f"{prefix}{stem}{block['start']:08x}{suffix}")
    result = _compact_body_fields(author, body, block, context)
    for item in auxiliary:
        nested = item["body"]
        declaration = _compact_body_fields(author, nested, block, context,
                                           role=item["role"], suffix=item["suffix"],
                                           owner=item["handwritten_owner"])
        declaration.pop("entry_pc")
        result["support"]["additional_definitions"].append({"position": item["position"], "declaration": declaration})
    return result


def _compact_definition(helper, context):
    """Read a bound, nonrecursive definition with explicit typed parameters."""
    compact_identifier(helper, qualified=True)
    owner, name = helper.rsplit(".", 1)
    source = context["source_closure"]["sources"].get(owner)
    if source is None or ".Generated." in owner or "Generated" in Path(source["path"]).parts:
        raise ValueError("A continuation helper has no handwritten source binding.")
    path = Path(source["path"])
    if digest(path) != source["sha256"]:
        raise ValueError("A continuation helper source binding changed.")
    text = path.read_text()
    commands = [command for command in rocq_commands(text)
                if [token for token, _ in command[:2]] == ["Definition", name]]
    if len(commands) != 1:
        raise ValueError("A continuation helper requires one Definition command.")
    command = commands[0]
    values = [token for token, _ in command]
    colons = top_level_positions(values[2:], {":"})
    if not colons:
        raise ValueError("A continuation helper requires an explicit result type.")
    boundary = colons[0] + 2
    parameters, index = [], 2
    while index < boundary:
        implicit = values[index] == "`"
        if implicit:
            index += 1
        if values[index] != ("{" if implicit else "("):
            raise ValueError("A continuation helper has unsupported binders.")
        opening, depth, stop = index, 1, index + 1
        while stop < boundary and depth:
            depth += int(values[stop] in {"(", "[", "{"})
            depth -= int(values[stop] in {")", "]", "}"})
            stop += 1
        if depth:
            raise ValueError("A continuation helper has unbalanced binders.")
        if implicit:
            if values[opening + 1] != "!":
                raise ValueError("A continuation helper has unsupported implicit binders.")
        else:
            split = top_level_positions(values[opening + 1:stop - 1], {":"})
            if len(split) != 1:
                raise ValueError("A continuation helper requires typed parameters.")
            names = values[opening + 1:opening + 1 + split[0]]
            if not names:
                raise ValueError("A continuation helper has an empty parameter group.")
            for parameter in names:
                compact_identifier(parameter)
                if parameter in parameters:
                    raise ValueError("A continuation helper repeats a parameter.")
                parameters.append(parameter)
        index = stop
    assignments = top_level_positions(values[boundary + 1:], {":="})
    if len(assignments) != 1:
        raise ValueError("A continuation helper has no supported definition body.")
    start = boundary + 2 + assignments[0]
    stop = command[-1][1] + len(command[-1][0])
    body = text[command[start][1]:stop].strip()
    return parameters, body, source, text, command[0][1], stop


def _compact_application(text):
    """Split one application without interpreting binders or pure propositions."""
    tokens = rocq_tokens(text)
    values = [token for token, _ in tokens]
    if not values or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", values[0]):
        raise ValueError("A continuation requires a single application.")
    arguments, index = [], 1
    while index < len(tokens):
        start, stop = index, index + 1
        if values[index] == "(":
            depth = 1
            while stop < len(tokens) and depth:
                depth += int(values[stop] == "(") - int(values[stop] == ")")
                stop += 1
            if depth:
                raise ValueError("A continuation application has unbalanced arguments.")
            start, end = index + 1, stop - 1
        elif re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", values[index]):
            end = stop
        else:
            raise ValueError("A continuation application has unsupported arguments.")
        if start == end or any(value in {"fun", "let", "forall", "∀", "∃", "⌜", "⌝", "∗"}
                               for value in values[start:end]):
            raise ValueError("A continuation application contains unsupported binding syntax.")
        arguments.append(text[tokens[start][1]:tokens[end - 1][1] + len(tokens[end - 1][0])])
        index = stop
    return values[0], arguments


def _compact_substitute(text, parameters, arguments):
    if len(parameters) != len(arguments):
        raise ValueError("A continuation helper application has the wrong arity.")
    replacements = dict(zip(parameters, arguments))
    tokens = rocq_tokens(text)
    result = text
    for token, position in reversed(tokens):
        if token in replacements:
            argument = replacements[token]
            value = argument if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", argument) else "(" + argument + ")"
            result = result[:position] + value + result[position + len(token):]
    return result


def _compact_continuation(selector, body, support, context, block):
    compact_record(selector, {"mode", "resource_component", "placement", "order"},
                   {"helper_summary"}, label="continuation projection")
    index = selector["resource_component"]
    if type(index) is not int or not 0 <= index < len(body["components"]):
        raise ValueError("A continuation projection selects an invalid authored component.")
    expanded = [_compact_expand(component, context, block) for component in body["components"]]
    selected = expanded[index]
    if not isinstance(selected, dict):
        raise ValueError("A continuation projection requires one expanded application.")
    output_index = sum(len(item) if isinstance(item, list) else 1 for item in expanded[:index])
    placement = selector["placement"]
    if placement == "explicit":
        if selected.get("kind") != "continuation" or "helper_summary" in selector:
            raise ValueError("An explicit continuation projection requires a continuation component.")
        predicate, arguments = selected["predicate"], deepcopy(selected["arguments"])
    elif placement == "included_in_base":
        from render_support import base_arguments
        if selected.get("kind") != "base":
            raise ValueError("An included continuation projection requires a base component.")
        helper = selector.get("helper_summary")
        summaries = context["shared"].get("continuation_summaries", {})
        if helper not in summaries or selected["predicate"] != helper:
            raise ValueError("An included continuation requires its selected helper summary.")
        summary = summaries[helper]
        if isinstance(summary, dict) and "binding_role" in summary:
            compact_record(summary, {"binding_role", "selected_application", "explicit_alias_steps"},
                           label="continuation binding role")
            if summary["binding_role"] != "from_bound_definition":
                raise ValueError("The continuation binding role is unsupported.")
            _, _, source, original, start, stop = _compact_definition(helper, context)
            first = original.count("\n", 0, start) + 1
            last = original.count("\n", 0, stop) + 1
            declaration = ''.join(original.splitlines(True)[first - 1:last])
            summary = {"helper": helper,
                "source": {"path": source["path"], "sha256": source["sha256"]},
                "definition": {"line_start": first, "line_end": last,
                    "sha256": hashlib.sha256(declaration.encode()).hexdigest()},
                "selected_application": summary["selected_application"],
                "explicit_alias_steps": summary["explicit_alias_steps"]}
        summary = compact_record(summary, {"helper", "source", "definition",
            "selected_application", "explicit_alias_steps"}, label="continuation summary")
        if summary["helper"] != helper:
            raise ValueError("A continuation summary changes its helper identity.")
        parameters, text, source, original, start, stop = _compact_definition(helper, context)
        binding, definition = summary["source"], summary["definition"]
        if (source["sha256"] != binding["sha256"] or digest(Path(binding["path"])) != binding["sha256"]
                or hashlib.sha256(''.join(original.splitlines(True)[definition["line_start"] - 1:
                    definition["line_end"]]).encode()).hexdigest() != definition["sha256"]
                or original.count("\n", 0, start) + 1 != definition["line_start"]
                or original.count("\n", 0, stop) + 1 != definition["line_end"]):
            raise ValueError("A continuation summary source or definition binding changed.")
        if not text.endswith(")%I") or not text.startswith("("):
            raise ValueError("A continuation helper requires top-level spatial resources.")
        spatial = text[1:-3]
        tokens = rocq_tokens(spatial)
        values = [token for token, _ in tokens]
        separators, depth, pure = [], 0, 0
        for offset, value in enumerate(values):
            if value == "⌜":
                pure += 1
            elif value == "⌝":
                pure -= 1
            elif not pure:
                if value == "∗" and depth == 0:
                    separators.append(offset)
                depth += int(value in {"(", "[", "{"}) - int(value in {")", "]", "}"})
        if depth or pure or any(value in {"∀", "∃", "fun", "let"} for value in values):
            raise ValueError("A continuation helper contains unsupported spatial binders.")
        application = compact_record(summary["selected_application"], {"callee", "require_unique"})
        callee = compact_identifier(application["callee"], qualified=True)
        if application["require_unique"] is not True:
            raise ValueError("A continuation summary must require a unique application.")
        matches = []
        for left, right in zip([0, *[p + 1 for p in separators]], [*separators, len(tokens)]):
            part = spatial[tokens[left][1]:tokens[right - 1][1] + len(tokens[right - 1][0])].strip()
            if part.split(maxsplit=1)[0] in {callee, callee.rsplit(".", 1)[-1]}:
                matches.append(part)
        if len(matches) != 1:
            raise ValueError("A continuation helper has no unique selected spatial application.")
        actual = base_arguments(selected)
        head, arguments = _compact_application(_compact_substitute(matches[0], parameters, actual))
        if (head != callee and context["globals"].get(head, set()) != {callee}):
            raise ValueError("The selected continuation application has an ambiguous source name.")
        predicate = callee
        aliases = summary["explicit_alias_steps"]
        if (not isinstance(aliases, list) or any(not isinstance(alias, str) for alias in aliases)
                or len(aliases) != len(set(aliases))):
            raise ValueError("Continuation alias steps repeat or recurse.")
        visited = set()
        for alias in aliases:
            if alias != predicate:
                raise ValueError("A continuation alias step does not match the selected application.")
            formals, alias_body, _, _, _, _ = _compact_definition(alias, context)
            head, arguments = _compact_application(_compact_substitute(alias_body, formals, arguments))
            owner = alias.rsplit(".", 1)[0]
            predicate = head if "." in head else owner + "." + head
            visited.add(alias)
            if predicate in visited:
                raise ValueError("A continuation alias step recurses.")
            if head != predicate and context["globals"].get(head, set()) != {predicate}:
                raise ValueError("A continuation alias has an ambiguous source name.")
        if predicate not in context["globals"].get(predicate.rsplit(".", 1)[-1], set()):
            raise ValueError("A projected continuation has no bound declaration.")
    else:
        raise ValueError("The continuation projection placement is unsupported.")
    return {"mode": placement, "predicate": predicate, "arguments": arguments,
            "order": selector["order"], "component_index": output_index}


def _compact_body_fields(author, body, block, context, *, role="primary_entry", suffix="", owner=None):
    shared = context["shared"]
    support = {"version": 1, "existentials": body.get("existentials", []),
               "components": body["components"], "loop": body.get("loop"),
               "additional_definitions": [], "continuation": body.get("continuation", shared["continuation"])}
    if "lets" in body or shared["lets"]:
        support["lets"] = body.get("lets", shared["lets"])
    support = _compact_expand(support, context, block)
    if support["loop"] is not None:
        invariant = support["loop"]["invariant"]
        if "resource_component" in invariant and set(invariant) != {"resource_component"}:
            raise ValueError("A selected loop invariant cannot copy its predicate or arguments.")
        if set(invariant) in ({"component_index"}, {"resource_component"}):
            index = invariant.get("resource_component", invariant.get("component_index"))
            if type(index) is not int or not 0 <= index < len(support["components"]):
                raise ValueError("The loop invariant selects no resource component.")
            component = support["components"][index]
            if component["kind"] not in {"base", "application"}:
                raise ValueError("The loop invariant requires an application resource.")
            from render_support import base_arguments
            invariant.pop("resource_component", None)
            invariant.update(component_index=index, predicate=component["predicate"], arguments=base_arguments(component)
                             if component["kind"] == "base" else deepcopy(component["arguments"]))
    continuation = support["continuation"]
    if continuation["mode"] == "from_resource_component":
        continuation = _compact_continuation(continuation, body, support, context, block)
        support["continuation"] = continuation
    elif continuation["mode"] in {"explicit", "included_in_base"}:
        kind = "base" if continuation["mode"] == "included_in_base" else "continuation"
        matches = [index for index, component in enumerate(support["components"])
                   if component.get("kind") == kind
                   and (kind == "base" or (component.get("predicate") == continuation["predicate"]
                                          and component.get("arguments") == continuation["arguments"]))]
        if len(matches) != 1:
            raise ValueError("A continuation requires one matching resource component.")
        continuation["component_index"] = matches[0]
    used = _compact_body_symbols(support, context)
    binders = _compact_entry_binders(author, support, used, context)
    prefix = context["selection"]["prefix"]
    selected_owner = owner
    owner = owner or context["selection"]["handwritten_owner"]
    if selected_owner is None and context["selection"].get("parameter_order") == "semantic_anchor":
        anchor, _ = _compact_anchor(support["components"])
        family = anchor["predicate"].rsplit(".", 1)[0]
        owners = context["selection"].get("helper_family_owners", {})
        owner = owners.get(anchor["predicate"], owners.get(family, owner))
    stem = "BodyAt" if role == "body" else "EntryAt"
    reference = owner + f".{prefix}{stem}{block['start']:08x}{suffix}"
    paths = shared.get("row_source_paths", [])
    if "source_policy" in body:
        if body["source_policy"] not in shared.get("source_policies", {}):
            raise ValueError("The body selects an unknown source policy.")
        paths = shared["source_policies"][body["source_policy"]]
    elif isinstance(paths, dict):
        compact_record(paths, {"function_entry", "other_blocks"}, label="row source policy")
        paths = paths["function_entry" if block["start"] == context["function"]["entry"] else "other_blocks"]
    return {"entry_pc": address(block["start"]), "entry_definition": reference,
            "binders": binders, "arguments": [item["name"] for item in binders],
            "resource_predicate": reference,
            "source_hashes": source_hashes(paths, context["root"]), "support": support}


def _compact_cfg_fields(function):
    """Derive author-profile CFG fields without consulting an entry declaration."""
    calls = resolved_calls(function)
    rows = {row["pc"]: row for row in function["rows"]}
    blocks = sorted(function["blocks"], key=lambda block: block["start"])
    incoming = {block["start"]: [] for block in blocks}
    uses, writes, kinds = {}, {}, {}
    backedges = {(int(edge["from"], 0), int(edge["to"], 0))
                 for loop in function["loops"] for edge in loop["backward_edges"]}
    for block in blocks:
        pc = block["start"]
        uses[pc], writes[pc] = set(), set()
        for at in range(pc, block["end"], 4):
            row = rows[at]
            kind, _, _, _ = control(row, calls)
            uses[pc].update(register_reads(row) - writes[pc])
            if kind in {"plain", "load"}:
                writes[pc].update({row["rd"]} - {0})
        tail = rows[block["end"] - 4]
        kind, targets, guards, _ = control(tail, calls)
        kinds[pc] = kind
        for target, guard in zip(targets, guards):
            if target not in incoming:
                raise ValueError("A CFG edge targets an undeclared block.")
            edge_kind = ("loop_backedge" if (tail["pc"], target) in backedges else
                         "conditional" if kind == "branch" else "jump" if kind == "jump" else
                         "call" if kind == "call" else "fallthrough")
            incoming[target].append({"from_block": address(pc), "from_instruction": address(tail["pc"]),
                                     "source_terminator": tail["mnemonic"], "kind": edge_kind,
                                     "path_condition": guard})
    live = {pc: set() for pc in incoming}
    while True:
        previous = deepcopy(live)
        for block in reversed(blocks):
            pc = block["start"]
            outgoing = set().union(*(live[target] for target in block["successors"]))
            live[pc] = uses[pc] | (outgoing - writes[pc])
        if live == previous:
            break
    for pc, edges in incoming.items():
        edges.sort(key=lambda edge: (edge["from_block"], edge["from_instruction"]))
        if pc == function["entry"]:
            edges.insert(0, {"from_block": "caller", "from_instruction": None,
                             "kind": "entry", "path_condition": {"op": "true"}})
    return incoming, live, kinds


def _compact_row_annotations(row, body, context):
    """Keep author descriptions explicit; derive declaration references from roles."""
    defaults = compact_record(context["shared"].get("annotation_defaults", {}), set(),
                              {"needed_resources", "rocq_entry"}, label="annotation defaults")
    annotations = compact_record(body.get("annotations", {}), set(),
                                 {"entry_class", "needed_resources", "branch_constant_facts",
                                  "return_clause", "incoming_edge_variants"}, label="body annotations")
    if "entry_class" in annotations:
        row["entry_class"] = compact_identifier(annotations["entry_class"])
    summary_fields = {"system_register_collection", "input", "output", "stack", "return_continuation"}
    for fields in [defaults.get("needed_resources", {}), annotations.get("needed_resources", {})]:
        compact_record(fields, set(), summary_fields, label="resource descriptions")
        if any(not isinstance(value, str) or not value.strip() for value in fields.values()):
            raise ValueError("A resource description requires nonempty text.")
        row["needed_resources"].update(deepcopy(fields))
    module = f"ZesuSsz.Generated.{FunctionNames(context['selection']['prefix']).module}.Entries"
    if "rocq_entry" in defaults:
        choice = compact_record(defaults["rocq_entry"], {"kind", "role", "namespace"})
        if choice != {"kind": "constructed_declaration_ref", "role": "entry", "namespace": "generated"}:
            raise ValueError("The resource summary requires a constructed generated entry reference.")
        row["needed_resources"]["rocq_entry"] = module + "." + row["entry_definition"].rsplit(".", 1)[-1]
    if "branch_constant_facts" in annotations:
        facts = annotations["branch_constant_facts"]
        if (not isinstance(facts, dict) or not facts or any(
                not re.fullmatch(r"x(?:[0-9]|[12][0-9]|3[01])", key) or type(value) is not int
                for key, value in facts.items())):
            raise ValueError("Branch facts require explicit register names and integer values.")
        row["branch_constant_facts"] = deepcopy(facts)
    if "return_clause" in annotations:
        clause = compact_record(annotations["return_clause"], {"contract", "cases"})
        if (not isinstance(clause["contract"], str) or not clause["contract"].strip()
                or not isinstance(clause["cases"], list) or not clause["cases"]
                or any(not isinstance(case, dict) or not case for case in clause["cases"])):
            raise ValueError("A return description requires a contract and ordered cases.")
        row.setdefault("return_clause", {}).update(deepcopy(clause))
    selections = annotations.get("incoming_edge_variants", [])
    if not isinstance(selections, list):
        raise ValueError("Incoming edge selections require an ordered list.")
    selected = set()
    for selection in selections:
        compact_record(selection, {"from_block", "declaration"})
        origin = selection["from_block"]
        matches = [edge for edge in row["incoming_edges"] if edge["from_block"] == origin]
        if len(matches) != 1 or origin in selected:
            raise ValueError("An incoming edge selection is missing, duplicate, or ambiguous.")
        selected.add(origin)
        reference = compact_record(selection["declaration"], {"kind", "role", "suffix", "namespace"})
        if (reference["kind"] != "local_declaration_ref" or reference["role"] != "entry_variant"
                or reference["namespace"] not in {"handwritten", "generated"}):
            raise ValueError("An incoming edge requires a local entry-variant role.")
        suffix = compact_identifier(reference["suffix"])
        expected = f"{context['selection']['prefix']}EntryAt{int(row['entry_pc'], 0):08x}{suffix}"
        declarations = [item["declaration"]["entry_definition"]
                        for item in row["support"]["additional_definitions"]
                        if item["declaration"]["entry_definition"].rsplit(".", 1)[-1] == expected]
        if len(declarations) != 1:
            raise ValueError("The incoming edge selects no unique attached declaration role.")
        matches[0]["resource_alternative"] = (declarations[0] if reference["namespace"] == "handwritten"
                                              else module + "." + expected)


def construct_profile(inventory, name, author, *, root=ROOT, source_closure, notation_choices=None,
                      registry_evidence=None):
    """Construct an expanded profile; expected profiles are not constructor inputs."""
    context = validate_author_data(author, inventory, name, root=root, source_closure=source_closure,
                                   notation_choices=notation_choices, registry_evidence=registry_evidence)
    function, shared = context["function"], context["shared"]
    metadata = deepcopy(shared["design_metadata"])
    metadata.update(deepcopy(shared["historical_design_metadata"]))
    metadata["function"] = function["name"]
    expanded = context["selection"]["profile_layout"] == "expanded_cfg"
    incoming, live, kinds = _compact_cfg_fields(function)
    if expanded:
        metadata.update(source_inventory=shared["input_digest_sources"]["inventory_sha256"],
                        entry_pc=address(function["entry"]), end_pc_exclusive=address(function["end"]),
                        instruction_count=len(function["rows"]), block_count=len(function["blocks"]),
                        conditional_branch_count=function["branch_count"], loop_count=function["loop_count"],
                        edge_condition_scope="register values before the source block's final instruction",
                        condition_ops={"eq": "equal bits", "ne": "unequal bits", "s_lt": "signed less than",
                                       "s_ge": "signed greater or equal", "u_lt": "unsigned less than",
                                       "u_ge": "unsigned greater or equal", "true": "unconditional"})
    output = []
    for block in sorted(function["blocks"], key=lambda block: block["start"]):
        pc = block["start"]
        row = construct_entry_fields(author, block, inventory, name, root=root,
                                     source_closure=source_closure, context=context)
        row.update(end_pc_exclusive=address(block["end"]) if expanded else None,
                   incoming_edges=incoming[pc] if expanded else [],
                   successor_pcs=[address(target) for target in block["successors"]] if expanded else [])
        if expanded:
            row.update(entry_class="declared_entry", needed_resources={
                "register_live_in_hint": [f"x{reg}" for reg in sorted(live[pc])],
                "rocq_entry": row["entry_definition"]})
        if kinds[pc] == "return":
            row["return_clause"] = {"return_instruction_pc": address(block["end"] - 4) if expanded else None}
        if expanded:
            _compact_row_annotations(row, next(body for body in context["bodies"] if int(body["at"], 0) == pc), context)
        elif shared.get("annotation_defaults") or any(body.get("annotations") for body in context["bodies"]):
            raise ValueError("Body annotations require the expanded CFG profile layout.")
        for annotation in shared["loop_annotations"]:
            compact_record(annotation, {"loop_index", "annotation"})
            index = annotation["loop_index"]
            if type(index) is not int or not 0 <= index < len(function["loops"]):
                raise ValueError("The compact loop annotation selects an absent loop.")
            if int(function["loops"][index]["minimum_pc"], 0) == pc:
                row["invariant_hint"] = _compact_expand(annotation["annotation"], context, block)
        output.append(row)
    metadata["blocks"] = output
    metadata["support"] = deepcopy(shared["support_metadata"])
    names = []
    for row in output:
        attached = row["support"]["additional_definitions"]
        names.extend(item["declaration"]["entry_definition"].rsplit(".", 1)[-1]
                     for item in attached if item["position"] == "before")
        names.append(row["entry_definition"].rsplit(".", 1)[-1])
        names.extend(item["declaration"]["entry_definition"].rsplit(".", 1)[-1]
                     for item in attached if item["position"] == "after")
    metadata["support"]["unfold_entries"] = names
    bodies = {body["at"]: body for body in context["bodies"]}
    introductions = {row["entry_pc"]: _compact_introduction(row, bodies[row["entry_pc"]], context)
                     for row in output if "introduction" in bodies[row["entry_pc"]]}
    order = compact_record(shared.get("selection_order", {}), set(), {"introductions"}, label="selection order")
    if "introductions" in order:
        selectors = order["introductions"]
        if (not isinstance(selectors, list) or any(not isinstance(item, str) for item in selectors)
                or len(selectors) != len(set(selectors)) or set(selectors) != set(introductions)):
            raise ValueError("The introduction order requires unique, complete, known selections.")
        introductions = {selector: introductions[selector] for selector in selectors}
    if introductions:
        if metadata["support"].get("introductions"):
            raise ValueError("Constructed introductions cannot coexist with copied introduction records.")
        metadata["support"]["introductions"] = list(introductions.values())
    derived = _compact_table_metadata(output, context)
    if derived:
        convention = metadata["table_convention"]
        if set(convention).intersection(derived):
            raise ValueError("The compact metadata contains copied derived existential tables.")
        convention.update(derived)
    hashes = deepcopy(shared["input_digest_sources"])

    def refresh(value):
        if isinstance(value, dict):
            for key in list(value):
                if key in {"source_hashes", "code_source_hashes"} and isinstance(value[key], dict):
                    value[key] = source_hashes(value[key], Path(root))
                else:
                    refresh(value[key])
        elif isinstance(value, list):
            for item in value:
                refresh(item)
    refresh(metadata)
    if "hashes" in metadata:
        metadata["hashes"] = {key: value for key, value in metadata["hashes"].items()}
        current = source_hashes(hashes.values(), Path(root))
        for key, path in hashes.items():
            metadata["hashes"][key] = current[path]
        if "generator_sha256" in metadata["hashes"]:
            metadata["hashes"]["generator_sha256"] = digest(Path(__file__))
    return {"function": function["name"], "hash_sources": hashes, "design": metadata}


def compare_constructed_identity(expected, current, *, function, scope, catalog_path, root=ROOT):
    """Compare migration evidence using only the reviewed literal exclusions."""
    if digest(catalog_path) not in {
            "19276d47af0e4746c698e67bca801d2ff435e70f2d538b7247aaae8c19169a17",
            "d2f41456399f7f37fc1a06d8ccd8110e0462713e06aef50695068a77714b0fcb"}:
        raise ValueError("The literal digest catalog is not the reviewed catalog.")
    catalog = json.loads(Path(catalog_path).read_text())
    rows = [row for row in catalog["scopes"][scope] if row["function"] == function]
    if not rows:
        raise ValueError("The digest catalog has no selected comparison scope.")
    return _compare_digest_values(expected, current, rows, root=Path(root))


def _compare_digest_values(expected, current, rows, *, root):
    excluded = {}
    for row in rows:
        pointer = row["json_pointer"]
        if not pointer.startswith("/") or pointer in excluded:
            raise ValueError("The digest catalog repeats or invalidates a literal pointer.")
        excluded[pointer] = row
    used = set()

    def compare(left, right, pointer=""):
        if type(left) is not type(right):
            raise ValueError("A migration value changed type: " + pointer)
        if pointer in excluded:
            if (not isinstance(left, str) or not re.fullmatch("[0-9a-f]{64}", left)
                    or not re.fullmatch("[0-9a-f]{64}", right)):
                raise ValueError("An excluded digest must be a scalar SHA256 value.")
            row = excluded[pointer]
            historical = row.get("expected_value", row.get("bound_sha256"))
            if left != historical:
                raise ValueError("The historical expected digest changed: " + pointer)
            actual = source_hashes([row["current_source"]], root)[row["current_source"]]
            if right != actual:
                raise ValueError("The excluded current digest does not bind source bytes: " + pointer)
            used.add(pointer)
        elif isinstance(left, dict):
            if left.keys() != right.keys():
                raise ValueError("Migration object keys changed: " + pointer)
            for key in left:
                escaped = key.replace("~", "~0").replace("/", "~1")
                compare(left[key], right[key], pointer + "/" + escaped)
        elif isinstance(left, list):
            if len(left) != len(right):
                raise ValueError("Migration array length changed: " + pointer)
            for index, (one, other) in enumerate(zip(left, right)):
                compare(one, other, pointer + "/" + str(index))
        elif left != right:
            raise ValueError("A semantic or structural migration value changed: " + pointer)

    compare(expected, current)
    if used != excluded.keys():
        raise ValueError("The migration comparison has unused digest pointers.")
    return {"exact_except_literal_digests": True, "validated_digest_values": len(used)}


def build(inventory, name, profile, *, root=ROOT, generator=None):
    """Preserve supplied resource declarations while checking the selected CFG."""
    root = Path(root)
    function = selected_function(inventory, name)
    if profile.get("function") != function["name"]:
        raise ValueError("The profile and inventory name different functions.")
    result = deepcopy(profile["design"])
    names = FunctionNames(prefix_argument(name))
    generated_paths = {str(Path("ZesuSsz/Generated") / names.module / filename)
                       for filename in ("Entries.v", "Registrations.v", "BootstrapRegistrations.v")}
    supported = [row for row in result["blocks"] if "support" in row]
    if supported:
        if generated_paths.intersection(profile["hash_sources"].values()):
            raise ValueError("The profile binds a generated output as an input source.")
        refresh_supported_sources(result, root, generated_paths)
    blocks = sorted(function["blocks"], key=lambda block: block["start"])
    rows = {row["pc"]: row for row in function["rows"]}
    starts = {block["start"] for block in blocks}
    templates = {int(row["entry_pc"], 0): row for row in result["blocks"]}
    if len(templates) != len(result["blocks"]) or set(templates) != starts:
        raise ValueError("The profile must describe every selected block exactly once.")
    if len(rows) != len(function["rows"]) or set(rows) != set(range(function["entry"], function["end"], 4)):
        raise ValueError("The selected instructions have a gap or a duplicate.")
    if blocks[0]["start"] != function["entry"] or blocks[-1]["end"] != function["end"]:
        raise ValueError("The blocks do not span the selected function.")
    if any(left["end"] != right["start"] for left, right in zip(blocks, blocks[1:])):
        raise ValueError("The selected blocks have a gap or an overlap.")
    if inventory["elf_sha256"] != digest(root / "build/stock-zisk/zesu-zisk.elf"):
        raise ValueError("The inventory binds a different selected ELF.")

    call_targets = resolved_calls(function)
    incoming = {pc: [] for pc in starts}
    uses, writes, terminators = {}, {}, {}
    backedges = {(int(edge["from"], 0), int(edge["to"], 0))
                 for loop in function["loops"] for edge in loop["backward_edges"]}
    branch_count, returns = 0, []
    for block in blocks:
        pc, stop = block["start"], block["end"]
        uses[pc], writes[pc] = set(), set()
        for at in range(pc, stop, 4):
            row = rows[at]
            kind, targets, _, _ = control(row, call_targets)
            if row["kind"] != kind or set(row["successors"]) != set(targets):
                raise ValueError(f"The instruction word and CFG differ at {address(at)}.")
            if at + 4 != stop and (kind == "call" or targets != [at + 4]):
                raise ValueError("A control transfer occurs inside a block.")
            uses[pc].update(register_reads(row) - writes[pc])
            if kind in {"plain", "load"}:
                writes[pc].update({row["rd"]} - {0})
        tail = rows[stop - 4]
        kind, targets, guards, _ = control(tail, call_targets)
        terminators[pc] = kind
        if set(block["successors"]) != set(targets) or any(target not in starts for target in targets):
            raise ValueError("A block has an undeclared successor.")
        branch_count += kind == "branch"
        if kind == "return":
            returns.append(tail["pc"])
        for target, guard in zip(targets, guards):
            edge_kind = ("loop_backedge" if (tail["pc"], target) in backedges else
                         "conditional" if kind == "branch" else
                         "jump" if kind == "jump" else "call" if kind == "call" else "fallthrough")
            incoming[target].append({"from_block": address(pc),
                "from_instruction": address(tail["pc"]), "source_terminator": tail["mnemonic"],
                "kind": edge_kind, "path_condition": guard})
    if sorted(returns) != sorted(function["returns"]) or branch_count != function["branch_count"]:
        raise ValueError("The selected branch or return inventory differs from the words.")

    live = {pc: set() for pc in starts}
    changed = True
    while changed:
        changed = False
        for block in reversed(blocks):
            pc = block["start"]
            successors = set().union(*(live[target] for target in block["successors"]))
            current = uses[pc] | (successors - writes[pc])
            if current != live[pc]:
                live[pc], changed = current, True
    output = []
    for block in blocks:
        pc = block["start"]
        row = deepcopy(templates[pc])
        selected = {(edge["from_block"], edge["from_instruction"]): edge["resource_alternative"]
                    for edge in row.get("incoming_edges", []) if "resource_alternative" in edge}
        edges = sorted(incoming[pc], key=lambda edge: (edge["from_block"], edge["from_instruction"]))
        for edge in edges:
            key = (edge["from_block"], edge["from_instruction"])
            if key in selected:
                edge["resource_alternative"] = selected.pop(key)
        if selected:
            raise ValueError("A resource alternative names an absent incoming edge.")
        if pc == function["entry"]:
            edges.insert(0, {"from_block": "caller", "from_instruction": None,
                             "kind": "entry", "path_condition": {"op": "true"}})
        row.update(entry_pc=address(pc), end_pc_exclusive=address(block["end"]),
                   incoming_edges=edges, successor_pcs=[address(target) for target in block["successors"]])
        row.setdefault("needed_resources", {})["register_live_in_hint"] = [f"x{reg}" for reg in sorted(live[pc])]
        row["source_hashes"] = source_hashes(row["source_hashes"], root)
        if terminators[pc] == "return":
            row["return_clause"]["return_instruction_pc"] = address(block["end"] - 4)
        elif "return_clause" in row:
            raise ValueError("A non-return block has a return clause.")
        output.append(row)
    result.update(function=function["name"], entry_pc=address(function["entry"]),
                  end_pc_exclusive=address(function["end"]), instruction_count=len(rows),
                  block_count=len(blocks), conditional_branch_count=branch_count,
                  loop_count=function["loop_count"], blocks=output)
    refreshed = source_hashes(profile["hash_sources"].values(), root)
    result["hashes"] = {key: refreshed[path] for key, path in profile["hash_sources"].items()}
    result["hashes"]["generator_sha256"] = digest(generator or Path(__file__))
    for call in result.get("calls", []):
        call["source_hashes"] = source_hashes(call["source_hashes"], root)
        call["code_source_hashes"] = source_hashes(call["code_source_hashes"], root)
    convention = result["table_convention"]
    convention["code_source_hashes"] = source_hashes(convention["code_source_hashes"], root)
    structure(inventory, result)
    validate_resources(result, root, names.prefix)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--function", required=True)
    parser.add_argument("--inventory", type=Path, default=ROOT / "build/stock-zisk/inventory.json")
    inputs = parser.add_mutually_exclusive_group()
    inputs.add_argument("--profile", type=Path)
    inputs.add_argument("--author", type=Path)
    parser.add_argument("--source-closure", type=Path)
    parser.add_argument("--notation-choices", type=Path)
    parser.add_argument("--registry-evidence", type=Path)
    parser.add_argument("--profile-output", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.author and args.source_closure is None:
        parser.error("--author requires a bound --source-closure input")
    if not args.author and (args.source_closure or args.profile_output or args.notation_choices or args.registry_evidence):
        parser.error("Source closure, profile output, notation choices, and registry evidence require --author")
    names = FunctionNames(prefix_argument(args.function))
    inventory = json.loads(args.inventory.read_text())
    if args.author:
        profile = construct_profile(inventory, args.function, json.loads(args.author.read_text()),
                                    source_closure=json.loads(args.source_closure.read_text()),
                                    notation_choices=json.loads(args.notation_choices.read_text())
                                    if args.notation_choices else None,
                                    registry_evidence=json.loads(args.registry_evidence.read_text())
                                    if args.registry_evidence else None)
    else:
        profile_path = args.profile or ROOT / f"ZesuSsz/Contracts/{names.filename}_block_design.json"
        profile = json.loads(profile_path.read_text())
    rendered = json.dumps(build(inventory, args.function, profile), indent=2) + "\n"
    if args.profile_output:
        text = json.dumps(profile, indent=2) + "\n"
        if args.check:
            if not args.profile_output.is_file() or args.profile_output.read_text() != text:
                raise SystemExit("The constructed profile is stale.")
        else:
            args.profile_output.parent.mkdir(parents=True, exist_ok=True)
            args.profile_output.write_text(text)
    output = (args.output or ROOT / f"ZesuSsz/Evidence/{names.filename}_block_design.json").resolve()
    label = output.relative_to(ROOT) if output.is_relative_to(ROOT) else output
    if args.check:
        if not output.is_file() or checked_design_text(output.read_bytes().decode("utf-8")) != checked_design_text(rendered):
            raise SystemExit("The selected block design is stale.")
        print(f"checked {label}")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered)
        print(f"wrote {label}")


if __name__ == "__main__":
    main()
