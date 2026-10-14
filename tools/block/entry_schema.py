"""Adapt the five approved design fields to the existing probe renderer."""
from copy import deepcopy
import hashlib
from pathlib import Path, PurePosixPath
import re

FIELDS = frozenset({"entry_definition", "binders", "arguments",
                    "resource_predicate", "source_hashes"})
IDENTIFIER = r"[A-Za-z_][A-Za-z0-9_']*"
ROCQ_NAME = re.compile(IDENTIFIER + r"(?:\." + IDENTIFIER + r")+")
SHA256 = re.compile(r"[0-9a-fA-F]{64}")


def expression(value, label):
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"The {label} is not a Rocq expression")
    return value


def contract_fields(block):
    """Copy the supplied fields; a descriptive block has no contract."""
    present = FIELDS.intersection(block)
    if not present:
        return None
    if present != FIELDS:
        raise ValueError("The executable entry lacks approved fields: " +
                         ", ".join(sorted(FIELDS - present)))
    for key in ("entry_definition", "resource_predicate"):
        value = block[key]
        if not isinstance(value, str) or not ROCQ_NAME.fullmatch(value):
            raise ValueError(f"The {key} is not a fully qualified Rocq name")
    binders = block["binders"]
    if not isinstance(binders, list):
        raise ValueError("The binders are not an ordered list")
    names = set()
    for binder in binders:
        if not isinstance(binder, dict) or set(binder) != {"name", "type"}:
            raise ValueError("Each binder must contain only name and type")
        name = binder["name"]
        if not isinstance(name, str) or not re.fullmatch(IDENTIFIER, name):
            raise ValueError("The binder name is invalid")
        if name in names or name == "Sigma":
            raise ValueError("The binder name is repeated or reserved")
        names.add(name)
        expression(binder["type"], "binder type")
    if not isinstance(block["arguments"], list):
        raise ValueError("The arguments are not an ordered list")
    for value in block["arguments"]:
        expression(value, "argument")
    hashes = block["source_hashes"]
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError("The source_hashes must be a nonempty path map")
    for path, digest in hashes.items():
        if (not isinstance(path, str) or not path or
                PurePosixPath(path).is_absolute() or
                any(part in (".", "..") for part in path.split("/")) or
                "\\" in path or str(PurePosixPath(path)) != path):
            raise ValueError("The source path is not repository-relative")
        if not isinstance(digest, str) or not SHA256.fullmatch(digest):
            raise ValueError("The source hash is not SHA-256 hex")
    return {name: deepcopy(block[name]) for name in sorted(FIELDS)}


def edge_contract_fields(block, edge):
    """Select an explicitly named target entry without changing its parameters."""
    fields = contract_fields(block)
    if "resource_alternative" not in edge:
        return fields
    name = edge["resource_alternative"]
    if edge.get("from_block") == "caller":
        raise ValueError("A caller entry cannot select an edge resource alternative")
    if not isinstance(name, str) or not ROCQ_NAME.fullmatch(name):
        raise ValueError("The edge resource alternative is not a fully qualified Rocq name")
    if fields is None:
        raise ValueError("The edge resource alternative lacks a target contract")
    if not any(path.endswith(".v") and name.startswith(source_module(path) + ".")
               for path in fields["source_hashes"]):
        raise ValueError("The source hashes do not bind the edge resource alternative: " + name)
    fields["entry_definition"] = name
    fields["resource_predicate"] = name
    return fields


def source_module(path):
    return str(PurePosixPath(path).with_suffix("")).replace("/", ".")


def verify_sources(fields, root):
    """Verify every declared source before parsing or rendering its entry."""
    root = Path(root).resolve()
    for path, expected in fields["source_hashes"].items():
        source = (root / path).resolve()
        if not source.is_relative_to(root):
            raise ValueError("The entry source escapes the repository")
        if hashlib.sha256(source.read_bytes()).hexdigest().lower() != expected.lower():
            raise ValueError("The executable entry source hash changed: " + path)
    return root


def verify_declarations(fields, root):
    """Locate the supplied entry definitions in their bound source modules."""
    root = Path(root)
    owners = {}
    for key in ("entry_definition", "resource_predicate"):
        name = fields[key]
        candidates = [path for path in fields["source_hashes"]
                      if path.endswith(".v") and name.startswith(source_module(path) + ".")]
        if not candidates:
            raise ValueError("The source hashes do not bind " + name)
        owner = max(candidates, key=lambda path: len(source_module(path)))
        declaration = name.rsplit(".", 1)[-1]
        if not re.search(r"\bDefinition\s+" + re.escape(declaration) + r"\b",
                         (root / owner).read_text()):
            raise ValueError("The entry source lacks Definition " + name)
        owners[key] = owner
    return owners


def entry_state(block, root, trace_import, code_premises):
    """Use supplied expressions without synthesizing resources or local values."""
    fields = contract_fields(block)
    if fields is None:
        return None
    root = verify_sources(fields, root)
    owners = verify_declarations(fields, root)
    if not isinstance(trace_import, str) or not ROCQ_NAME.fullmatch(trace_import):
        raise ValueError("The trace import is not a fully qualified Rocq name")
    if not code_premises or not any(line.strip() for line in code_premises):
        raise ValueError("The probe lacks explicit code premises")
    pc = int(block["entry_pc"], 0) if isinstance(block["entry_pc"], str) else block["entry_pc"]
    binders = fields["binders"]
    resource = fields["resource_predicate"]
    resource += "".join(" (" + value + ")" for value in fields["arguments"])
    path = owners["entry_definition"]
    return {"entry": hex(pc), "name": f"DesignedEntry_{pc:x}",
            "binders": "`{!islaG Sigma} `{!threadG}" +
                       "".join(f" ({item['name']} : {item['type']})" for item in binders),
            "arguments": " ".join(item["name"] for item in binders),
            "spatial": [resource], "coq": [],
            "imports": [source_module(path) for path in fields["source_hashes"] if path.endswith(".v")],
            "entry_source": {"path": path, "declaration": fields["entry_definition"].rsplit(".", 1)[-1],
                             "sha256": fields["source_hashes"][path].lower()},
            "root_provenance": fields,
            "probe_options": {"trace_import": trace_import, "code_premises": list(code_premises)}}


def design_states(design, root, trace_import, code_premises):
    states, errors = {}, {}
    for block in design["blocks"]:
        pc = int(block["entry_pc"], 0) if isinstance(block["entry_pc"], str) else block["entry_pc"]
        try:
            state = entry_state(block, root, trace_import, code_premises)
        except (ValueError, OSError) as error:
            errors[pc] = str(error)
        else:
            if state is not None:
                states[pc] = state
    return states, errors
