"""Render source-bound access regions with reset-register expressions."""
import hashlib
import gzip
import json
from pathlib import Path
import re


def checked_file(binding, source_map=None):
    if source_map is None:
        path = Path(binding["path"])
    else:
        mapped = source_map["paths"].get(binding["path"])
        if mapped is None or mapped["sha256"] != binding["sha256"]:
            raise ValueError("A region source has no exact retained mapping: " + binding["path"])
        relative = Path(mapped["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("A retained region source escapes its policy root")
        root = source_map["root"]
        path = (root / relative).resolve()
        if not path.is_relative_to(root):
            raise ValueError("A retained region source escapes its policy root")
    if hashlib.sha256(path.read_bytes()).hexdigest() != binding["sha256"]:
        raise ValueError("A region source changed: " + str(path))
    return path


def read_source_map(path, digest):
    path = checked_file({"path": str(path), "sha256": digest})
    data = json.loads(path.read_text())
    if data.get("schema") != "source.region-path-map.v1" or not isinstance(data.get("paths"), dict):
        raise ValueError("The region source map is invalid")
    return dict(data, root=path.resolve().parent)


def read_packet(path, digest, source_map=None):
    path = Path(path)
    payload = path.read_bytes()
    if path.suffix == ".gz":
        if source_map is None:
            raise ValueError("A policy archive requires an explicit source map")
        archive = source_map.get("archives", {}).get(path.name)
        if (archive is None or path.resolve().parent != source_map["root"]
                or archive.get("sha256") != hashlib.sha256(payload).hexdigest()
                or archive.get("payload_sha256") != digest):
            raise ValueError("The policy archive binding differs")
        try:
            payload = gzip.decompress(payload)
        except (OSError, EOFError) as error:
            raise ValueError("The policy archive is invalid") from error
    if hashlib.sha256(payload).hexdigest() != digest:
        raise ValueError("A region source changed: packet payload " + str(path))
    return json.loads(payload)


def region_bounds(packet, source_map=None):
    regions = packet.get("regions")
    if regions is not None:
        return {name: (int(value["lower"]), int(value["upper"]))
                for name, value in regions.items()}
    for declaration in packet.get("source_declarations", []):
        checked_file(declaration["file"], source_map)
        if "closed_region_values" in declaration:
            return {name: (value["lo"], value["hi"])
                    for name, value in declaration["closed_region_values"].items()}
    raise ValueError("The packet has no closed region bounds")


def input_end_register(packet, access):
    region = access["production_region"]
    bindings = region.get("source_parameter_bindings")
    if bindings is not None:
        symbol = bindings.get("inputEnd")
        if (not isinstance(symbol, str) or region.get("symbol_types", {}).get(symbol) != "BitVec64"
                or bindings.get("actualInputEnd_owner") != f'"zisk_input_end" ↦ᵣ RVal_Bits {symbol}'):
            raise ValueError("The input-end source symbol has no register binding")
        if not any(row["event"][:3] == ["read-reg", "|zisk_input_end|", "nil"]
                   for row in region.get("original_input_end_reads", [])):
            raise ValueError("The input-end register has no source read")
    else:
        owner = region.get("input_end_owner") or packet.get("input_end_owner") or {}
        if not re.fullmatch(r"\(KindReg zisk_input_end, ExactShape \(RVal_Bits .+\)\)",
                            owner.get("shape", "")):
            raise ValueError("The input-end source has no exact register owner")
    return "zisk_input_end"


def access_constraint(packet, access, instruction, bounds):
    for key in ["pc", "word", "size", "kind", "mnemonic", "rs1", "imm", "width"]:
        if access["instruction"].get(key) != instruction.get(key):
            raise ValueError("The region instruction differs from the checked ELF: " + key)
    operation = instruction["kind"]
    if access.get("operation") != operation or operation not in {"load", "store"}:
        raise ValueError("The region operation differs from the instruction")
    if (access.get("address_width") != 64 or access.get("comparison_width") != 128
            or access.get("access_bytes") != instruction["width"]):
        raise ValueError("The access or comparison width differs")
    register = f"x{instruction['rs1']}"
    event = access["raw_register"]["event"]
    if len(event) != 4 or event[:3] != ["read-reg", f"|{register}|", "nil"]:
        raise ValueError("The address source is not the decoded ISA register")
    expression = access["raw_address"]["event"]
    offset = instruction["imm"] % (1 << 64)
    literal = f"#x{offset:016x}"
    if (len(expression) != 3 or expression[0] != "define-const"
            or expression[2] != ["bvadd", event[3], literal]):
        raise ValueError("The address source does not use the decoded immediate")
    region = access["production_region"]
    source = region.get("source_parameter_bindings")
    if source is not None:
        address = re.fullmatch(r"\(bvadd ([A-Za-z_][A-Za-z0-9_]*) (#x[0-9a-f]{16})\)",
                               source.get("address", ""))
        if (address is None or region.get("symbol_types", {}).get(address[1]) != "BitVec64"
                or address[2] != literal):
            raise ValueError("The address source parameter is unresolved or has another offset")
    names = access.get("unsplit_region_set")
    if (not isinstance(names, list) or not names or len(names) != len(set(names))
            or set(names) != set(region["set"])):
        raise ValueError("The exact unsplit region union is absent or inconsistent")
    if operation == "store" and names != ["RAM"]:
        raise ValueError("A store region is not writable RAM")
    address = f"(bvadd {register} {literal})"
    width = instruction["width"]
    if type(width) is not int or not 0 < width < 1 << 64:
        raise ValueError("The access width does not fit an unsigned word")
    width_literal = f"#x{width:016x}"
    alternatives = []
    for name in names:
        if name not in {"RAM", "INPUT_BUFFER", "RODATA"} or name not in bounds:
            raise ValueError("The region name has no resolved platform bounds: " + str(name))
        lower, upper = bounds[name]
        if (type(lower) is not int or type(upper) is not int
                or not 0 <= lower < upper <= 1 << 64):
            raise ValueError("The platform region bounds are invalid")
        input_end = input_end_register(packet, access) if name == "INPUT_BUFFER" else None
        if upper - lower < width:
            alternatives.append("false")
            continue
        # Subtract the width from the bound, not from the symbolic address.
        # This preserves the full access condition without modular end wrap.
        clauses = [f"(bvule #x{lower:016x} {address})",
                   f"(bvule {address} #x{upper - width:016x})"]
        if input_end is not None:
            clauses.extend([f"(bvule {width_literal} {input_end})",
                            f"(bvule {address} (bvsub {input_end} {width_literal}))"])
        alternatives.append("(and " + " ".join(clauses) + ")")
    constraint = alternatives[0] if len(alternatives) == 1 else "(or " + " ".join(alternatives) + ")"
    return constraint, {"pc": hex(instruction["pc"]), "operation": operation,
                        "register": register, "immediate": instruction["imm"],
                        "access_bytes": instruction["width"], "region_union": names,
                        "comparison_width": 64,
                        "source_comparison_width": access["comparison_width"],
                        "constraint": constraint, "assume_discharge": "OPEN"}


def checked_exemptions(path, digest, rows, source_map=None):
    if path is None:
        return {}, []
    packet = read_packet(path, digest, source_map)
    if packet.get("schema") != "source.single-leaf-load-exemptions.v1":
        raise ValueError("The load-exemption schema is unsupported")
    selected = {row["pc"]: row for row in rows}
    exemptions = {}
    sources = [{"path": str(path), "sha256": digest}] if source_map is None else []
    for item in packet["exemptions"]:
        pc = int(item["pc"], 0)
        if pc in exemptions or pc not in selected:
            raise ValueError("The load exemption is repeated or outside the selection")
        instruction = selected[pc]
        original = item["source_access"]["instruction"]
        if (item.get("kind") != "single_leaf_load_exemption"
                or instruction["kind"] != "load" or item.get("new_premises") != []
                or any(original.get(key) != instruction.get(key)
                       for key in ["pc", "word", "size", "kind", "mnemonic", "rs1", "imm", "width"])):
            raise ValueError("The load exemption does not match the selected instruction")
        for name in ["source_packet", "precise_handoff", "raw_trace", "rocq_trace"]:
            checked_file(item[name], source_map)
            sources.append(item[name])
        exemptions[pc] = item
    if len(exemptions) != packet.get("exemption_count"):
        raise ValueError("The load-exemption count differs")
    return exemptions, sources


def annotate_regions(rows, packet_path, packet_hash, exemption_path=None, exemption_hash=None, source_map=None):
    packet = read_packet(packet_path, packet_hash, source_map)
    if packet.get("schema") != "source-per-load-placement319.v1":
        raise ValueError("The access-region schema is unsupported")
    checked_file(packet["entry"], source_map)
    bounds = region_bounds(packet, source_map)
    source_bindings = [packet["entry"]]
    source_bindings.extend(row["file"] for row in packet.get("source_declarations", [])
                           if "file" in row)
    exemptions, exemption_sources = checked_exemptions(exemption_path, exemption_hash, rows, source_map)
    source_bindings.extend(exemption_sources)
    accesses = {}
    for access in packet["loads"]:
        pc = int(access["pc"], 0)
        if pc in accesses:
            raise ValueError("The region packet repeats an instruction")
        checked_file(access["raw_trace"], source_map)
        source_bindings.append(access["raw_trace"])
        accesses[pc] = access
    memory = {row["pc"] for row in rows if row["kind"] in {"load", "store"}}
    if memory != set(accesses):
        raise ValueError("The packet does not cover the exact selected memory instructions")
    result = []
    records = []
    for row in rows:
        row = dict(row)
        if row["pc"] in accesses:
            constraint, record = access_constraint(packet, accesses[row["pc"]], row, bounds)
            if row["pc"] in exemptions:
                if any(line.startswith("//@constraint:") for line in row.get("annotations", [])):
                    raise ValueError("An exempt load already has a constraint")
                record["constraint_emitted"] = False
                record["exemption"] = {"pc": hex(row["pc"]), "kind": exemptions[row["pc"]]["kind"]}
            else:
                row["annotations"] = list(row.get("annotations", [])) + ["//@constraint: " + constraint]
                record["constraint_emitted"] = True
            records.append(record)
        result.append(row)
    unique = {}
    for binding in source_bindings:
        path = binding["path"]
        if path in unique and unique[path]["sha256"] != binding["sha256"]:
            raise ValueError("The region source bindings conflict")
        unique[path] = binding
    bindings = list(unique.values())
    if source_map is not None:
        bindings = [{"path": str(checked_file(binding, source_map)), "sha256": binding["sha256"]}
                    for binding in bindings]
    return result, records, bindings
