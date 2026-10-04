"""Render and check selected-byte commitments and decoded CFG data."""
import hashlib
import re

MARKER = "\n(* Selected ELF commitments. *)\n"

def native_prefix(text):
    return text.split(MARKER, 1)[0]

def make_commitment(rows, edges, exits, calls=None):
    rows = sorted(rows, key=lambda row: row["pc"])
    addresses = [row["pc"] for row in rows]
    if len(addresses) != len(set(addresses)):
        raise ValueError("The instruction-byte table repeats an address")
    table = [{"pc": hex(row["pc"]),
              "bytes": row["word"].to_bytes(row["size"], "little").hex()} for row in rows]
    data = b"".join(bytes.fromhex(entry["bytes"]) for entry in table)
    return {"instruction_bytes_sha256": hashlib.sha256(data).hexdigest(),
            "instruction_bytes": table,
            "cfg_edges": [[hex(source), hex(target)] for source, target in sorted(set(edges))],
            "cfg_exits": exits, "call_sites": calls or []}

def cfg_edges(rows, function_pcs, slots=None):
    """Keep intra-function transfers and separate calls from exits."""
    slots = slots or {}
    edges, exits, calls = [], [], []
    for row in sorted(rows, key=lambda row: row["pc"]):
        pc, kind = row["pc"], row["kind"]
        if kind == "return":
            exits.append({"pc": hex(pc), "kind": "return", "target": None})
            continue
        if kind == "call":
            if "target" not in row:
                raise ValueError(f"The call target is unresolved at {pc:#x}")
            target = row["target"]
            if row.get("resolution") == "selected allocator vtable under the stated entry condition":
                if target not in slots:
                    raise ValueError(f"The selected vtable slot is absent at {pc:#x}")
                callee = {"kind": "vtable-slot", "identity": hex(slots[target])}
            else:
                callee = {"kind": "entry", "identity": hex(target)}
            calls.append({"pc": hex(pc), "callee": callee,
                          "continuation": hex(pc + row["size"])})
            continue
        if kind == "jump":
            successors = [row["target"]]
        elif kind == "branch":
            successors = [row["target"], pc + row["size"]]
        elif kind == "indirect":
            if not row.get("successors") or not row.get("resolution"):
                raise ValueError(f"The indirect transfer is unresolved at {pc:#x}")
            successors = row["successors"]
        elif kind == "runtime":
            # The byte table still binds this explicitly refused instruction.
            continue
        else:
            successors = [pc + row["size"]]
        for target in sorted(set(successors)):
            if target in function_pcs:
                edges.append((pc, target))
            elif kind == "jump":
                exits.append({"pc": hex(pc), "kind": "tail", "target": hex(target)})
            else:
                raise ValueError(f"A non-tail transfer leaves the function at {pc:#x}")
    return sorted(set(edges)), exits, calls

def render_exports(name, commitment):
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
        raise ValueError("The export name is not a Rocq identifier")
    table = []
    for entry in commitment["instruction_bytes"]:
        values = "; ".join(f"0x{byte:02x}%Z" for byte in bytes.fromhex(entry["bytes"]))
        table.append(f"  ({entry['pc']}%Z, [{values}])")
    edges = [f"  ({source}%Z, {target}%Z)" for source, target in commitment["cfg_edges"]]
    calls = []
    for call in commitment["call_sites"]:
        constructor = "CalleeEntry" if call["callee"]["kind"] == "entry" else "CalleeVtableSlot"
        calls.append(f"  ({call['pc']}%Z, {constructor} {call['callee']['identity']}%Z, {call['continuation']}%Z)")
    return (MARKER + "From Coq Require Import Lists.List ZArith.ZArith Strings.String.\n"
            + "Require Import ZesuSsz.CalleeIdentity.CalleeId.\n"
            + "Import ListNotations.\n"
            + f"Definition {name}_instruction_bytes_sha256 : string :=\n"
            + f"  \"{commitment['instruction_bytes_sha256']}\"%string.\n"
            + f"Definition {name}_instruction_bytes : list (Z * list Z) := [\n"
            + ";\n".join(table) + "\n].\n"
            + f"Definition {name}_cfg_edges : list (Z * Z) := [\n"
            + ";\n".join(edges) + "\n].\n"
            + f"Definition {name}_cfg_step (source target : Z) : Prop :=\n"
            + f"  List.In (source, target) {name}_cfg_edges.\n"
            + f"Definition {name}_call_sites : list (Z * CalleeId * Z) := [\n"
            + ";\n".join(calls) + "\n].\n")

def append_exports(path, name, commitment):
    path.write_text(native_prefix(path.read_text()) + render_exports(name, commitment))

def validate_exports(path, name, commitment):
    text = path.read_text()
    if MARKER not in text or text.split(MARKER, 1)[1] != render_exports(name, commitment).split(MARKER, 1)[1]:
        raise ValueError("The byte or CFG exports differ from the manifest: " + name)
    data = b"".join(bytes.fromhex(entry["bytes"]) for entry in commitment["instruction_bytes"])
    if hashlib.sha256(data).hexdigest() != commitment["instruction_bytes_sha256"]:
        raise ValueError("The instruction-byte hash differs from its table: " + name)

def selected_commitments(inventory, image, groups):
    """Bind complete region bytes and the approved call boundary."""
    from indexes import FUNCTION_NAMES, approved_regions
    from riscv import decode_range, simple_transfers
    functions = {function["name"]: function for function in inventory["functions"]}
    owner = {name: function for function, name in FUNCTION_NAMES.items() if name}
    inline = inventory["inline_decodeSingleTx"]
    inline_rows = simple_transfers([row for block in inline["block_ranges"]
        for row in decode_range(block["start"], image.read(block["start"], block["end"] - block["start"]))])
    inline_at = {row["pc"]: row for row in inline_rows}
    for call in inline["calls"]:
        if call["kind"] != "call":
            continue
        row = inline_at[call["pc"]]
        if row.get("target", call["target"]) != call["target"]:
            raise ValueError("The inline call target changed")
        row.update(kind="call", target=call["target"])
    all_pcs = {row["pc"] for function in functions.values() for row in function["rows"]} | set(inline_at)
    complete_regions = approved_regions(inventory, all_pcs)
    vtable = inventory["allocator_vtable"]
    table_bytes = image.read(vtable["address"], 32)
    if table_bytes.hex() != vtable["bytes"]:
        raise ValueError("The selected allocator vtable bytes changed")
    slots = {}
    for index, slot in enumerate(["alloc", "resize", "remap", "free"]):
        entry = int.from_bytes(table_bytes[index * 8:index * 8 + 8], "little")
        if entry != vtable["slots"][slot]:
            raise ValueError("The selected allocator slot changed")
        slots[entry] = vtable["address"] + index * 8
    result = {}
    for name in groups:
        if name == "decodeSingleTx":
            at = inline_at
            symbol = image.symbols[inline["parent_symbol"]]
            function_pcs = set(range(symbol["st_value"], symbol["st_value"] + symbol["st_size"], 4))
            function_name = inline["parent_symbol"]
        else:
            function_name = "rlp_decode.decodeTxFields" if name.startswith("decodeTxFields_") else owner[name]
            function = functions[function_name]
            at = {row["pc"]: row for row in function["rows"]}
            function_pcs = set(at)
            dispatch = function.get("dispatch")
            if dispatch:
                data = image.read(dispatch["table_address"], len(bytes.fromhex(dispatch["table_bytes"])))
                if data.hex() != dispatch["table_bytes"] or [int.from_bytes(data[offset:offset+8], "little")
                      for offset in range(0, len(data), 8)] != dispatch["targets"]:
                    raise ValueError("The selected dispatch targets changed")
                if at[dispatch["pc"]]["successors"] != dispatch["targets"]:
                    raise ValueError("The decoded dispatch successors changed")
        rows = [at[pc] for pc in sorted(complete_regions[name])]
        if set(groups[name]) != {row["pc"] for row in rows if row["kind"] != "runtime"}:
            raise ValueError("The indexed PCs differ from the complete byte region: " + name)
        for row in rows:
            if image.read(row["pc"], row["size"]) != row["word"].to_bytes(row["size"], "little"):
                raise ValueError("The committed instruction bytes differ from the ELF")
        edges, exits, calls = cfg_edges(rows, function_pcs, slots)
        commitment = make_commitment(rows, edges, exits, calls)
        commitment["function"] = function_name
        commitment["unmodeled_instruction_pcs"] = [hex(row["pc"]) for row in rows if row["kind"] == "runtime"]
        result[name] = commitment
    return result
