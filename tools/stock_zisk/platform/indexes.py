"""Assign approved regions and check native instruction indexes."""
from collections import Counter
import re

FUNCTION_NAMES = {
    "rlp.decodeItem": "decodeItem",
    "rlp_decode.nextUint64": "nextUint64",
    "rlp_decode.decodeParentHeader": "decodeParentHeader",
    "rlp_decode.decodeTxFields": None,
    "rlp_decode.txAccessList": "txAccessList",
    "array_list.Aligned([32]u8,null).ensureTotalCapacity": "ensureTotalCapacity",
    "array_list.Aligned([32]u8,null).toOwnedSlice": "sliceBytes32",
    "array_list.Aligned(input.AccessListEntry,null).toOwnedSlice": "sliceAccessList",
    "alt_fl_alloc.alloc": "allocatorAlloc",
    "alt_fl_alloc.remap": "allocatorRemap",
    "alt_fl_alloc.free": "allocatorFree",
    "memcpy": "memcpyStub",
}

def approved_regions(inventory, supported):
    regions = {}
    functions = {function["name"]: function for function in inventory["functions"]}
    if len(functions) != len(inventory["functions"]) or functions.keys() != FUNCTION_NAMES.keys():
        raise ValueError("The selected function names differ")
    for function_name, name in FUNCTION_NAMES.items():
        function = functions[function_name]
        if name:
            regions[name] = {row["pc"] for row in function["rows"]} & supported
        else:
            blocks = {block["start"]: block for block in function["blocks"]}
            for region in inventory["transaction_regions"]:
                regions["decodeTxFields_" + region["name"]] = {
                    pc for start in region["blocks"]
                    for pc in range(start, blocks[start]["end"], 4)} & supported
    regions["decodeSingleTx"] = {
        pc for block in inventory["inline_decodeSingleTx"]["block_ranges"]
        for pc in range(block["start"], block["end"], 4)} & supported
    validate_partition(regions, supported)
    return regions

def validate_partition(regions, supported):
    counts = Counter(pc for pcs in regions.values() for pc in pcs)
    duplicates = sorted(pc for pc, count in counts.items() if count != 1)
    missing = sorted(supported - counts.keys())
    extra = sorted(counts.keys() - supported)
    if duplicates or missing or extra:
        raise ValueError(f"Index ownership differs: duplicates={duplicates[:10]}, missing={missing[:10]}, extra={extra[:10]}")

def validate_indexes(out, regions, coqdir):
    expected = {"index_" + name + ".v" for name in regions}
    actual = {path.name for path in out.glob("index_*.v")}
    if actual != expected:
        raise ValueError("Index modules differ from the approved regions")
    for name, pcs in regions.items():
        text = (out / ("index_" + name + ".v")).read_text()
        imports = re.findall(r"^Require Export ([A-Za-z0-9_.]+)\.a([0-9a-f]+)\.$", text, re.M)
        addresses = [int(pc, 16) for prefix, pc in imports if prefix == coqdir]
        pairs = [(int(pc, 16), int(reference, 16)) for pc, reference in
                 re.findall(r"\(0x([0-9a-f]+)%Z, a([0-9a-f]+)", text)]
        if any(pc != reference for pc, reference in pairs):
            raise ValueError("An index entry references a different instruction address: " + name)
        entries = [pc for pc, reference in pairs]
        if any(prefix != coqdir for prefix, pc in imports) or len(imports) != len(pcs) or set(addresses) != pcs or len(addresses) != len(pcs) or set(entries) != pcs or len(entries) != len(pcs):
            raise ValueError("Native index imports or entries differ: " + name)
