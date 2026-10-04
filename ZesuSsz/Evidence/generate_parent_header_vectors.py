#!/usr/bin/env python3
"""Check real header RLP fixtures and stage their SailRun execution script."""

import argparse
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = Path(__file__).with_name("parent_header_vectors.json")
OUTPUT = ROOT / "ZesuSsz/Compliance/ParentHeaderVectorAudit.v"
FIELD_NAMES = (
    "parentHash", "sha3Uncles", "miner", "stateRoot", "transactionsRoot",
    "receiptsRoot", "logsBloom", "difficulty", "number", "gasLimit",
    "gasUsed", "timestamp", "extraData", "mixHash", "nonce",
    "baseFeePerGas", "withdrawalsRoot", "blobGasUsed", "excessBlobGas",
    "parentBeaconBlockRoot",
)


def rlp_items(encoded):
    if encoded[0] < 248:
        raise ValueError("Expected a long RLP list")
    width = encoded[0] - 247
    payload_length = int.from_bytes(encoded[1:1 + width], "big")
    payload = encoded[1 + width:]
    if payload_length != len(payload):
        raise ValueError("The RLP list length differs from its payload")
    items = []
    offset = 0
    while offset < len(payload):
        tag = payload[offset]
        if tag < 128:
            item, end = payload[offset:offset + 1], offset + 1
        elif tag < 184:
            length = tag - 128
            end = offset + 1 + length
            item = payload[offset + 1:end]
        elif tag < 192:
            width = tag - 183
            length = int.from_bytes(payload[offset + 1:offset + 1 + width], "big")
            end = offset + 1 + width + length
            item = payload[offset + 1 + width:end]
        else:
            raise ValueError("A header field must be an RLP string")
        if end > len(payload):
            raise ValueError("An RLP field exceeds the list payload")
        items.append(item)
        offset = end
    return items


def check_fixture(header):
    data = bytes.fromhex(header["rlp"][2:])
    digest = subprocess.check_output(
        ["openssl", "dgst", "-keccak-256", "-binary"], input=data).hex()
    if "0x" + digest != header["hash"]:
        raise ValueError("The RLP Keccak digest differs from the RPC block hash")
    items = rlp_items(data)
    if len(items) != header["fieldCount"]:
        raise ValueError("The RLP field count differs from the RPC fixture")
    for key in ("baseFeePerGas", "blobGasUsed", "excessBlobGas"):
        index = FIELD_NAMES.index(key)
        actual = None if index >= len(items) else int.from_bytes(items[index], "big")
        recorded = header[key]
        expected = None if recorded is None else int(recorded, 16)
        if actual != expected:
            raise ValueError(f"The {key} value differs from the RPC fixture")
    return data


def rocq_bytes(name, data):
    values = [str(value) for value in data]
    rows = ["; ".join(values[offset:offset + 20])
            for offset in range(0, len(values), 20)]
    return f"Definition {name} : list byte := map mword_of_int [\n  " + (
        ";\n  ".join(rows)) + "].\n"


def render(fixtures):
    result = """From Coq Require Import List ZArith.
Require Import SailStdpp.MachineWord SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.

Import ListNotations.
Open Scope Z_scope.

(* Execution evidence for Q24. No contract consumes these computations. *)
Definition parentNodeSummary {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len) :=
  match runRlpNodeCursor bytes node with
  | Success (existT _ (existT _ cursor)) =>
      Success (cursor.(StatelessInputSliceFields_bytes),
               cursor.(StatelessInputSliceFields_len))
  | Reject error => Reject error
  | UnsupportedOrInternalFailure message =>
      UnsupportedOrInternalFailure message
  end.

Definition parentFieldsSummary (outcome : SailOutcome ParentHeaderFields) :=
  match outcome with
  | Success fields => Success (
      fields.(ParentHeaderFields_have_parent),
      fields.(ParentHeaderFields_have_state),
      if fields.(ParentHeaderFields_have_base_fee) then
        Some fields.(ParentHeaderFields_base_fee).(word_value) else None,
      if fields.(ParentHeaderFields_have_blob_gas) then
        Some fields.(ParentHeaderFields_blob_gas_used) else None,
      if fields.(ParentHeaderFields_have_excess_blob_gas) then
        Some fields.(ParentHeaderFields_excess_blob_gas).(excess_blob_gas_value)
      else None)
  | Reject error => Reject error
  | UnsupportedOrInternalFailure message =>
      UnsupportedOrInternalFailure message
  end.

"""
    for header in fixtures["headers"]:
        data = check_fixture(header)
        name = header["case"]
        size = len(data)
        result += (f"(* Mainnet block {header['number']}: {header['hash']}. *)\n"
                   + rocq_bytes(name, data)
                   + f"Definition {name}Node := @Build_StatelessInputSliceFields 0 {size} 0 {size}.\n"
                   + f"Eval vm_compute in parentNodeSummary {name} {name}Node.\n"
                   + f"Eval vm_compute in parentFieldsSummary "
                     f"(sailParentHeaderRun {name} {name}Node).\n\n")
    last = fixtures["headers"][-1]
    truncated = check_fixture(last)[:-1]
    size = len(truncated)
    result += ("(* One byte removed from the last RLP field of the final block. *)\n"
               + rocq_bytes("truncated_header", truncated)
               + f"Definition truncatedNode := @Build_StatelessInputSliceFields 0 {size} 0 {size}.\n"
               + "Eval vm_compute in parentNodeSummary truncated_header truncatedNode.\n"
               + "Eval vm_compute in parentFieldsSummary "
                 "(sailParentHeaderRun truncated_header truncatedNode).\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render(json.loads(FIXTURES.read_text()))
    if args.check:
        if OUTPUT.read_text() != content:
            raise SystemExit("ParentHeaderVectorAudit.v differs from its fixtures")
    else:
        OUTPUT.write_text(content)


if __name__ == "__main__":
    main()
