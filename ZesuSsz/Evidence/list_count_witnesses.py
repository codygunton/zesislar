#!/usr/bin/env python3
"""Serialize the SSZ fixtures from Compliance/ListCountExamples.v.

These bytes are test evidence. No theorem uses this evidence as a premise.
"""

import argparse
import struct
from pathlib import Path


TRANSACTION = bytes([201, 128, 128, 128, 128, 128, 128, 27, 128, 128])


def u32(value):
    return struct.pack("<I", value)


def repeated_byte_list(count, item):
    offsets = bytearray(4 * count)
    for index in range(count):
        struct.pack_into("<I", offsets, 4 * index, 4 * count + len(item) * index)
    return bytes(offsets) + item * count


def witness_input(transactions=b"", withdrawals=b"", headers=b""):
    payload = bytearray(540)
    for position, offset in ((436, 540), (504, 540),
                             (508, 540 + len(transactions)),
                             (528, 540 + len(transactions) + len(withdrawals))):
        struct.pack_into("<I", payload, position, offset)
    payload = bytes(payload) + transactions + withdrawals
    request = (u32(44) + u32(44 + len(payload)) + bytes(32) +
               u32(76 + len(payload)) + payload + bytes(32) + u32(20) * 5)
    witness = u32(12) * 3 + headers
    config = (struct.pack("<Q", 1) + u32(12) + u32(4) + u32(8) + u32(16) +
              bytes(16))
    return (bytes([21, 1]) + u32(16) + u32(16 + len(request)) +
            u32(16 + len(request) + len(witness)) +
            u32(56 + len(request) + len(witness)) + request + witness + config)


def withdrawal_count_witness():
    return witness_input(withdrawals=bytes(17 * 44))


def transaction_count_witness():
    return witness_input(transactions=repeated_byte_list(1048577, TRANSACTION))


def witness_header_count_witness():
    return witness_input(headers=repeated_byte_list(257, b""))


if __name__ == "__main__":
    fixtures = {"withdrawals": withdrawal_count_witness,
                "transactions": transaction_count_witness,
                "witness-headers": witness_header_count_witness}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=fixtures)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_bytes(fixtures[args.kind]())
