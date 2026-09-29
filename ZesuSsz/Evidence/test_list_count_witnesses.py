#!/usr/bin/env python3
"""Check the complete encoded count witnesses without a Rocq premise."""

import re
import struct
import unittest
from pathlib import Path

from list_count_witnesses import (
    TRANSACTION, transaction_count_witness, withdrawal_count_witness,
    witness_header_count_witness,
)


ROOT = Path(__file__).resolve().parents[2]


def read_u32(data, offset):
    return struct.unpack_from("<I", data, offset)[0]


def container(data, positions, fixed_length):
    offsets = [read_u32(data, position) for position in positions] + [len(data)]
    if offsets[0] != fixed_length or offsets != sorted(offsets):
        raise ValueError("The container offsets are invalid.")
    return [data[start:end] for start, end in zip(offsets, offsets[1:])]


def variable_items(data):
    if not data:
        return
    first = read_u32(data, 0)
    if first == 0 or first % 4 or first > len(data):
        raise ValueError("The list offset table is invalid.")
    count = first // 4
    start = first
    for index in range(count):
        end = read_u32(data, 4 * (index + 1)) if index + 1 < count else len(data)
        if end < start or end > len(data):
            raise ValueError("The list item offsets are invalid.")
        yield data[start:end]
        start = end


def legacy_rlp_fields(encoded):
    """Read the short RLP list and canonical scalar fields in this fixture."""
    if not encoded or not 192 <= encoded[0] <= 247:
        raise ValueError("The transaction is not a short RLP list.")
    if encoded[0] - 192 != len(encoded) - 1:
        raise ValueError("The RLP list length is invalid.")
    fields = []
    position = 1
    while position < len(encoded):
        tag = encoded[position]
        position += 1
        if tag < 128:
            fields.append(bytes([tag]))
        elif tag <= 183:
            size = tag - 128
            end = position + size
            if end > len(encoded) or (size == 1 and encoded[position] < 128):
                raise ValueError("The RLP scalar encoding is invalid.")
            fields.append(bytes(encoded[position:end]))
            position = end
        else:
            raise ValueError("The fixture contains an unexpected RLP field.")
    if len(fields) != 9:
        raise ValueError("A legacy transaction requires nine fields.")
    for index, width in ((0, 8), (1, 16), (2, 8), (4, 32), (6, 32), (7, 32), (8, 32)):
        value = fields[index]
        if len(value) > width or (value and value[0] == 0):
            raise ValueError("The transaction integer encoding is invalid.")
    if len(fields[3]) not in (0, 20):
        raise ValueError("The transaction recipient length is invalid.")
    return fields


class ListCountWitnessTests(unittest.TestCase):
    def fields(self, encoded):
        self.assertLessEqual(len(encoded), 64 * 1024 * 1024)
        self.assertEqual(encoded[:2], bytes([21, 1]))
        request, witness, config, keys = container(memoryview(encoded)[2:], (0, 4, 8, 12), 16)
        payload, hashes, requests = container(request, (0, 4, 40), 44)
        extra, transactions, withdrawals, access = container(payload, (436, 504, 508, 528), 540)
        nodes, codes, headers = container(witness, (0, 4, 8), 12)
        # Check that the seven original divergence domains do not apply.
        self.assertEqual(len(extra), 0)
        self.assertEqual(len(hashes), 32)
        self.assertEqual(len(keys), 0)
        self.assertTrue(all(len(part) == 0 for part in container(requests, (0, 4, 8, 12, 16), 20)))
        self.assertEqual(bytes(config), struct.pack("<QIIIIQQ", 1, 12, 4, 8, 16, 0, 0))
        self.assertEqual(struct.unpack_from("<Q", payload, 404)[0], 0)
        self.assertEqual(struct.unpack_from("<Q", payload, 428)[0], 0)
        self.assertEqual(bytes(nodes), b"")
        self.assertEqual(bytes(codes), b"")
        self.assertEqual(bytes(access), b"")
        return transactions, withdrawals, headers

    def test_withdrawal_count_mismatch(self):
        transactions, withdrawals, headers = self.fields(withdrawal_count_witness())
        self.assertEqual(len(withdrawals) % 44, 0)
        self.assertEqual(len(withdrawals) // 44, 17)
        self.assertGreater(len(withdrawals) // 44, 16)
        self.assertEqual(list(variable_items(transactions)), [])
        self.assertEqual(list(variable_items(headers)), [])

    def test_transaction_count_mismatch(self):
        encoded = transaction_count_witness()
        transactions, withdrawals, headers = self.fields(encoded)
        self.assertEqual(len(encoded), 14680784)
        self.assertEqual(len(transactions), 14680078)
        self.assertEqual(read_u32(transactions, 0), 4194308)
        expected = [b"", b"", b"", b"", b"", b"", bytes([27]), b"", b""]
        count = 0
        for item in variable_items(transactions):
            self.assertEqual(legacy_rlp_fields(item), expected)
            count += 1
        self.assertEqual(count, 1048577)
        self.assertGreater(count, 2 ** 20)
        self.assertEqual(bytes(withdrawals), b"")
        self.assertEqual(list(variable_items(headers)), [])

    def test_witness_header_count_mismatch(self):
        transactions, withdrawals, headers = self.fields(witness_header_count_witness())
        items = list(variable_items(headers))
        self.assertEqual(len(items), 257)
        self.assertTrue(all(len(item) == 0 for item in items))
        self.assertGreater(len(items), 256)
        self.assertEqual(list(variable_items(transactions)), [])
        self.assertEqual(bytes(withdrawals), b"")

    def test_rocq_fixture_parameters_agree(self):
        source = (ROOT / "ZesuSsz/Compliance/ListCountExamples.v").read_text()
        item = re.search(r"Definition zesuCountWitnessTransaction.*?\[([^]]+)\]", source, re.S)
        self.assertEqual(bytes(int(value.strip()) for value in item[1].split(";")), TRANSACTION)
        self.assertRegex(source, r"repeat 0 \(17 \* 44\)")
        self.assertRegex(source, r"zesuEncodeRepeatedByteList 1048577 zesuCountWitnessTransaction")
        self.assertRegex(source, r"zesuEncodeRepeatedByteList 257 \[\]")

    def test_reference_limits_agree(self):
        source = (ROOT / "generated/evm-sail-coq/evm_decoder.v").read_text()
        for name, exponent in (("WITHDRAWALS_PER_PAYLOAD", 4),
                               ("TRANSACTIONS_PER_PAYLOAD", 20), ("WITNESS_HEADERS", 8)):
            self.assertRegex(source, rf"Definition MAX_{name} := \(\(pow2 \({exponent}\)\)\)")

    def test_invalid_offsets_and_rlp_fail(self):
        for encoded in (bytes([0, 0, 0, 0]), bytes([8, 0, 0, 0, 4, 0, 0, 0])):
            with self.assertRaises(ValueError):
                list(variable_items(encoded))
        for encoded in (b"", bytes([201, 128]), bytes([192]), bytes([193, 129, 0])):
            with self.assertRaises(ValueError):
                legacy_rlp_fields(encoded)


if __name__ == "__main__":
    unittest.main()
