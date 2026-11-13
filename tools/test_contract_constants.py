"""Check that contract constants match the pinned ELF and its symbol table.

The contracts state some facts of the selected binary as literals: its SHA256
and the addresses of runtime symbols. A binary switch must edit each of them;
this test names every literal that no longer matches. It only checks; it never
edits a contract.
"""
import hashlib
import re
import unittest
from pathlib import Path

from machine_config import read_machine


ROOT = Path(__file__).resolve().parents[1]
ELF = ROOT / "build/stock-zisk/zesu-zisk.elf"
SYMBOLS = ROOT / "build/stock-zisk/symbols.txt"
CONTRACTS = ROOT / "ZesuSsz/Contracts"

# Contract files that state the selected ELF's SHA256.
ELF_HASH_FILES = ["Machine.v", "ParentHeader.v", "RlpDecodeItem.v", "RlpDecodeItemSchema.v"]

# (file, pattern) pairs whose one group is the memcpy entry address
# (Machine.v's mapMemcpyPc is checked with the other machine map symbols).
MEMCPY_SITES = [
    ("ParentHeaderLevel1.v", r"ziskMemcpyEntryPc\) = (0x[0-9a-f]+)"),
    ("ParentHeaderMemcpyService.v", r"Notation memcpyCsrPc := \(\((0x[0-9a-f]+)\) : Z\)"),
]

# defaultMap fields in Machine.v that are the address of one ELF symbol.
MACHINE_SYMBOLS = {
    "mapStartPc": "_start",
    "mapReadInputPc": "read_input",
    "mapWriteOutputPc": "write_output",
    "mapMemcpyPc": "memcpy",
    "mapMainPc": "main",
    "mapHeapTopAddress": "ZKVM_HEAP_TOP",
    "mapHeapPosAddress": "ZKVM_HEAP_POS",
}


def symbol_addresses(text):
    """Every address of each symbol name in `readelf -Ws` output."""
    result = {}
    for row in text.splitlines():
        fields = row.split()
        if len(fields) >= 8 and fields[0].endswith(":") and fields[0][:-1].isdigit():
            result.setdefault(fields[7], set()).add(int(fields[1], 16))
    return result


class ContractConstantDriftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.elf_sha256 = hashlib.sha256(ELF.read_bytes()).hexdigest()
        cls.symbols = symbol_addresses(SYMBOLS.read_text())

    def symbol(self, name):
        addresses = self.symbols.get(name, set())
        self.assertEqual(len(addresses), 1, f"The symbol table needs one address for {name}")
        return next(iter(addresses))

    def test_elf_hash_literals_match_the_pinned_elf(self):
        for name in ELF_HASH_FILES:
            with self.subTest(file=name):
                hashes = set(re.findall(r"\b[0-9a-f]{64}\b", (CONTRACTS / name).read_text()))
                self.assertEqual(hashes, {self.elf_sha256},
                                 f"{name} states another ELF SHA256 than {ELF.name}")

    def test_memcpy_literals_match_the_symbol_table(self):
        memcpy = self.symbol("memcpy")
        for name, pattern in MEMCPY_SITES:
            with self.subTest(file=name):
                found = re.findall(pattern, (CONTRACTS / name).read_text())
                self.assertEqual(len(found), 1, f"{name} has no single memcpy literal")
                self.assertEqual(int(found[0], 16), memcpy, f"{name} states another memcpy address")

    def test_machine_map_symbols_match_the_symbol_table(self):
        machine = read_machine((CONTRACTS / "Machine.v").read_text())
        for field, symbol in MACHINE_SYMBOLS.items():
            with self.subTest(field=field):
                self.assertEqual(machine[field], self.symbol(symbol),
                                 f"Machine.v {field} is not the address of {symbol}")


if __name__ == "__main__":
    unittest.main()
