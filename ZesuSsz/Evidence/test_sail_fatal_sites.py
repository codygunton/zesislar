"""Keep the four decoder roots' rejection classification pinned to Sail sites."""

import os
from pathlib import Path
import re
import subprocess
import unittest


REVISION = "d0e4aabdde52f9158d191dbc8add444abffd9a6a"
EXPECTED = {
    "lib/rlp/decoding.sail": {
        46, 60, 70, 88, 103, 108, 111, 123, 160, 172, 185, 494, 511, 524,
    },
    "lib/ssz/stateless_input.sail": {727, 738},
}
FUNCTIONS = {
    "lib/rlp/decoding.sail": {
        "rlp_ref_hdr", "rlp_decode_list", "rlp_decode_item", "rlp_single_ref",
        "rlp_node_cursor", "rlp_decode_word", "rlp_decode_u256", "rlp_decode_uint64",
    },
    "lib/ssz/stateless_input.sail": {"decode_parent_header_fields"},
}
CALL = re.compile(r"fatal_error\s*\(\s*RlpDecode\s*\)")
FUNCTION = re.compile(r"^\s*function\s+([A-Za-z_][A-Za-z_0-9]*)\b")


def reachable_sites(source: Path, names: set[str]) -> set[int]:
    lines = source.read_text().splitlines()
    starts = [(index, match.group(1)) for index, line in enumerate(lines)
              if (match := FUNCTION.match(line))]
    found_names = {name for _, name in starts if name in names}
    if found_names != names:
        raise AssertionError(f"Missing functions in {source}: {sorted(names - found_names)}")
    found = set()
    for (start, name), (end, _) in zip(starts, starts[1:] + [(len(lines), "")]):
        if name in names:
            found.update(index + 1 for index in range(start, end) if CALL.search(lines[index]))
    return found


class SailFatalSitesTest(unittest.TestCase):
    def test_four_decoder_roots_have_exact_rejection_sites(self) -> None:
        source = Path(os.environ.get("EVM_SAIL_SOURCE", Path.home() / "evm-sail"))
        revision = subprocess.check_output(
            ["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        self.assertEqual(revision, REVISION)
        for path, expected in EXPECTED.items():
            self.assertEqual(reachable_sites(source / "sail" / path, FUNCTIONS[path]), expected)
        generated = (Path(__file__).resolve().parents[2]
                     / "generated/evm-sail-coq/rlp/evm_rlp.v").read_text()
        self.assertEqual(len(CALL.findall(generated)), 16)


if __name__ == "__main__":
    unittest.main()
