"""Keep the decoder roots' rejection classification pinned to Sail sites."""

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
# decode_access_list runs from the transaction closure (runDecodeAccessList).
ACCESS_LIST_EXPECTED = {
    "lib/rlp/decoding.sail": {46, 60, 70, 88, 103, 108, 111, 123, 147, 494},
    "lib/rlp/codecs/transactions.sail": {103},
}
ACCESS_LIST_FUNCTIONS = {
    "lib/rlp/decoding.sail": {
        "rlp_ref_hdr", "rlp_decode_list", "rlp_decode_item", "rlp_decode_word",
        "rlp_cursor_expect_end",
    },
    "lib/rlp/codecs/transactions.sail": {
        "transaction_rlp_content", "decode_access_list_keys",
        "decode_access_list_entries", "decode_access_list",
    },
}
CALL = re.compile(r"fatal_error\s*\(\s*RlpDecode\s*\)")
FUNCTION = re.compile(r"^\s*function\s+([A-Za-z_][A-Za-z_0-9]*)\b")
PUBLIC_ROOT = re.compile(
    r"^Definition\s+(run(?:Rlp|ParentHeader|DecodeAccessList)\w*)\b", re.MULTILINE)
APPROVED_ROOTS = {
    "runRlpDecodeItem", "runRlpRefHdr", "runRlpNodeCursor",
    "runParentHeaderFields", "runRlpDecodeU256", "runRlpDecodeUint64",
    "runDecodeAccessList",
}


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


def generated_closure(source: str, root: str) -> dict[str, str]:
    """Definitions of a generated Sail module that the root reaches."""
    definitions = {}
    for chunk in re.split(r"\n(?=(?:Definition|Fixpoint) )", source):
        if match := re.match(r"(?:Definition|Fixpoint) (\w+)", chunk):
            definitions[match.group(1)] = chunk
    reached, pending = {}, [root]
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached[name] = definitions[name]
        body = definitions[name].split(name, 1)[1]
        pending.extend(token for token in set(re.findall(r"\w+", body))
                       if token in definitions and token != name)
    return reached


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
        runners = Path(__file__).resolve().parents[1] / "Compliance"
        roots = set()
        for runner in ("SailRun.v", "SailRunAccessList.v"):
            roots.update(PUBLIC_ROOT.findall((runners / runner).read_text()))
        self.assertEqual(roots, APPROVED_ROOTS)

    def test_access_list_root_has_exact_rejection_sites(self) -> None:
        source = Path(os.environ.get("EVM_SAIL_SOURCE", Path.home() / "evm-sail"))
        revision = subprocess.check_output(
            ["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        self.assertEqual(revision, REVISION)
        for path, expected in ACCESS_LIST_EXPECTED.items():
            self.assertEqual(
                reachable_sites(source / "sail" / path, ACCESS_LIST_FUNCTIONS[path]), expected)
        generated = (Path(__file__).resolve().parents[2] / "generated/evm-sail-coq"
                     / "transactions/evm_decode_access_list_tx.v").read_text()
        closure = generated_closure(generated, "decode_access_list")
        rejecting = {name for name, text in closure.items() if CALL.search(text)}
        self.assertEqual(rejecting, set().union(*ACCESS_LIST_FUNCTIONS.values())
                         - {"transaction_rlp_content", "decode_access_list_keys",
                            "decode_access_list_entries"})
        self.assertEqual(sum(len(CALL.findall(closure[name])) for name in rejecting),
                         sum(map(len, ACCESS_LIST_EXPECTED.values())))


if __name__ == "__main__":
    unittest.main()
