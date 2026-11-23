"""Address literals of an exported goal back to the symbol notations of ZesuSsz/Generated/Stock/Symbols.v.

A residual goal that names a code or data address by its literal is not relocatable
(tools/oblig/check_relocatable.py). When the address is that of a symbol listed in
tools/oblig/symbols.json, or lies at most MAX_OFFSET bytes above one, the literal is written
`sym_<name>` or `(sym_<name> + <offset>)`. The notations are parsing-only and typed `Z`, so an
exact symbol gives the same term; a symbol plus offset gives a `Z.add` that computes to it. The
caller checks the identity with the kernel (package.py).

Only literals whose type is fixed to `Z` are rewritten in a statement: `(<literal>)%Z` (the
exporter's form) and positive constructor terms under `Zpos`. A literal of another scope stays,
so its goal stays class ADDRESS. In display text (a task's readable goal) every hex or decimal
literal that maps to a symbol is rewritten.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SYMBOLS_FILE = ROOT / "ZesuSsz/Generated/Stock/Symbols.v"
MODULE = "ZesuSsz.Generated.Stock.Symbols"
REQUIRE = "Require Import %s." % MODULE
MAX_OFFSET = 0x1000
NOTATION = re.compile(r"^Notation (sym_\w+) := \(\(0x([0-9a-fA-F]+)\) : Z\) \(only parsing\)\.$", re.M)
SCOPED = re.compile(r"\((0x[0-9a-fA-F]+|\d+)\)%Z")
ZPOS = re.compile(r"\bZpos\b")
WORD = re.compile(r"(?<![\w'.])(0x[0-9a-fA-F]+|\d+)(?![\w'])")


def table(path=SYMBOLS_FILE):
    """[(address, notation name)] of Symbols.v, by address."""
    path = Path(path)
    if not path.is_file():
        return []
    return sorted((int(value, 16), name) for name, value in NOTATION.findall(path.read_text()))


def name_of(value, symbols, max_offset=MAX_OFFSET):
    """`sym_x` for a symbol's address, `(sym_x + off)` within MAX_OFFSET above one, else None. A power of
    two or one less (2^31 is also the entry of rlp_decode.txAccessList) is an arithmetic constant as
    much as an address: it is never rewritten, and its goal stays class ADDRESS for the owner."""
    if value <= 0 or value & (value - 1) == 0 or value & (value + 1) == 0:
        return None
    below = [(address, name) for address, name in symbols if address <= value < address + max_offset + 1]
    if not below:
        return None
    address, name = max(below)
    return name if value == address else "(%s + %d)" % (name, value - address)


def statement(text, symbols):
    """(rewritten text, [(literal, notation)]) of a Coq statement: `(N)%Z` and `Zpos <positive>`."""
    import falsify
    found = []

    def scoped(match):
        value = int(match[1], 0) if match[1].startswith("0x") else int(match[1])
        name = name_of(value, symbols)
        if name is None:
            return match[0]
        found.append((match[1], name))
        return "(%s)%%Z" % name
    text = SCOPED.sub(scoped, text)
    out, i = [], 0
    for match in ZPOS.finditer(text):
        if match.start() < i:
            continue
        parsed = falsify.parse_positive(text, match.end())
        name = name_of(parsed[0], symbols) if parsed else None
        if name is None:
            continue
        out.append(text[i:match.start()] + "(%s)" % name)
        found.append((text[match.start():parsed[1]], name))
        i = parsed[1]
    return "".join(out) + text[i:], found


def display(text, symbols):
    """TEXT with every hex or decimal literal that maps to a symbol written as its notation."""
    def word(match):
        value = int(match[1], 0) if match[1].startswith("0x") else int(match[1])
        return name_of(value, symbols) or match[0]
    return WORD.sub(word, text)


def with_require(header_lines):
    """The header with the Symbols import added before its first non-Require line."""
    if REQUIRE in header_lines:
        return list(header_lines)
    lines = list(header_lines)
    at = max((n + 1 for n, line in enumerate(lines) if line.startswith(("Require ", "From "))), default=0)
    return lines[:at] + [REQUIRE] + lines[at:]
