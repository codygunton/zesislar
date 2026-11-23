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

Range bounds. A code-disjointness disjunction `x + n <= A \\/ B <= x` (exporter form
`@Coq.Init.Logic.or` of two `Z.le`, possibly beside `false = true` disjuncts) names its bounds A and
B by literal; they are ELF section bounds, not symbols, and A is often 2^31, which name_of never
rewrites. When both are section bounds of Symbols.v (`sec_<section>_start`/`_end`,
tools/oblig/render_symbols.py), both literals are written as those notations, whatever their value.
A goal whose code addresses all sat in such bounds is a pure range goal; one where a binder equals
a code address keeps class ADDRESS unless the address is a symbol.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SYMBOLS_FILE = ROOT / "ZesuSsz/Generated/Stock/Symbols.v"
MODULE = "ZesuSsz.Generated.Stock.Symbols"
REQUIRE = "Require Import %s." % MODULE
MAX_OFFSET = 0x1000
NOTATION = re.compile(r"^Notation (sym_\w+) := \(\(0x([0-9a-fA-F]+)\) : Z\) \(only parsing\)\.$", re.M)
SECTION = re.compile(r"^Notation (sec_\w+) := \(\(0x([0-9a-fA-F]+)\) : Z\) \(only parsing\)\.$", re.M)
LITERAL = re.compile(r"^\((0x[0-9a-fA-F]+|\d+)\)%Z$")
OR, LE, ADD = "@Coq.Init.Logic.or", "@Coq.ZArith.BinInt.Z.le", "@Coq.ZArith.BinInt.Z.add"
FALSE_TRUE = "(@Coq.Init.Logic.eq (@Coq.Init.Datatypes.bool) (@Coq.Init.Datatypes.false) (@Coq.Init.Datatypes.true))"
RANGE_DISPLAY = re.compile(r"(≤\s*)(0x[0-9a-fA-F]+|\d+)(\s*∨\s*)(0x[0-9a-fA-F]+|\d+)(?=\s*≤)")
SCOPED = re.compile(r"\((0x[0-9a-fA-F]+|\d+)\)%Z")
ZPOS = re.compile(r"\bZpos\b")
WORD = re.compile(r"(?<![\w'.])(0x[0-9a-fA-F]+|\d+)(?![\w'])")


def table(path=SYMBOLS_FILE):
    """[(address, notation name)] of Symbols.v, by address."""
    path = Path(path)
    if not path.is_file():
        return []
    return sorted((int(value, 16), name) for name, value in NOTATION.findall(path.read_text()))


def sections(path=SYMBOLS_FILE):
    """{address: notation name} of the section bounds of Symbols.v (the first name of a shared value)."""
    path = Path(path)
    if not path.is_file():
        return {}
    out = {}
    for name, value in SECTION.findall(path.read_text()):
        out.setdefault(int(value, 16), name)
    return out


def literal_value(token):
    found = LITERAL.match(token)
    if not found:
        return None
    return int(found[1], 0) if found[1].startswith("0x") else int(found[1])


def tokens(text, start, end, limit=None):
    """[(start, end)] of the top-level terms of TEXT[start:end] (at most LIMIT): a parenthesised group
    (with a scope suffix such as `%Z`) or an atom."""
    import similar
    out, i = [], start
    while i < end and (limit is None or len(out) < limit):
        if text[i].isspace():
            i += 1
            continue
        j = i
        if text[i] == "(":
            close = similar.matching(text, i)
            if close is None or close >= end:
                return out
            j = close + 1
        while j < end and not text[j].isspace() and text[j] not in "()":
            j += 1
        out.append((i, j))
        i = j
    return out


def application(text, span):
    """(head, [argument spans]) of a group `(@f a b)` at SPAN, else None."""
    start, end = span
    if text[start] != "(" or text[end - 1] != ")":
        return None
    parts = tokens(text, start + 1, end - 1)
    return (text[parts[0][0]:parts[0][1]], parts[1:]) if parts else None


def disjuncts(text, span):
    app = application(text, span)
    if app and app[0] == OR and len(app[1]) == 2:
        return disjuncts(text, app[1][0]) + disjuncts(text, app[1][1])
    return [span]


def flat(text, span):
    return " ".join(text[span[0]:span[1]].split())


def range_bounds(text):
    """[((A start, A end, A value), (B start, B end, B value))] of every disjunction
    `x + n <= A \\/ B <= x` (either order, `false = true` disjuncts dropped) with literal A and B."""
    found = []
    for match in re.finditer(r"\(" + re.escape(OR) + r"\s", text):
        span = tokens(text, match.start(), len(text), limit=1)
        if not span:
            continue
        rest = [d for d in disjuncts(text, span[0]) if flat(text, d) != FALSE_TRUE]
        if len(rest) != 2:
            continue
        les = [application(text, d) for d in rest]
        if not all(app and app[0] == LE and len(app[1]) == 2 for app in les):
            continue
        for upper, lower in ((les[0], les[1]), (les[1], les[0])):
            add = application(text, upper[1][0])
            a, b = upper[1][1], lower[1][0]
            values = literal_value(text[a[0]:a[1]]), literal_value(text[b[0]:b[1]])
            if (add and add[0] == ADD and len(add[1]) == 2 and None not in values
                    and flat(text, add[1][0]) == flat(text, lower[1][1])):
                pair = ((a[0], a[1], values[0]), (b[0], b[1], values[1]))
                if pair not in found:
                    found.append(pair)
                break
    return found


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


def statement(text, symbols, bounds=None):
    """(rewritten text, [(literal, notation)]) of a Coq statement: the range bounds that are section
    bounds of BOUNDS ({address: notation}), then `(N)%Z` and `Zpos <positive>` symbol literals."""
    import falsify
    found = []
    spans = sorted({bound for pair in range_bounds(text) if all(v in bounds for _, _, v in pair)
                    for bound in pair}) if bounds else []
    for start, end, value in reversed(spans):
        found.insert(0, (LITERAL.match(text[start:end])[1], bounds[value]))
        text = text[:start] + "(%s)%%Z" % bounds[value] + text[end:]

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


def display(text, symbols, bounds=None):
    """TEXT with every hex or decimal literal that maps to a symbol written as its notation, and the
    bounds of a readable range disjunction `≤ A ∨ B ≤` that are both section bounds as theirs."""
    def word(match):
        value = int(match[1], 0) if match[1].startswith("0x") else int(match[1])
        return name_of(value, symbols) or match[0]

    def bound(match):
        values = [int(v, 0) if v.startswith("0x") else int(v) for v in (match[2], match[4])]
        if not bounds or not all(v in bounds for v in values):
            return match[0]
        return match[1] + bounds[values[0]] + match[3] + bounds[values[1]]
    return WORD.sub(word, RANGE_DISPLAY.sub(bound, text))


def with_require(header_lines):
    """The header with the Symbols import added before its first non-Require line."""
    if REQUIRE in header_lines:
        return list(header_lines)
    lines = list(header_lines)
    at = max((n + 1 for n, line in enumerate(lines) if line.startswith(("Require ", "From "))), default=0)
    return lines[:at] + [REQUIRE] + lines[at:]
