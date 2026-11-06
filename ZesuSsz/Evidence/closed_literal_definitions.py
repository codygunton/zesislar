"""Find closed numeric definitions without evaluating symbolic Rocq terms."""
from dataclasses import dataclass
import hashlib
import re
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools/block"))
from check_data_only_lemmas import rocq_commands, rocq_tokens

RULE = "CONST-NOTATION"
NUMERIC_TYPE = re.compile(r"(?:Z|N|nat|positive|bv\s*\(?\s*\d+(?:%N)?\s*\)?)\Z")
PRIMITIVES = {"Z_to_bv", "BV", "bv_modulus", "Z0", "Zpos", "Zneg", "N0", "Npos",
              "O", "S", "xH", "xI", "xO", "Z", "N", "nat", "positive", "bv", "mod"}
for namespace in ["Z", "N", "Nat", "Pos"]:
    PRIMITIVES.update(namespace + "." + name for name in [
        "add", "sub", "mul", "div", "modulo", "rem", "quot", "pow", "opp", "abs",
        "succ", "pred", "min", "max", "ones", "shiftl", "shiftr", "land", "lor",
        "lxor", "lnot", "log2", "sqrt", "of_nat", "of_N", "to_nat", "to_N"])
TOKEN = re.compile(r"0[xX][0-9a-fA-F]+|\d+|[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\S")
SYMBOLS = set("()+-*/^%:@")


@dataclass(frozen=True)
class LiteralDefinition:
    name: str
    type: str
    body: str
    start: int
    end: int
    line: int
    source: str

    @property
    def digest(self):
        return hashlib.sha256(self.source.encode()).hexdigest()


def code_text(text):
    result = ["\n" if character == "\n" else " " for character in text]
    for token, offset in rocq_tokens(text):
        result[offset:offset + len(token)] = token
    return "".join(result)


def literal_expression(body, known=()):
    tokens = TOKEN.findall(code_text(body))
    return bool(tokens) and any(token[0].isdigit() or token in {"O", "Z0", "N0", "xH"}
                                for token in tokens) and all(
        token in SYMBOLS or token in PRIMITIVES or token in known or token[0].isdigit()
        for token in tokens)


def closed_literal_definitions(text):
    result = []
    commands = rocq_commands(text)
    known = set()
    for command in commands:
        values = [token for token, _ in command]
        if len(values) > 4 and values[:1] == ["Notation"] and values[2] == ":=":
            last, offset = command[-1]
            body = text[command[2][1] + 2:offset + len(last)]
            body = re.sub(r"\(\s*only\s+parsing\s*\)\s*$", "", body)
            if literal_expression(body, known):
                known.add(values[1])
    for command in commands:
        tokens = [token for token, _ in command]
        while tokens and tokens[0] in ["Local", "Global", "Polymorphic", "Monomorphic"]:
            tokens, command = tokens[1:], command[1:]
        if tokens[:2] == ["#", "["]:
            try:
                end_attribute = tokens.index("]") + 1
            except ValueError:
                continue
            tokens, command = tokens[end_attribute:], command[end_attribute:]
        if len(tokens) < 4 or tokens[0] != "Definition" or tokens[2] not in [":", ":="]:
            continue
        try:
            assignment = tokens.index(":=")
        except ValueError:
            continue
        type_text = text[command[2][1] + 1:command[assignment][1]].strip() if tokens[2] == ":" else ""
        if type_text and not NUMERIC_TYPE.fullmatch(type_text):
            continue
        body_start = command[assignment][1] + 2
        last, offset = command[-1]
        end = offset + len(last)
        body = text[body_start:end].strip()
        if not literal_expression(body, known):
            continue
        start = command[0][1]
        result.append(LiteralDefinition(tokens[1], type_text, body, start, end + 1,
                                        text.count("\n", 0, start) + 1, text[start:end + 1]))
    return result


def closed_literal_failures(name, text, exceptions):
    if name.startswith("ZesuSsz/Automation/"):
        return []
    failures = []
    for constant in closed_literal_definitions(text):
        approved = exceptions.get((name, constant.name))
        if approved and approved.get("reason") and approved.get("sha256") == constant.digest:
            continue
        failures.append(f"{RULE}: {name}:{constant.line}: {constant.name} must use parsing-only "
                        "Notation; see AGENTS.md Constants and the reviewed exception allowlist.")
    return failures
