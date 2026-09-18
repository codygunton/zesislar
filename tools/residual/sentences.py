"""Split a Rocq proof body into whole sentences.

The replay of section 10 E1 inserts a probe between the original lines of a
proof. A source line is the wrong unit: a tactic often spans several lines,
and a line often holds several tactics. Rocq ends a sentence at a `.`
followed by whitespace or end of input, and treats `{`, `}` and the bullets
as sentences of their own.
"""

from __future__ import annotations

import re

BULLETS = set("-+*")
OPEN_COMMENT = "(*"
CLOSE_COMMENT = "*)"


def split_sentences(body: str) -> list[str]:
    """Every sentence of `body`, in order, comments and blank lines dropped."""
    sentences: list[str] = []
    current: list[str] = []
    depth = 0          # comment nesting
    in_string = False
    index = 0
    while index < len(body):
        character = body[index]
        if depth:
            if body.startswith(CLOSE_COMMENT, index):
                depth -= 1
                index += 2
                continue
            if body.startswith(OPEN_COMMENT, index):
                depth += 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            current.append(character)
            if character == '"':
                in_string = False
            index += 1
            continue
        if body.startswith(OPEN_COMMENT, index):
            depth += 1
            index += 2
            continue
        if character == '"':
            in_string = True
            current.append(character)
            index += 1
            continue
        if character in "{}" and not "".join(current).strip():
            sentences.append(character)
            current = []
            index += 1
            continue
        if character in BULLETS and not "".join(current).strip() \
                and _is_bullet(body, index):
            run = _bullet_run(body, index)
            sentences.append(run)
            index += len(run)
            continue
        current.append(character)
        if character == "." and _ends_sentence(body, index):
            sentence = "".join(current).strip()
            if sentence:
                sentences.append(sentence)
            current = []
        index += 1
    tail = "".join(current).strip()
    if tail:
        sentences.append(tail)
    return sentences


def _ends_sentence(body: str, index: int) -> bool:
    """A `.` ends a sentence when whitespace or the end of input follows."""
    if index + 1 >= len(body):
        return True
    return body[index + 1].isspace()


def _bullet_run(body: str, index: int) -> str:
    character = body[index]
    end = index
    while end < len(body) and body[end] == character:
        end += 1
    return body[index:end]


def _is_bullet(body: str, index: int) -> bool:
    """A run of `-`, `+` or `*` alone on its line is a bullet, not a term."""
    run = _bullet_run(body, index)
    after = index + len(run)
    return after >= len(body) or body[after].isspace()


def opener_and_steps(body: str) -> tuple[list[str], list[str]]:
    """The proof's sentences, split into its opener and the rest.

    The opener is what puts the proof into Iris proof mode. Nothing before it
    can be replaced by the automation, so the replay starts after it.
    """
    sentences = split_sentences(body)
    opener: list[str] = []
    for index, sentence in enumerate(sentences):
        if re.match(r"^(move\s*=>|intros?\b|iStartProof\b)", sentence):
            opener.append(sentence)
            continue
        return opener, sentences[index:]
    return opener, []
