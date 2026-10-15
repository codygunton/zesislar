"""Read event identity fields without retaining snapshot or feedback payloads."""

import json
from pathlib import Path
import re


class _Reader:
    """Read UTF-8 JSON with bounded buffers and an iterative container stack."""

    def __init__(self, stream):
        self.stream = stream
        self.buffer = ""
        self.offset = 0

    def peek(self):
        if self.offset == len(self.buffer):
            self.buffer = self.stream.read(65536)
            self.offset = 0
        return self.buffer[self.offset:self.offset + 1]

    def take(self):
        value = self.peek()
        if not value:
            raise ValueError("A raw event contains incomplete JSON.")
        self.offset += 1
        return value

    def space(self):
        while self.peek():
            match = re.match(r"[ \t\r\n]*", self.buffer[self.offset:])
            self.offset += match.end()
            if self.offset < len(self.buffer):
                return

    def expect(self, expected):
        self.space()
        if self.take() != expected:
            raise ValueError("A raw event contains invalid JSON structure.")

    def string(self, retain=False):
        if self.take() != '"':
            raise ValueError("A raw event contains an invalid JSON string.")
        parts = ['"'] if retain else None
        length = 1
        while self.peek():
            match = re.search(r'["\\\x00-\x1f]', self.buffer[self.offset:])
            end = self.offset + match.start() if match else len(self.buffer)
            part = self.buffer[self.offset:end]
            self.offset = end
            if retain:
                parts.append(part)
                length += len(part)
                if length > 65536:
                    raise ValueError("A raw event identity field exceeds 65536 characters.")
            if match is None:
                continue
            char = self.take()
            if char == '"':
                return json.loads("".join(parts) + '"') if retain else None
            if char != "\\":
                raise ValueError("A raw event string contains a control character.")
            escape = self.take()
            suffix = escape
            if escape == "u":
                digits = "".join(self.take() for _ in range(4))
                if not re.fullmatch(r"[0-9a-fA-F]{4}", digits):
                    raise ValueError("A raw event string has an invalid Unicode escape.")
                suffix += digits
            elif escape not in '"\\/bfnrt':
                raise ValueError("A raw event string has an invalid escape.")
            if retain:
                parts.append("\\" + suffix)
                length += 1 + len(suffix)
        raise ValueError("A raw event contains an unterminated JSON string.")

    def scalar(self):
        self.space()
        if self.peek() == '"':
            return self.string(retain=True)
        parts = []
        while self.peek() and self.peek() not in " \t\r\n,]}":
            parts.append(self.take())
            if len(parts) > 65536:
                raise ValueError("A raw event scalar exceeds 65536 characters.")
        token = "".join(parts)
        if not re.fullmatch(r"(?:null|true|false|-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)", token):
            raise ValueError("A raw event contains an invalid JSON scalar.")
        return json.loads(token)

    def skip_value(self):
        states = ["value"]
        while states:
            self.space()
            state = states.pop()
            char = self.peek()
            if state == "value":
                if char == '"':
                    self.string()
                elif char == "{":
                    self.take()
                    states.append("object_first")
                elif char == "[":
                    self.take()
                    states.append("array_first")
                else:
                    self.scalar()
            elif state in ("object_first", "object_next"):
                if char == "}" and state == "object_first":
                    self.take()
                    continue
                self.string()
                self.expect(":")
                states.extend(("object_tail", "value"))
            elif state == "object_tail":
                if self.take() == "}":
                    continue
                if char != ",":
                    raise ValueError("A raw event contains an invalid JSON object.")
                states.append("object_next")
            elif state in ("array_first", "array_next"):
                if char == "]" and state == "array_first":
                    self.take()
                    continue
                states.extend(("array_tail", "value"))
            else:
                if self.take() == "]":
                    continue
                if char != ",":
                    raise ValueError("A raw event contains an invalid JSON array.")
                states.append("array_next")


def read_event_identity(path):
    """Validate JSON syntax and retain only top-level identity fields."""
    with Path(path).open(encoding="utf-8") as stream:
        reader = _Reader(stream)
        reader.expect("{")
        fields = {}
        keys = set()
        reader.space()
        if reader.peek() != "}":
            while True:
                reader.space()
                key = reader.string(retain=True)
                if key in keys:
                    raise ValueError("A raw event contains a duplicate top-level field.")
                keys.add(key)
                reader.expect(":")
                if key in ("kind", "rule", "invocation", "trial"):
                    fields[key] = reader.scalar()
                else:
                    reader.skip_value()
                reader.space()
                if reader.peek() != ",":
                    break
                reader.take()
        reader.expect("}")
        reader.space()
        if reader.peek():
            raise ValueError("A raw event contains trailing JSON content.")
        if not isinstance(fields.get("kind"), str):
            raise ValueError("A raw event lacks its kind.")
        return fields
