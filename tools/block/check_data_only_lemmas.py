"""Check the data-only modules listed in each function text manifest."""

import json
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CATEGORIES = ("contracts", "introductions", "exit_meanings", "loop_steps",
              "registrations", "generator_json")
DATA_CATEGORIES = ("introductions", "exit_meanings", "loop_steps")
FORBIDDEN = re.compile(r"instr_body|instr_pre|WPasm|liAStep|zesu_block|zesu_liAStep")
REGISTRATION_CLASSES = {"ZesuEntryIntro", "ZesuLoopStep"}
IDENTIFIER = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")


@dataclass(frozen=True)
class Registration:
    name: str
    class_name: str
    predicate: str
    line: int


def rocq_tokens(text: str) -> list[tuple[str, int]]:
    """Retain code tokens and offsets, excluding nested comments and strings."""
    tokens, position, depth = [], 0, 0
    while position < len(text):
        if text[position] == '"':
            start = position
            position += 1
            while position < len(text):
                if text.startswith('""', position):
                    position += 2
                elif text[position] == '"':
                    position += 1
                    break
                else:
                    position += 1
            else:
                raise ValueError("The registration module has an unterminated string.")
            if not depth:
                tokens.append((text[start:position], start))
        elif text.startswith("(*", position):
            depth += 1
            position += 2
        elif depth and text.startswith("*)", position):
            depth -= 1
            position += 2
        elif depth or text[position].isspace():
            position += 1
        else:
            word = IDENTIFIER.match(text, position)
            operator = next((item for item in (":=", "->", "=>")
                             if text.startswith(item, position)), None)
            token = word.group() if word else operator or text[position]
            tokens.append((token, position))
            position += len(token)
    if depth:
        raise ValueError("The registration module has an unterminated comment.")
    return tokens


def rocq_commands(text: str) -> list[list[tuple[str, int]]]:
    commands, current, brackets = [], [], []
    matching = {")": "(", "]": "[", "}": "{"}
    for token in rocq_tokens(text):
        value = token[0]
        if value in ("(", "[", "{"):
            brackets.append(value)
        elif value in (")", "]", "}"):
            if not brackets or brackets.pop() != matching[value]:
                raise ValueError("The registration module has mismatched delimiters.")
        if value == "." and not brackets:
            commands.append(current)
            current = []
        else:
            current.append(token)
    if brackets:
        raise ValueError("The registration module has an unbalanced argument.")
    if current:
        commands.append(current)
    return commands


def top_level_positions(values: list[str], wanted: set[str]) -> list[int]:
    result, depth = [], 0
    for index, value in enumerate(values):
        if depth == 0 and value in wanted:
            result.append(index)
        if value in ("(", "[", "{"):
            depth += 1
        elif value in (")", "]", "}"):
            depth -= 1
    return result


def atom(values: list[str], position: int) -> tuple[list[str], int]:
    if position >= len(values):
        raise ValueError("The registration has a missing class argument.")
    if values[position] in ("(", "[", "{"):
        opening, depth = position, 1
        position += 1
        while position < len(values) and depth:
            if values[position] in ("(", "[", "{"):
                depth += 1
            elif values[position] in (")", "]", "}"):
                depth -= 1
            position += 1
        if depth:
            raise ValueError("The registration has an unbalanced argument.")
        return values[opening + 1:position - 1], position
    if values[position] == "@":
        return values[position:position + 2], position + 2
    return values[position:position + 1], position + 1


def predicate_head(values: list[str]) -> str:
    while values and values[0] == "(":
        values, _ = atom(values, 0)
    if values and values[0] == "@":
        values = values[1:]
    if (not values or not IDENTIFIER.fullmatch(values[0]) or
            values[0] in {"fun", "let", "match", "if", "forall", "ltac"}):
        raise ValueError("The registration source needs a named predicate head.")
    return values[0]


def instance_conclusion(values: list[str]) -> list[str]:
    """Remove outer parentheses, quantified binders, and premise arrows."""
    while values:
        if values[0] == "(":
            inside, end = atom(values, 0)
            if end == len(values):
                values = inside
                continue
        if values[0] in {"forall", "∀"}:
            commas = top_level_positions(values, {","})
            if commas:
                values = values[commas[0] + 1:]
                continue
        arrows = top_level_positions(values, {"->", "→"})
        if arrows:
            values = values[arrows[-1] + 1:]
            continue
        break
    return values


def command_imports(values: list[str]) -> tuple[list[str], bool]:
    """Read imported or exported module names, including From prefixes."""
    prefix = ""
    if values and values[0] == "From" and "Require" in values:
        prefix = values[1] + "."
        values = values[values.index("Require"):]
    if values and values[0] == "Require":
        values = values[1:]
    if not values or values[0] not in {"Import", "Export"}:
        return [], False
    return [prefix + value for value in values[1:]
            if IDENTIFIER.fullmatch(value)], values[0] == "Export"


class PredicateResolver:
    """Resolve source heads through repository declarations and module imports."""

    def __init__(self, root: Path, modules: set[Path], aliases: dict[str, str]):
        self.root = root
        self.modules = modules
        self.aliases = aliases
        self.canonical_aliases = {}
        self.symbols = set()
        self.alias_symbols = set()
        self.exports = {}
        self.loaded = set()

    def load(self, module: str) -> None:
        parts = module.split(".")
        for length in range(len(parts), 0, -1):
            path = self.root.joinpath(*parts[:length]).with_suffix(".v")
            if path in self.modules:
                owner = ".".join(parts[:length])
                break
        else:
            return  # External libraries cannot define a repository source predicate.
        if owner in self.loaded:
            return
        self.loaded.add(owner)
        self.exports[owner] = []
        scopes = []
        for command in rocq_commands(path.read_text()):
            values = [token[0] for token in command]
            if not values:
                continue
            imported, exported = command_imports(values)
            if exported:
                self.exports[owner].extend(imported)
            if values[0] == "Module" and len(values) > 1:
                if values[1] != "Type" and ":=" not in values:
                    index = 2 if values[1] in {"Import", "Export"} else 1
                    scopes.append(("Module", values[index]))
                continue
            if values[0] == "Section":
                scopes.append(("Section", values[1]))
                continue
            if values[0] == "End" and scopes and values[1] == scopes[-1][1]:
                scopes.pop()
                continue
            declarations = top_level_positions(
                values, {"Definition", "Fixpoint", "CoFixpoint", "Parameter",
                         "Axiom", "Inductive", "Record", "Class", "Notation"})
            if declarations:
                name = values[declarations[0] + 1]
                if name.startswith('"'):
                    name = name[1:-1].replace('""', '"')
                if not IDENTIFIER.fullmatch(name):
                    continue
                modules = [name for kind, name in scopes if kind == "Module"]
                qualified = ".".join([owner, *modules, name])
                self.symbols.add(qualified)
                if values[declarations[0]] in {"Definition", "Notation"}:
                    self.alias_symbols.add(qualified)

    def visible_modules(self, imports: list[str]) -> list[str]:
        modules, pending = [], list(imports)
        while pending:
            module = pending.pop(0)
            if module in modules:
                continue
            modules.append(module)
            self.load(module)
            pending.extend(self.exports.get(module, []))
        return modules

    def resolve(self, predicate: str, namespace: str, imports: list[str]) -> str:
        self.load(namespace)
        self.load(predicate)
        visible = self.visible_modules(imports)
        if predicate in self.symbols:
            return self.canonical(predicate)
        parts = namespace.split(".")
        for length in range(len(parts), 0, -1):
            candidate = ".".join([*parts[:length], predicate])
            if candidate in self.symbols:
                return self.canonical(candidate)
        candidates = set()
        for module in visible:
            for prefix in (module, module.rsplit(".", 1)[0] if "." in module else ""):
                candidate = ".".join(filter(None, [prefix, predicate]))
                if candidate in self.symbols:
                    candidates.add(candidate)
        if len(candidates) == 1:
            return self.canonical(candidates.pop())
        if candidates:
            raise ValueError("unresolved registration key: " + predicate +
                             " (ambiguous: " + ", ".join(sorted(candidates)) + ")")
        raise ValueError("unresolved registration key: " + predicate)

    def validate_aliases(self) -> None:
        if not self.aliases:
            return
        for path in sorted(self.modules):
            self.load(".".join(path.relative_to(self.root).with_suffix("").parts))
        for source, target in self.aliases.items():
            candidates = ({source} if source in self.alias_symbols else
                          {name for name in self.alias_symbols if name.endswith("." + source)})
            if len(candidates) != 1:
                raise ValueError("unresolved registration key: " + source)
            canonical_source = candidates.pop()
            if target not in self.symbols:
                raise ValueError("unresolved registration key: " + target)
            if (canonical_source in self.canonical_aliases and
                    self.canonical_aliases[canonical_source] != target):
                raise ValueError("The aliases disagree on registration key: " + canonical_source)
            self.canonical_aliases[canonical_source] = target
        for source in self.canonical_aliases:
            self.canonical(source)

    def canonical(self, predicate: str) -> str:
        """Apply only aliases that the manifests explicitly declare."""
        seen = set()
        while True:
            if predicate in seen:
                raise ValueError("The registration aliases contain a cycle: " + predicate)
            seen.add(predicate)
            target = self.canonical_aliases.get(predicate)
            if target is None:
                return predicate
            self.load(target)
            if target not in self.symbols:
                raise ValueError("unresolved registration key: " + target)
            predicate = target


def registrations(text: str, module: str = "",
                  resolver: PredicateResolver | None = None) -> list[Registration]:
    """Read instance conclusions; parameter values do not distinguish keys."""
    result, scopes, definitions, imports = [], [], {}, []
    for command in rocq_commands(text):
        values = [token[0] for token in command]
        if not values:
            continue
        imported, _ = command_imports(values)
        imports.extend(imported)
        if values[0] == "Module" and len(values) > 1 and values[1] != "Type":
            if ":=" not in values:
                index = 2 if values[1] in {"Import", "Export"} else 1
                scopes.append(("Module", values[index]))
            continue
        if values[0] == "Section":
            scopes.append(("Section", values[1]))
            continue
        if values[0] == "End" and scopes and values[1] == scopes[-1][1]:
            scopes.pop()
            continue
        modules = [name for kind, name in scopes if kind == "Module"]
        namespace = ".".join([part for part in [module, *modules] if part])
        declaration = next((index for index in top_level_positions(
            values, {"Definition", "Fixpoint", "CoFixpoint", "Parameter"})), None)
        if declaration is not None:
            name = values[declaration + 1]
            definitions[(*modules, name)] = ".".join(filter(None, [namespace, name]))
        if "Instance" not in values:
            continue
        start = values.index("Instance") + 1
        colons = top_level_positions(values[start:], {":"})
        if not colons:
            continue
        colon = start + colons[0]
        conclusion = values[colon + 1:]
        endings = top_level_positions(conclusion, {":=", "|"})
        if endings:
            conclusion = conclusion[:endings[0]]
        conclusion = instance_conclusion(conclusion)
        explicit = bool(conclusion and conclusion[0] == "@")
        index = 1 if explicit else 0
        if index >= len(conclusion):
            continue
        class_name = conclusion[index].rsplit(".", 1)[-1]
        if class_name not in REGISTRATION_CLASSES:
            continue
        line = text.count("\n", 0, command[start - 1][1]) + 1
        name = values[start] if start < colon else ""
        if not IDENTIFIER.fullmatch(name):
            raise ValueError(f"Line {line}: {class_name} needs an explicit instance name.")
        argument = index + 1
        if explicit:
            _, argument = atom(conclusion, argument)
        source, argument = atom(conclusion, argument)
        while top_level_positions(source, {":="}):
            source, argument = atom(conclusion, argument)
        predicate = predicate_head(source)
        parts = tuple(predicate.split("."))
        for depth in range(len(modules), -1, -1):
            local = definitions.get((*modules[:depth], *parts))
            if local:
                predicate = local
                break
        if resolver is not None:
            predicate = resolver.resolve(predicate, namespace, imports)
        result.append(Registration(".".join(filter(None, [namespace, name])),
                                   class_name, predicate, line))
    return result


def registration_violations(paths: set[Path], root: Path, modules: set[Path],
                            aliases: dict[str, str]) -> list[str]:
    errors, seen = [], {}
    resolver = PredicateResolver(root, modules, aliases)
    try:
        resolver.validate_aliases()
    except ValueError as error:
        return [f"Registration aliases: {error}"]
    for path in sorted(paths):
        label = path.relative_to(root)
        try:
            records = registrations(path.read_text(), ".".join(label.with_suffix("").parts), resolver)
        except ValueError as error:
            errors.append(f"{label}: {error}")
            continue
        for record in records:
            key = (record.class_name, record.predicate)
            if key in seen:
                earlier, earlier_path = seen[key]
                errors.append(f"Duplicate {record.class_name} registration for {record.predicate}: "
                              f"{earlier.name} ({earlier_path}:{earlier.line}) and "
                              f"{record.name} ({label}:{record.line}).")
            else:
                seen[key] = (record, label)
    return errors


def manifest_files(manifest: dict, root: Path) -> dict[str, list[Path]]:
    """Require file lists that stay inside the repository."""
    if not isinstance(manifest, dict) or not isinstance(manifest.get("function"), str) \
            or not manifest["function"].strip():
        raise ValueError("The manifest requires a nonempty function name.")
    files = {}
    for category in CATEGORIES:
        values = manifest.get(category)
        if not isinstance(values, list) or any(not isinstance(value, str) or not value
                                               for value in values):
            raise ValueError(f"The manifest requires a file list for {category}.")
        files[category] = []
        for value in values:
            relative = Path(value)
            path = root / relative
            if relative.is_absolute() or not path.resolve().is_relative_to(root.resolve()):
                raise ValueError(f"The listed file leaves the repository: {value}")
            if not path.is_file():
                raise ValueError(f"The listed file is missing: {value}")
            files[category].append(path)
    return files


def manifest_aliases(manifest: dict) -> dict[str, str]:
    aliases = manifest.get("aliases", {})
    if not isinstance(aliases, dict):
        raise ValueError("The manifest aliases must be an object.")
    for source, target in aliases.items():
        if not isinstance(source, str) or not IDENTIFIER.fullmatch(source):
            raise ValueError("The manifest alias needs a Definition or Notation name.")
        if (not isinstance(target, str) or "." not in target or
                not IDENTIFIER.fullmatch(target)):
            raise ValueError("The manifest alias target needs a qualified predicate name.")
    return aliases


def violations(root: Path) -> list[str]:
    errors, registration_paths, modules, aliases = [], set(), set(), {}
    for manifest in sorted((root / "ZesuSsz/Evidence").glob("*_function_text.json")):
        label = manifest.relative_to(root)
        try:
            contents = json.loads(manifest.read_text())
            files = manifest_files(contents, root)
            named_aliases = manifest_aliases(contents)
            for source, target in named_aliases.items():
                if source in aliases and aliases[source] != target:
                    raise ValueError("The manifests disagree on registration alias: " + source)
        except (ValueError, OSError) as error:
            errors.append(f"{label}: {error}")
            continue
        registration_paths.update(files["registrations"])
        modules.update(path for paths in files.values() for path in paths if path.suffix == ".v")
        aliases.update(named_aliases)
        for category in DATA_CATEGORIES:
            for path in files[category]:
                for line, text in enumerate(path.read_text().splitlines(), 1):
                    for match in FORBIDDEN.finditer(text):
                        errors.append(f"{label}: {path.relative_to(root)}:{line}: "
                                      f"Forbidden data-lemma reference: {match.group()}")
    errors.extend(registration_violations(registration_paths, root, modules, aliases))
    return errors


def main() -> int:
    errors = violations(ROOT)
    for error in errors:
        print(error)
    if errors:
        return 1
    count = len(list((ROOT / "ZesuSsz/Evidence").glob("*_function_text.json")))
    print(f"Data-only lemma checks passed for {count} function manifests.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
