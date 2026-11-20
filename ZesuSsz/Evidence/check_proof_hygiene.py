#!/usr/bin/env python3
"""Enforce proof hygiene and ratchet away legacy forbidden identifiers."""

import fnmatch
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "residual"))
from modules import PROOF_OPENER, parse_module
from closed_literal_definitions import closed_literal_failures
sys.path.insert(0, str(ROOT / "tools" / "residuals"))
from render_residual_module import (RenderError, SHARED, module_name, parse_module as parse_residual_module,
                                    parse_shared_module)
sys.path.append(str(ROOT / "tools"))
from kill_scan import tree_failures as unsafe_kill_failures
BASELINE_PATH = Path(__file__).with_name("hygiene_baseline.json")
SIZE_BASELINE_PATH = Path(__file__).with_name("proof_size_baseline.json")
CLOSED_LITERAL_EXCEPTIONS_PATH = Path(__file__).with_name("closed_literal_exceptions.json")
TRUSTED_DECLARATIONS_PATH = Path(__file__).with_name("hygiene_trusted_declarations.json")
PROVED_FUNCTIONS_PATH = ROOT / "ZesuSsz/Contracts/proved_functions.json"
INTERFACES_PREFIX = "ZesuSsz/Interfaces/"
AUTOMATION_PREFIX = "ZesuSsz/Automation/"
HOOKS_PATH = "ZesuSsz/Automation/Hooks.v"
LEGACY_PATH = "ZesuSsz/Automation/AllLegacy.v"
LEGACY_HOOKS_PATH = "ZesuSsz/Automation/Legacy/Hooks.v"
PROOFS_PREFIX = "ZesuSsz/Proofs/"
RESIDUALS_PREFIX = "ZesuSsz/Residuals/"
GENERATED_PROOFS_PREFIX = "ZesuSsz/Generated/"
SHELL_ALLOWLIST = {"ZesuSsz/Compliance/Shell.v"}
GENERATED_PREFIX = "generated/"

PLACEHOLDER = re.compile(
    r"^\s*(?:(?:Admitted|admit|Abort)\s*\.|"
    r"(?:Axiom|Parameter|Hypothesis|Variable)\b)"
)
HOOK_REDEFINITION = re.compile(
    r"\b(?:Ltac\s+(?P<name>[\w.']+)\s*::=|(?:liAStep|liAAsm|liStep)\s*::=)"
)
# Project tactics declared with a default (`Ltac X := fail.`) in an early
# Automation2 module and redefined once by the one later module that owns the
# rule (the two-step pattern of `LiaHook.v`). Key: the redefining file; value:
# the unqualified tactic names it may redefine. Lithium and isla hooks are
# never listed here: they belong to `Automation2/Hooks.v`.
PROJECT_HOOK_REDEFINITIONS = {
    "ZesuSsz/Automation2/BlockTail.v": {"zesu_block_tail_one"},
}
# A test may redefine a project tactic for its own file only.
TEST_LOCAL_HOOK = re.compile(r"^\s*#\[\s*local\s*\]\s*Ltac\b")
TESTS_PREFIX = "ZesuSsz/Proofs/Tests/"
FORBIDDEN_EXECUTABLE_FORMS = (
    ("timeout identifier", re.compile(r"(?<![\w'])timeoutf?(?![\w'])")),
    ("Timeout command", re.compile(r"\b(?P<default>Set\s+Default\s+)?Timeout\s+\d+\b")),
    ("default timeout", re.compile(r"\bSet\s+Default\s+Timeout\b")),
    ("disabled checking", re.compile(r"\bUnset\b[^.]*\bChecking\b")),
    ("bypass_check identifier", re.compile(r"(?<![\w'])bypass_check(?![\w'])")),
)
TRUSTED_DECLARATION_FORMS = (
    ("ML declaration", re.compile(r"\bDeclare\s+ML\s+Module\b")),
    ("external declaration", re.compile(r"\bLtac2\s+@\s*external\b")),
)
DECLARATION_TOKEN = re.compile(r'"(?:[^"]|"")*"|[\w\x27]+|:=|->|=>|[^\s]')
LEGACY_HOOK_LINES = {
    "Ltac liAStep ::= zesu_liAStep.",
}
FORBIDDEN_IDENTIFIERS = (
    "IslaInstructionSegment",
    "writeSuccessTraceAssumptions",
    "zesu_ld_byte_array_at_spec",
    "zesu_lbu_byte_array_at_spec",
    "zesu_ld_array_at_spec",
    "solve_zesu_ld_array_at",
    "mem_mapsto_array_recombine_u64_read",
    "Local Remove Hints subsume_instr_pre'_inst",
    "Local Remove Hints subsume_instr_pre_zesu_inst",
)
A1_MODULES = (
    "ZesuSsz.Contracts.InstructionBoundary",
    "ZesuSsz.Contracts.ExecutionCertificate",
    "ZesuSsz.Contracts.ExecutionCertificateExamples",
    "ZesuSsz.Contracts.IslaMemoryOperational",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessOperationalModel",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessOperationalDefinitions",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessSegmentAutomation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCoverageAutomation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessConcreteRepresentation",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessConcreteMachine",
    "ZesuSsz.Proofs.WriteSuccess.WriteSuccessCfgCertificate",
    "ZesuSsz.Generated.WriteSuccessCertificate",
)
A2_PATTERNS = (
    "WriteSuccessSegment*.v",
    "WriteSuccess*Operational*.v",
    "WriteSuccess*Rank*.v",
    "WriteSuccess*Coverage*.v",
    "WriteSuccess*Concrete*.v",
    "WriteSuccess*Counterexample*.v",
    "WriteSuccessTraceAssumptions*.v",
    "WriteSuccess*Position*.v",
    "WriteSuccess*Recorded*.v",
    "WriteSuccess*Blocker*.v",
    "WriteSuccess*Iteration*.v",
    "WriteSuccessCp1Concrete.v",
    "WriteSuccessReviewInterfaces.v",
    "WriteSuccessRepresentedPrefix.v",
    "WriteSuccessOutputOwned.v",
    "WriteSuccessHostObservation.v",
)
A2_EXCEPTIONS = {"WriteSuccessWithdrawalsIterationBody.v"}
CP1_ENFORCED = True
RETIRED_PROOF_MODULES = (
    "ZesuSsz.Proofs.DecodeItem.Join6ae0.From6a38",
    "ZesuSsz.Proofs.DecodeItem.Join6ae0.From6ad8",
)


def executable_text(text: str, *, mask_strings: bool = True) -> str:
    """Mask nested comments and optional strings without changing offsets."""
    result = list(text)
    depth = 0
    quoted = False
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "(*":
                result[index:index + 2] = "  "
                depth += 1
                index += 2
            elif pair == "*)":
                result[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    result[index] = " "
                index += 1
        elif quoted:
            if pair == '""':
                if mask_strings:
                    result[index:index + 2] = "  "
                index += 2
            else:
                if text[index] == '"':
                    quoted = False
                if mask_strings and text[index] != "\n":
                    result[index] = " "
                index += 1
        elif pair == "(*":
            result[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text[index] == '"':
            if mask_strings:
                result[index] = " "
            quoted = True
            index += 1
        else:
            index += 1
    return "".join(result)


def normalized_declaration(text: str) -> str:
    """Preserve string contents and lexical tokens, ignoring comments and spacing."""
    return " ".join(DECLARATION_TOKEN.findall(executable_text(text, mask_strings=False)))


def trusted_declarations() -> set[tuple[str, str]]:
    rows = json.loads(TRUSTED_DECLARATIONS_PATH.read_text())["declarations"]
    result = set()
    for row in rows:
        name, statement = row["path"], row["statement"]
        if statement != normalized_declaration(statement):
            raise ValueError(f"A trusted declaration is not normalized: {name}")
        key = (name, statement)
        if key in result:
            raise ValueError(f"A trusted declaration repeats: {name}")
        result.add(key)
    return result


def trusted_declaration_failures(
    name: str, text: str, trusted: set[tuple[str, str]]
) -> list[str]:
    code = executable_text(text)
    failures = []
    seen = set()
    endings = list(re.finditer(r"\.(?=\s|$)", code))
    for label, pattern in TRUSTED_DECLARATION_FORMS:
        for match in pattern.finditer(code):
            start = max((ending.end() for ending in endings
                         if ending.end() <= match.start()), default=0)
            end = next((ending.end() for ending in endings
                        if ending.start() >= match.end()), len(text))
            statement = normalized_declaration(text[start:end])
            key = (name, statement)
            if key not in trusted or key in seen:
                number = code.count("\n", 0, match.start()) + 1
                failures.append(f"unapproved {label}: {name}:{number}")
            seen.add(key)
    return failures


def executable_form_failures(name: str, text: str) -> list[str]:
    code = executable_text(text)
    failures = []
    for label, pattern in FORBIDDEN_EXECUTABLE_FORMS:
        for match in pattern.finditer(code):
            if match.groupdict().get("default"):
                # Set Default Timeout has its own diagnostic.
                continue
            number = code.count("\n", 0, match.start()) + 1
            failures.append(f"forbidden {label}: {name}:{number}")
    return failures


# The project's `assert_fails` takes a tactic value. A bare `match` argument
# is evaluated when the argument is built, before `assert_fails` runs, so its
# failure escapes the guard (LESSONS 2026-11-10; f59fb0c55). The safe form
# delays it: `assert_fails (idtac; match ...)`.
ASSERT_FAILS_MATCH = re.compile(r"\bassert_fails\s*(?:ltac:)?\(\s*(?:lazy|multi)?match\b")
ASSERT_FAILS_MATCH_PREFIXES = ("ZesuSsz/Automation2/", PROOFS_PREFIX)


def assert_fails_match_failures(name: str, text: str) -> list[str]:
    if not name.startswith(ASSERT_FAILS_MATCH_PREFIXES):
        return []
    code = executable_text(text)
    return [f"assert_fails with an undelayed match (use `idtac; match`): {name}:"
            f"{code.count(chr(10), 0, match.start()) + 1}"
            for match in ASSERT_FAILS_MATCH.finditer(code)]


# Importing a module re-adds the original body of each tactic it defines, so a
# caller that imports Coq's Lia (directly, or through stdpp or iris) after the
# umbrella gets the library `Lia.lia` back: a project tactic that calls `lia`
# then runs another proof than in a caller without that import. Automation2
# calls `zesu_lia` (LiaHook), which no library import restores.
TACTIC_SENTENCE = re.compile(
    r"(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Export)\s+)?(?:Ltac2?|Hint|Tactic\s+Notation)\b")
LIA_CALL = re.compile(r"(?<![\w.'])(?:Coq\.micromega\.)?(?:Lia\.)?lia(?![\w'])")
LIA_HOOK_SENTENCES = ("Ltac zesu_lia := lia.", "Ltac Lia.lia ::= zesu_lia.")


def automation_lia_call_failures(name: str, text: str) -> list[str]:
    if not name.startswith("ZesuSsz/Automation2/"):
        return []
    code = executable_text(text)
    failures, start = [], 0
    for end in re.finditer(r"\.(?=\s|$)", code):
        sentence = code[start:end.end()]
        offset, start = start + len(sentence) - len(sentence.lstrip()), end.end()
        if (not TACTIC_SENTENCE.match(sentence.lstrip())
                or " ".join(sentence.split()) in LIA_HOOK_SENTENCES):
            continue
        failures.extend(f"Automation2 tactic calls lia (call zesu_lia): {name}:"
                        f"{code.count(chr(10), 0, offset + match.start()) + 1}"
                        for match in LIA_CALL.finditer(sentence.lstrip()))
    return failures


def retired_module_failures(name: str, text: str) -> list[str]:
    """Prevent superseded hand modules and their imports from returning."""
    failures = []
    code = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    for module in RETIRED_PROOF_MODULES:
        if name == module.replace(".", "/") + ".v":
            failures.append(f"retired proof module remains: {name}")
        prefix, short = module.rsplit(".", 1)
        relative = (rf"\bFrom\s+{re.escape(prefix)}\s+Require\s+"
                    rf"(?:Import|Export)\s+[^.]*\b{short}\b")
        if module in code or re.search(relative, code):
            failures.append(f"imports retired proof module: {name}: {module}")
    return failures


def interface_paths(entry: dict) -> list[str]:
    """The generated interface modules of a registry entry."""
    interface = entry["interface"]
    return ["ZesuSsz/" + module[len("ZesuSsz."):].replace(".", "/") + ".v"
            for module in (interface["module"], interface["correct"]["module"])]


def sealed_callees(path=PROVED_FUNCTIONS_PATH) -> list[dict]:
    """The black-box rules of every registered function that has an interface."""
    callees = []
    for entry in json.loads(Path(path).read_text())["functions"]:
        if not entry.get("interface"):
            continue
        paths = interface_paths(entry)
        callees.append({
            "interfaces": paths,
            "sealed": [row["name"] for row in entry["sealed"]],
            # The template bridge and the meaning links reveal the sealed definitions:
            # only the interface modules use them.
            "restricted": [entry["call_spec"]["name"] + "CorrectFrom"] +
                          [lemma["name"] for lemma in entry["interface_lemmas"]
                           if lemma.get("exit_composition_only")],
            "unsealed": [row["definition"] for row in entry["sealed"]],
            "owned_prefixes": entry["owned_prefixes"],
        })
    return callees


def sealed_callee_failures(name: str, text: str, callees: list[dict]) -> list[str]:
    """A caller treats a proved callee as a black box.

    The template bridge and meaning links of a sealed callee occur only in its
    interface modules; no file but the interface unfolds a sealed name; and no
    other function's generated module states an unsealed callee predicate.
    """
    code = executable_text(text)
    failures = []

    def line(match):
        return code.count("\n", 0, match.start()) + 1

    for callee in callees:
        if name in callee["interfaces"]:
            continue
        for word in callee["restricted"]:
            for match in re.finditer(rf"(?<![\w.']){re.escape(word)}(?![\w'])", code):
                failures.append(f"sealed callee interface used outside it: {name}:{line(match)}: {word}")
        for word in callee["sealed"]:
            pattern = rf"\b(?:unfold|Transparent|Strategy)\b[^.;]*?(?<![\w.']){re.escape(word)}(?![\w'])"
            for match in re.finditer(pattern, code):
                failures.append(f"sealed callee predicate unfolded: {name}:{line(match)}: {word}")
        if name.startswith(GENERATED_PROOFS_PREFIX) and not name.startswith(tuple(callee["owned_prefixes"])):
            for word in callee["unsealed"]:
                for match in re.finditer(rf"(?<![\w.']){re.escape(word)}(?![\w'])", code):
                    failures.append(f"unsealed callee predicate in a caller entry: {name}:{line(match)}: {word}")
    return failures


def interface_signature_lines(text: str) -> set[int]:
    """Line numbers inside a `Module Type ... End` block of a generated interface."""
    inside, lines = False, set()
    for number, line in enumerate(text.splitlines(), 1):
        if re.match(r"\s*Module\s+Type\s+(\w+)", line):
            inside = True
        elif inside and re.match(r"\s*End\s+\w+\s*\.", line):
            inside = False
        elif inside:
            lines.add(number)
    return lines


def fresh_interface_modules() -> set[str]:
    """Generated interface modules that equal a fresh render of the registry."""
    sys.path.insert(0, str(ROOT / "tools" / "block"))
    from render_interfaces import rendered
    return {path for path, text in rendered().items()
            if path.startswith(INTERFACES_PREFIX) and (ROOT / path).exists() and (ROOT / path).read_text() == text}


def tracked_files() -> list[str]:
    """Every file the repository would carry, tracked or not yet added.

    `git ls-files` alone lists only tracked files, so a new module escapes
    every rule here until it is committed. A `Ltac … ::=` outside
    `Hooks.v` survived two commits that way. `--others
    --exclude-standard` adds the files that are new but not ignored, which
    is what a reviewer would see.
    """
    output = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        cwd=ROOT, text=True
    )
    return sorted(set(output.splitlines()))


def generated_hand_line_failures(name: str, text: str) -> list[str]:
    """Generated instruction-body proofs must use only block automation."""
    if not name.startswith(GENERATED_PROOFS_PREFIX):
        return []
    path = ROOT / name
    proofs = parse_module(path)
    lines = text.splitlines()
    failures = []
    for proof in proofs:
        statement = "\n".join(lines[proof.declaration_line:proof.proof_line])
        if "instr_body" in statement and proof.hand_lines:
            failures.append(
                f"generated instr_body proof has hand lines: {name}: "
                f"{proof.name}: {len(proof.hand_lines)} lines"
            )
    return failures


def shared_core_modules(root=ROOT) -> set[str]:
    """Module names that exist in both the frozen core and Automation2."""
    frozen = {path.stem for path in (Path(root) / AUTOMATION_PREFIX).rglob("*.v")}
    current = {path.stem for path in (Path(root) / "ZesuSsz/Automation2").rglob("*.v")}
    return frozen & current


def short_core_name_failures(name: str, text: str, shared: set[str]) -> list[str]:
    """A proof file on the Automation2 core names shared core modules in full.

    A short name such as `ContextCollection.zesu_context_prune_goal` can
    resolve to the frozen core when that module is also in scope, so the file
    silently calls the frozen tactic.
    """
    if not name.startswith(PROOFS_PREFIX) or not shared:
        return []
    code = executable_text(text)
    if "Require Import ZesuSsz.Automation2.All." not in code:
        return []
    pattern = re.compile(r"(?<![\w.'])(" + "|".join(sorted(map(re.escape, shared))) + r")\.[A-Za-z_]")
    failures = []
    for match in pattern.finditer(code):
        number = code.count("\n", 0, match.start()) + 1
        failures.append(
            f"short core module name: {name}:{number}: {match.group(1)}.; "
            f"write ZesuSsz.Automation2.{match.group(1)}.")
    return failures


REWRITE_HINT = re.compile(
    r"(?:#\[\s*(?P<attribute>\w+)\s*\]\s*|\b(?P<locality>Local|Global|Export)\s+)?"
    r"\bHint\s+Rewrite\b(?P<body>.*?)\.(?=\s)", re.S)


def rewrite_hint_terms(head: str) -> list[str]:
    """Split the lemma list of a `Hint Rewrite` at top-level spaces."""
    terms, depth, current = [], 0, ""
    for char in head:
        depth += {"(": 1, ")": -1}.get(char, 0)
        if char.isspace() and depth == 0:
            if current:
                terms.append(current)
            current = ""
        else:
            current += char
    if current:
        terms.append(current)
    return terms


def duplicate_rewrite_failures(sources: dict[str, str]) -> list[str]:
    """One lemma, in one direction, is registered once in one rewrite database.

    `autorewrite` tries every registration, with its side-condition solver,
    so a second registration doubles that cost and adds nothing. Local
    registrations are file-scoped and are not compared.
    """
    seen: dict[tuple[str, str, str], list[str]] = {}
    for name, text in sorted(sources.items()):
        code = executable_text(text, mask_strings=False)
        for match in REWRITE_HINT.finditer(code):
            locality = (match.group("attribute") or match.group("locality") or "").lower()
            body = match.group("body")
            if locality == "local" or ":" not in body:
                continue
            head, databases = body.rsplit(":", 1)
            head = re.split(r"\busing\b", head, maxsplit=1)[0].strip()
            direction = "->"
            if head.startswith(("<-", "->")):
                direction, head = head[:2], head[2:]
            line = code.count("\n", 0, match.start()) + 1
            for term in rewrite_hint_terms(head):
                for database in databases.split():
                    key = (database, direction, " ".join(term.split()))
                    seen.setdefault(key, []).append(f"{name}:{line}")
    return [f"rewrite registered twice: {term} ({direction}) in {database}: " + ", ".join(places)
            for (database, direction, term), places in sorted(seen.items()) if len(places) > 1]


# Frozen `Global` instances that may stay active beside the Automation2 core,
# each with its reason. Empty: every reachable one is removed.
FROZEN_GLOBAL_ALLOWLIST: dict[str, str] = {}
REQUIRE_COMMAND = re.compile(
    r"^\s*(?:From\s+(?P<prefix>\S+)\s+)?Require\s+(?:Import\s+|Export\s+)?(?P<modules>[^.]+(?:\.[\w']+)*)\s*\.\s*$",
    re.M)
FROZEN_GLOBAL_INSTANCE = re.compile(r"^\s*Global\s+(?:Existing\s+)?Instance\s+(?P<name>[\w']+)", re.M)
LOCAL_DEFINITION = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Global|Local)\s+)?(?:Program\s+)?"
    r"(?:Definition|Instance|Lemma|Theorem|Fixpoint)\s+(?P<name>[\w']+)", re.M)
GLOBAL_REMOVE_HINTS = re.compile(r"\bGlobal\s+Remove\s+Hints\b(?P<names>[^:]*):\s*typeclass_instances\s*\.")


def module_path(module: str, root=ROOT):
    if not module.startswith("ZesuSsz."):
        return None
    path = Path(root) / (module.replace(".", "/") + ".v")
    return path if path.exists() else None


def required_closure(start: str, root=ROOT) -> set[str]:
    """Every ZesuSsz module that `start` loads, through any Require."""
    seen, stack = set(), [start]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module, root)
        if path is None:
            continue
        code = executable_text(path.read_text())
        for match in REQUIRE_COMMAND.finditer(code):
            prefix = match.group("prefix")
            for name in match.group("modules").split():
                full = f"{prefix}.{name}" if prefix else name
                if full.startswith("ZesuSsz."):
                    stack.append(full)
    return seen


def frozen_global_failures(root=ROOT, umbrella="ZesuSsz.Automation2.All",
                           allowlist=FROZEN_GLOBAL_ALLOWLIST) -> list[str]:
    """A frozen `Global` instance that the Automation2 umbrella loads is removed.

    `Global` instances stay active wherever their module is loaded, even
    without an import, so a frozen copy runs beside its Automation2 copy and
    doubles every failing instance search. A loaded frozen instance needs a
    `Global Remove Hints` with its full name in a non-frozen loaded module, or
    an allowlist entry with a reason.
    """
    closure = required_closure(umbrella, root)
    removed: set[str] = set()
    declared: list[tuple[str, str]] = []
    for module in sorted(closure):
        path = module_path(module, root)
        if path is None:
            continue
        code = executable_text(path.read_text())
        if module.startswith("ZesuSsz.Automation."):
            # A library instance registered again is one hint, shared with
            # the Automation2 registration; only frozen-defined ones count.
            defined = {match.group("name") for match in LOCAL_DEFINITION.finditer(code)}
            for match in FROZEN_GLOBAL_INSTANCE.finditer(code):
                if match.group("name") in defined:
                    declared.append((module, match.group("name")))
        else:
            for match in GLOBAL_REMOVE_HINTS.finditer(code):
                removed.update(match.group("names").split())
    return [f"frozen Global instance active beside Automation2: {module}.{name}"
            for module, name in declared
            if f"{module}.{name}" not in removed and f"{module}.{name}" not in allowlist]


def residual_module_failures(name: str, text: str) -> list[str]:
    """Residual modules hold only rendered declarations around copied proofs."""
    if not name.startswith(RESIDUALS_PREFIX):
        return []
    if name[len(RESIDUALS_PREFIX):-len(".v")] in SHARED:
        try:
            parse_shared_module(text)
        except RenderError as error:
            return [f"residual module is not renderer output: {name}: {error}"]
        return []
    try:
        block, _, _ = parse_residual_module(text)
    except RenderError as error:
        return [f"residual module is not renderer output: {name}: {error}"]
    if name != RESIDUALS_PREFIX + module_name(block) + ".v":
        return [f"residual module name does not match its block: {name}"]
    return []


def forbidden_counts(text: str) -> dict[str, int]:
    return {
        identifier: text.count(identifier)
        for identifier in FORBIDDEN_IDENTIFIERS
        if text.count(identifier)
    }


def ratchet_failures(
    name: str, counts: dict[str, int], baseline: dict[str, dict[str, int]]
) -> list[str]:
    failures = []
    allowed = baseline.get(name, {})
    for identifier, count in counts.items():
        limit = allowed.get(identifier, 0)
        if count > limit:
            failures.append(
                f"forbidden-name increase: {name}: {identifier}: {count} > {limit}"
            )
    return failures


def proof_size_warnings(name: str, lines: list[str]) -> list[str]:
    warnings = []
    proof_start = None
    statement_has_instr_body = False
    rename_count = 0
    for number, line in enumerate(lines, 1):
        if proof_start is None:
            statement_has_instr_body = statement_has_instr_body or "instr_body" in line
            if PROOF_OPENER.match(line):
                if re.search(r"\bQed\.", line):
                    statement_has_instr_body = False
                else:
                    proof_start = number
                    rename_count = 0
            elif re.match(r"^\s*(?:Definition|Lemma|Theorem|Corollary)\b", line):
                statement_has_instr_body = "instr_body" in line
            continue
        rename_count += line.count("iRename select")
        if re.match(r"^\s*Qed\.", line):
            if rename_count > 5:
                warnings.append(
                    f"proof has {rename_count} iRename select calls: {name}:{proof_start}"
                )
            proof_lines = number - proof_start - 1
            if statement_has_instr_body and proof_lines > 40:
                warnings.append(
                    f"instr_body proof has {proof_lines} lines: {name}:{proof_start}"
                )
            proof_start = None
            statement_has_instr_body = False
    return warnings


def proof_size_metrics(messages: list[str]) -> dict[str, int]:
    line_counts = [
        int(match.group(1))
        for message in messages
        if (match := re.search(r"instr_body proof has (\d+) lines", message))
    ]
    rename_counts = [
        int(match.group(1))
        for message in messages
        if (match := re.search(r"proof has (\d+) iRename", message))
    ]
    return {
        "long_proofs": len(line_counts),
        "max_proof_lines": max(line_counts, default=0),
        "rename_proofs": len(rename_counts),
        "max_renames": max(rename_counts, default=0),
    }


def proof_size_ratchet_failures(
    name: str, messages: list[str], baseline: dict[str, dict[str, int]]
) -> list[str]:
    current = proof_size_metrics(messages)
    allowed = baseline.get(name, {})
    failures = []
    for metric, count in current.items():
        limit = allowed.get(metric, 0)
        if count > limit:
            failures.append(
                f"proof-size increase: {name}: {metric}: {count} > {limit}"
            )
    return failures



FROZEN_AUTOMATION_TREE = "e962d3a7974b662a75e955d8315bed9f0fa66fd1"


def frozen_automation_failures(root=ROOT, tree=FROZEN_AUTOMATION_TREE):
    """Compare working source bytes with a pinned tree, independent of ancestry."""
    records = subprocess.check_output([
        "git", "-C", str(root), "ls-tree", "-r", "-z", tree]).decode().split("\0")
    expected = {}
    for record in filter(None, records):
        metadata, name = record.split("\t", 1)
        mode, kind, digest = metadata.split()
        expected[AUTOMATION_PREFIX + name] = (mode, digest)
    names = subprocess.check_output([
        "git", "-C", str(root), "ls-files", "--cached", "--others", "--exclude-standard",
        "-z", "--", AUTOMATION_PREFIX], text=True).split("\0")
    actual = {}
    for name in set(filter(None, names)):
        path = Path(root)/name
        if not path.exists() or path.is_symlink():
            continue
        raw = path.read_bytes()
        digest = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        actual[name] = ("100755" if path.stat().st_mode & 0o111 else "100644", digest)
    changed = sorted(name for name in expected.keys() | actual.keys()
                     if expected.get(name) != actual.get(name))
    if not changed:
        return []
    reason = os.environ.get("ZESU_AUTOMATION_EMERGENCY_OVERRIDE", "").strip()
    if reason:
        print("emergency Automation override: " + reason, file=sys.stderr)
        return []
    return ["frozen Automation changed: " + name for name in changed]



def automation_entry_failures(name, text, legacy_entries):
    """Require one core umbrella while preserving the approved legacy ratchet."""
    code = executable_text(text)
    entries = (
        "Require Import ZesuSsz.Automation.All." in code,
        "Require Import ZesuSsz.Automation2.All." in code,
        "Require Import ZesuSsz.Automation.AllLegacy." in code,
    )
    normal, automation2, legacy = entries
    failures = []
    if not (normal or automation2) and not (name in legacy_entries and legacy):
        failures.append(f"missing Automation umbrella import: {name}")
    if legacy and name not in legacy_entries:
        failures.append(f"unapproved Automation.AllLegacy import: {name}")
    if sum(entries) > 1:
        failures.append(f"mixed Automation umbrellas imported: {name}")
    return failures


def main() -> None:
    baseline_data = json.loads(BASELINE_PATH.read_text())
    baseline = baseline_data["files"]
    legacy_entries = set(baseline_data["legacy_entry_files"])
    size_baseline_data = json.loads(SIZE_BASELINE_PATH.read_text())
    size_baseline = size_baseline_data["files"]
    trusted = trusted_declarations()
    callees = sealed_callees()
    fresh_interfaces = fresh_interface_modules()
    literal_exceptions = {(row["file"], row["name"]): row for row in
                          json.loads(CLOSED_LITERAL_EXCEPTIONS_PATH.read_text())["exceptions"]}
    failures: list[str] = list(frozen_automation_failures(ROOT))
    shared = shared_core_modules(ROOT)
    warnings: list[str] = []
    remaining = 0
    core_sources: dict[str, str] = {}
    names = tracked_files()
    # A kill by name or by parent PID in a committed tool reaches other agents'
    # jobs (2026-11-15); `run_registry.py launch` refuses such a script too.
    failures.extend(unsafe_kill_failures(ROOT, names))
    for name in names:
        if name.startswith("generated/isla-traces/"):
            failures.append(f"tracked generated Isla trace: {name}")
        if not name.endswith(".v"):
            continue
        path = ROOT / name
        if not path.exists():
            # `git ls-files --cached` still lists a file that has been
            # deleted in the working tree. A reviewer sees the deletion,
            # so the checker does too.
            continue
        text = path.read_text()
        lines = text.splitlines()
        if name.startswith("ZesuSsz/Automation2/"):
            core_sources[name] = text
        failures.extend(executable_form_failures(name, text))
        failures.extend(assert_fails_match_failures(name, text))
        failures.extend(automation_lia_call_failures(name, text))
        failures.extend(closed_literal_failures(name, text, literal_exceptions))
        failures.extend(trusted_declaration_failures(name, text, trusted))
        failures.extend(generated_hand_line_failures(name, text))
        failures.extend(retired_module_failures(name, text))
        failures.extend(residual_module_failures(name, text))
        failures.extend(short_core_name_failures(name, text, shared))
        failures.extend(sealed_callee_failures(name, text, callees))

        # Generated Sail interfaces contain upstream Axiom declarations.
        # A fresh generated black-box interface declares its sealed predicates
        # and lemmas as Parameter/Axiom inside its Module Type only; the opaque
        # module ascribed to that signature realizes each of them.
        # Reviewed proof files remain subject to the complete placeholder check.
        signature = interface_signature_lines(text) if name in fresh_interfaces else set()
        if name not in SHELL_ALLOWLIST and not name.startswith(GENERATED_PREFIX):
            for number, line in enumerate(lines, 1):
                if number in signature and re.match(r"\s*(?:Parameter|Axiom)\b", line):
                    continue
                if PLACEHOLDER.search(line):
                    failures.append(
                        f"proof placeholder: {name}:{number}: {line.strip()}"
                    )

        if name not in (HOOKS_PATH, "ZesuSsz/Automation2/Hooks.v"):
            allowed = PROJECT_HOOK_REDEFINITIONS.get(name, set())
            used = set()
            for number, line in enumerate(lines, 1):
                match = HOOK_REDEFINITION.search(line)
                if not match:
                    continue
                if (name in (LEGACY_HOOKS_PATH, "ZesuSsz/Automation2/Legacy/Hooks.v") and
                        line.strip() in LEGACY_HOOK_LINES):
                    continue
                tactic = match.group("name") or ""
                if (name.startswith(TESTS_PREFIX) and tactic.startswith("ZesuSsz.") and
                        TEST_LOCAL_HOOK.match(line)):
                    continue
                short = tactic.rsplit(".", 1)[-1]
                if short in allowed and short not in used:
                    used.add(short)
                    continue
                failures.append(f"Lithium hook redefinition: {name}:{number}")

        if name.startswith(PROOFS_PREFIX):
            failures.extend(automation_entry_failures(name, text, legacy_entries))
            if (path.name not in A2_EXCEPTIONS and
                    any(fnmatch.fnmatch(path.name, pattern) for pattern in A2_PATTERNS)):
                failures.append(f"Appendix A.2 file remains: {name}")
            size_messages = proof_size_warnings(name, lines)
            if CP1_ENFORCED:
                warnings.extend(size_messages)
                failures.extend(
                    proof_size_ratchet_failures(name, size_messages, size_baseline)
                )
            else:
                warnings.extend(size_messages)

        for module in A1_MODULES:
            if module in text:
                failures.append(f"imports Appendix A.1 module: {name}: {module}")

        if not name.startswith((AUTOMATION_PREFIX, "ZesuSsz/Automation2/")):
            counts = forbidden_counts(text)
            remaining += sum(counts.values())
            failures.extend(ratchet_failures(name, counts, baseline))

    failures.extend(duplicate_rewrite_failures(core_sources))
    failures.extend(frozen_global_failures(ROOT))
    if warnings:
        print(f"warning: {len(warnings)} proof-size baseline violations remain", file=sys.stderr)
    if remaining:
        print(
            f"warning: {remaining} baseline forbidden-name occurrences remain",
            file=sys.stderr,
        )
    if failures:
        raise SystemExit("\n".join(failures))


if __name__ == "__main__":
    main()
