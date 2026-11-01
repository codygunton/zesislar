#!/usr/bin/env python3
"""Ratchet the resource shape of handwritten Islaris helper specifications."""

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BASELINE = Path(__file__).with_name("spec_shape_baseline.json")
INVENTORY = Path(__file__).with_name("spec_shape_inventory.json")
METRICS = (
    "uninferable_existentials",
    "predicates_without_unfold",
    "disjunctive_specs",
    "frame_parameters_in_closed_specs",
    "unfold_without_typeclasses_opaque",
)
DEFINITION = re.compile(
    r"\bDefinition\s+(\w+)\b"
    r"(?P<signature>(?:(?!\b(?:Definition|Lemma|Theorem|Fixpoint)\b).)*?)"
    r":\s*iProp\s+Sigma\s*:=", re.S
)
BINDER_GROUP = re.compile(r"\((\w+(?:\s+\w+)*)\s*:\s*[^)]+\)")
CONSTANT = r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*"
UNFOLD_INSTANCE = re.compile(
    r"\bInstance\b(?:(?!\.(?=\s|$)).)*?\bLithiumUnfold\s+"
    r"(?P<target>(?:(?!\.(?=\s|$)).)*?)\s*(?:\|\s*\d+\s*)?"
    r"(?::=|\.(?=\s|$))", re.S
)
TYPECLASSES_OPAQUE = re.compile(
    r"(?P<scope>Global\s+|Local\s+|#\[\s*(?:global|local|export)\s*\]\s*)?"
    r"\bTypeclasses\s+Opaque\s+(?P<names>"
    + CONSTANT + r"(?:\s+" + CONSTANT + r")*)\s*\.", re.S
)


def remove_comments(source: str) -> str:
    """Remove nested Rocq comments and retain offsets for definition spans."""
    result = list(source)
    depth = 0
    offset = 0
    while offset < len(source):
        pair = source[offset:offset + 2]
        if pair == "(*":
            depth += 1
            result[offset:offset + 2] = "  "
            offset += 2
            continue
        if pair == "*)" and depth:
            depth -= 1
            result[offset:offset + 2] = "  "
            offset += 2
            continue
        if depth:
            result[offset] = " " if source[offset] != "\n" else "\n"
        offset += 1
    return "".join(result)


def definitions(source: str) -> list[tuple[str, str, str]]:
    clean = remove_comments(source)
    result = []
    for match in DEFINITION.finditer(clean):
        end = re.search(r"\.(?=\s*(?:\n|$))", clean[match.end():])
        if end is None:
            continue
        body = clean[match.end():match.end() + end.start()]
        result.append((match.group(1), match.group("signature"), body))
    return result


def unfold_targets(source: str) -> list[str | None]:
    """Find instance constants. Count other targets as violations."""
    targets = []
    for match in UNFOLD_INSTANCE.finditer(remove_comments(source)):
        target = re.fullmatch(
            r"\(?\s*@?(" + CONSTANT + r")\s*\)?", match.group("target")
        )
        targets.append(target.group(1) if target else None)
    return targets


def typeclasses_opaque(source: str, global_only: bool = False) -> set[str]:
    """Find explicit typeclass opacity declarations, including constant lists."""
    return {name
            for match in TYPECLASSES_OPAQUE.finditer(remove_comments(source))
            if not global_only or re.match(
                r"(?:Global\b|#\[\s*(?:global|export)\b)", match.group("scope") or ""
            )
            for name in match.group("names").split()}


def unfold_opacity_count(source: str, opaque: set[str]) -> int:
    return sum(target not in opaque for target in unfold_targets(source))


def sealed_predicates(source: str) -> set[str]:
    """Find predicates with an explicit opaque boundary and unfold lemma."""
    clean = remove_comments(source)
    opaque = set(re.findall(r"\bGlobal\s+Opaque\s+(\w+)\s*\.", clean))
    unfold_lemmas = set(re.findall(r"\bLemma\s+(\w+)_unfold\b", clean))
    return opaque & unfold_lemmas


def resource_parts(body: str) -> list[str]:
    """Split the outer separating chain without splitting predicate arguments."""
    existence = body.find("∃")
    if existence >= 0:
        comma = body.find(",", existence)
        if comma >= 0:
            body = body[comma + 1:]
            # Stop at the existential's enclosing argument, not a later chain.
            depth = 0
            for offset, char in enumerate(body):
                if char == "(":
                    depth += 1
                elif char == ")":
                    if depth == 0:
                        body = body[:offset]
                        break
                    depth -= 1
    return resource_chain(body)


def existential_binders(body: str) -> list[str]:
    existence = body.find("∃")
    if existence < 0:
        return []
    comma = body.find(",", existence)
    if comma < 0:
        return []
    declaration = body[existence + 1:comma]
    def bare_binders(segment: str) -> list[str]:
        return re.findall(r"\b[A-Za-z_]\w*\b", segment.split(":", 1)[0])

    binders = []
    offset = 0
    for group in BINDER_GROUP.finditer(declaration):
        binders.extend(bare_binders(declaration[offset:group.start()]))
        binders.extend(group.group(1).split())
        offset = group.end()
    binders.extend(bare_binders(declaration[offset:]))
    return binders


def resource_atom(part: str) -> str:
    """Remove parentheses around a complete spatial or pure atom."""
    part = re.sub(r"%I\s*$", "", part.strip()).strip()
    while part.startswith("(") and part.endswith(")"):
        depth = 0
        for offset, char in enumerate(part):
            depth += (char == "(") - (char == ")")
            if depth == 0:
                break
        if offset != len(part) - 1:
            break
        part = part[1:-1].strip()
    return part


def resource_chain(body: str) -> list[str]:
    """Flatten only separating conjunctions and their grouping parentheses."""
    body = resource_atom(body)
    cuts = []
    depth = pure_depth = 0
    for offset, char in enumerate(body):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "⌜":
            pure_depth += 1
        elif char == "⌝":
            pure_depth -= 1
        elif (char == "∗" and depth == pure_depth == 0
              and (offset == 0 or body[offset - 1] not in "ₘ-")):
            cuts.append(offset)
    if not cuts:
        return [body]
    return [atom for start, end in zip([0] + [cut + 1 for cut in cuts],
                                      cuts + [len(body)])
            for atom in resource_chain(body[start:end])]


def resource_before_pure(binder: str, parts: list[str]) -> bool:
    """Recognize a direct resource argument before all pure uses in this chain.

    Require a pure use for this additional idiom. Keep the existing checks for
    resource-only binders, function arguments, and unknown nested expressions.
    """
    token = re.compile(r"(?<![\w.])" + re.escape(binder) + r"(?![\w.])")
    resources, pure = [], []
    for index, part in enumerate(parts):
        part = resource_atom(part)
        part = re.sub(r'"(?:[^"]|"")*"', lambda match: " " * len(match.group()), part)
        # Parentheses around the binder alone do not make a function argument.
        grouped = re.compile(r"\(\s*" + re.escape(binder) + r"\s*\)")
        while grouped.search(part):
            part = grouped.sub(binder, part)
        if not token.search(part):
            continue
        if part.startswith("⌜") and part.endswith("⌝"):
            pure.append(index)
            continue
        if any(char in part for char in "⌜⌝∗∧∨∃∀→"):
            return False
        head = re.match(CONSTANT + r"\b", part)
        if head is None or head.group() == binder:
            return False
        # An occurrence below a function or another predicate cannot infer it.
        direct = False
        for match in token.finditer(part, head.end()):
            prefix = part[head.end():match.start()]
            if prefix.count("(") == prefix.count(")"):
                direct = True
        if not direct:
            return False
        resources.append(index)
    return bool(resources and pure and min(resources) < min(pure))


def binder_shape(binder: str, parts: list[str], unfolded: set[str]) -> str:
    if resource_before_pure(binder, parts):
        return "inferable"
    token = re.compile(r"\b" + re.escape(binder) + r"\b")
    for part in parts:
        if not token.search(part):
            continue
        if "⌜" in part and "⌝" in part:
            return "pure_only"
        if re.search(r"↦ᵣ\s+RVal_Bits\s+" + re.escape(binder) + r"\b", part):
            return "inferable"
        if re.search(r"\b" + re.escape(binder) + r"\s*↦ₘ(?:∗|\?)?", part):
            return "inferable"
        if re.search(r"↦ₘ(?:∗|\?)?\s+" + re.escape(binder) + r"\b", part):
            return "inferable"
        if re.search(r"spec_trace\s+" + re.escape(binder) + r"\b", part):
            return "inferable"
        if "spec_trace" in part and re.search(
            r"(?:writeOutputEvents|writeOutputEventsAny)\b[\s\S]*\b"
            + re.escape(binder) + r"\b\s*\)", part
        ):
            return "inferable"
        names = re.findall(r"\b([A-Za-z]\w*)\b", part[:token.search(part).start()])
        if names and names[-1] not in unfolded and names[-1] not in {
            "RVal_Bits", "Z_to_bv", "bv_unsigned", "Z", "of_nat",
            "spec_trace", "writeOutputEvents", "writeOutputEventsAny"
        }:
            return "opaque_predicate"
        return "under_function"
    return "under_function"


def shape_counts(source: str, unfolded: set[str], *, module: str | None = None) -> dict[str, int]:
    specs = definitions(source)
    sealed = sealed_predicates(source)
    counts = dict.fromkeys(METRICS, 0)
    for name, signature, body in specs:
        counts["predicates_without_unfold"] += (
            name not in unfolded and
            (module is None or module + "." + name not in unfolded) and
            name not in sealed
        )
        counts["disjunctive_specs"] += "∨" in body
        counts["frame_parameters_in_closed_specs"] += bool(
            name.endswith(("CallSpec", "BodySpec")) and
            re.search(r"\(\w+\s*:\s*iProp\s+Sigma\)", signature)
        )
        parts = resource_parts(body)
        counts["uninferable_existentials"] += sum(
            binder_shape(binder, parts, unfolded) != "inferable"
            for binder in existential_binders(body)
        )
    return counts


def failures(name: str, counts: dict[str, int], baseline: dict) -> list[str]:
    allowed = baseline.get(name, {})
    return [f"{name}: {metric}: {count} > {allowed.get(metric, 0)}"
            for metric, count in counts.items() if count > allowed.get(metric, 0)]


def scoped_inventory_errors(inventory: dict, texts: dict[str, str]) -> list[str]:
    added = subprocess.check_output(
        ["git", "diff", "--diff-filter=A", "--name-only", inventory["base_commit"],
         "--", "ZesuSsz/Evidence", "ZesuSsz/Compliance"],
        cwd=ROOT, text=True).splitlines()
    pending = subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard",
         "ZesuSsz/Evidence/*.v", "ZesuSsz/Compliance/*.v"],
        cwd=ROOT, text=True).splitlines()
    required = {name for name in added + pending if name.endswith(".v") and name in texts
                and name.startswith(("ZesuSsz/Evidence/", "ZesuSsz/Compliance/"))}
    recorded = set(inventory["modules"])
    return (["Missing shape inventory: " + name for name in sorted(required - recorded)] +
            ["Stale shape inventory: " + name for name in sorted(recorded - required)])


def main() -> int:
    baseline = json.loads(BASELINE.read_text())
    inventory = json.loads(INVENTORY.read_text())
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard",
         "ZesuSsz/*.v"], cwd=ROOT, text=True
    ).splitlines()
    # Match the reviewable tree, including additions and pending deletions.
    texts = {name: (ROOT / name).read_text() for name in set(paths)
             if (ROOT / name).is_file()}
    unfolded = {target for source in texts.values()
                for target in unfold_targets(source) if target is not None}
    global_opaque = {
        constant if "." in constant else
        ".".join(Path(name).with_suffix("").parts) + "." + constant
        for name, source in texts.items()
        for constant in typeclasses_opaque(source, global_only=True)
    }
    errors = scoped_inventory_errors(inventory, texts)
    for name, source in texts.items():
        counts = (shape_counts(source, unfolded, module=".".join(Path(name).with_suffix("").parts))
                  if name.startswith(("ZesuSsz/Contracts/", "ZesuSsz/Proofs/"))
                  or name in inventory["modules"]
                  else dict.fromkeys(METRICS, 0))
        counts["unfold_without_typeclasses_opaque"] = unfold_opacity_count(
            source, global_opaque | typeclasses_opaque(source)
        )
        allowances = (inventory["modules"] if name in inventory["modules"] else baseline)
        errors.extend(failures(name, counts, allowances))
    for error in errors:
        print(error, file=sys.stderr)
    return int(bool(errors))


if __name__ == "__main__":
    sys.exit(main())
