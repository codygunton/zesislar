#!/usr/bin/env python3
"""Ratchet the resource shape of handwritten Islaris helper specifications."""

import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BASELINE = Path(__file__).with_name("spec_shape_baseline.json")
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
    r"(?P<scope>Global\s+|Local\s+|#\[\s*(?:global|local)\s*\]\s*)?"
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
                r"(?:Global\b|#\[\s*global\b)", match.group("scope") or ""
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
    depths = []
    depth = 0
    for offset, char in enumerate(body):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "∗" and (offset == 0 or body[offset - 1] != "ₘ"):
            depths.append((offset, depth))
    if not depths:
        return [body]
    outer = min(level for _, level in depths)
    cuts = [offset for offset, level in depths if level == outer]
    return [body[start:end] for start, end in zip([0] + [cut + 1 for cut in cuts], cuts + [len(body)])]


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


def binder_shape(binder: str, parts: list[str], unfolded: set[str]) -> str:
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


def shape_counts(source: str, unfolded: set[str]) -> dict[str, int]:
    specs = definitions(source)
    sealed = sealed_predicates(source)
    counts = dict.fromkeys(METRICS, 0)
    for name, signature, body in specs:
        counts["predicates_without_unfold"] += (
            name not in unfolded and name not in sealed
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


def main() -> int:
    baseline = json.loads(BASELINE.read_text())
    paths = subprocess.check_output(
        ["git", "ls-files", "ZesuSsz/*.v"], cwd=ROOT, text=True
    ).splitlines()
    texts = {name: (ROOT / name).read_text() for name in paths}
    unfolded = {target for source in texts.values()
                for target in unfold_targets(source) if target is not None}
    global_opaque = {
        constant if "." in constant else
        ".".join(Path(name).with_suffix("").parts) + "." + constant
        for name, source in texts.items()
        for constant in typeclasses_opaque(source, global_only=True)
    }
    errors = []
    for name, source in texts.items():
        counts = (shape_counts(source, unfolded)
                  if name.startswith(("ZesuSsz/Contracts/", "ZesuSsz/Proofs/"))
                  else dict.fromkeys(METRICS, 0))
        counts["unfold_without_typeclasses_opaque"] = unfold_opacity_count(
            source, global_opaque | typeclasses_opaque(source)
        )
        errors.extend(failures(name, counts, baseline))
    for error in errors:
        print(error, file=sys.stderr)
    return int(bool(errors))


if __name__ == "__main__":
    sys.exit(main())
